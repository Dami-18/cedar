/*
 * Copyright Cedar Contributors
 *
 * Licensed under the Apache License, Version 2.0 (the "License_");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      https://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

//! This module contains PolTree structure used for policy evaluation. It is a tree structure where each node represents a policy statement or a condition

use crate::ast::*;
use crate::authorizer::{Decision, Diagnostics};
use crate::entities::{Dereference, Entities};
use serde::{Deserialize, Serialize};
use smol_str::{SmolStr, ToSmolStr};
use std::collections::{HashMap, HashSet};
use std::sync::Arc;

const SCOPE_PRINCIPAL_ATTR: &str = "__scope_principal";
const SCOPE_RESOURCE_ATTR: &str = "__scope_resource";
const SCOPE_ACTION_ATTR: &str = "__scope_action";
// Namespace prefix for context attributes, so `context.foo` never collides
// with a principal/resource attribute also named `foo` in the flat attr map.
const CONTEXT_ATTR_PREFIX: &str = "__context_";

fn context_attr_key(attr: &SmolStr) -> SmolStr {
    format!("{CONTEXT_ATTR_PREFIX}{attr}").into()
}

fn is_context_attr(attr: &SmolStr) -> bool {
    attr.as_str().starts_with(CONTEXT_ATTR_PREFIX)
}

/// Look up a literal value for a context attribute directly from the
/// request's `Context` record. Context is per-request, not a property of
/// any entity, so (unlike principal/resource attributes) this never scans
/// the `Entities` store.
fn request_context_literal(request: &Request, attr: &SmolStr) -> Option<Literal> {
    let raw_attr = attr.as_str().strip_prefix(CONTEXT_ATTR_PREFIX)?;
    match request.context()? {
        Context::Value(map) => map.get(raw_attr).and_then(|v| v.try_as_lit().cloned()),
        Context::RestrictedResidual(_) => None,
    }
}

// Non-scope (`when`-clause) constraints are indexed per-attribute-NAME, e.g.
// "clearance". If a policy constrains `principal.clearance` and
// `resource.clearance` separately (a common ABAC pattern -- compare a
// principal's clearance to a resource's clearance), those are two distinct
// facts about two different entities that happen to share an attribute name.
// Indexing them under the same bare "clearance" key would make
// `request_values_for_attr` union both entities' values into one membership
// check, silently turning the policy's AND into an OR. These prefixes keep
// principal-side and resource-side constraints on the same attribute name in
// separate index keys.
const PRINCIPAL_ATTR_PREFIX: &str = "__principal_attr_";
const RESOURCE_ATTR_PREFIX: &str = "__resource_attr_";

/// Build the namespaced index key for a principal-side or resource-side
/// non-scope attribute constraint. See the module comment above.
fn side_scoped_attr(is_principal: bool, attr: &SmolStr) -> SmolStr {
    if is_principal {
        SmolStr::from(format!("{PRINCIPAL_ATTR_PREFIX}{attr}"))
    } else {
        SmolStr::from(format!("{RESOURCE_ATTR_PREFIX}{attr}"))
    }
}

/// Inverse of [`side_scoped_attr`]: given an index key, recover which side it
/// came from (`true` = principal, `false` = resource) and the underlying
/// entity attribute name. Returns `None` for keys that were never produced by
/// `side_scoped_attr` (scope attributes, or raw entity-attribute-name keys
/// that never got a matching policy constraint -- see `build_from_entities`).
fn split_side_scoped_attr(attr: &str) -> Option<(bool, &str)> {
    if let Some(rest) = attr.strip_prefix(PRINCIPAL_ATTR_PREFIX) {
        Some((true, rest))
    } else if let Some(rest) = attr.strip_prefix(RESOURCE_ATTR_PREFIX) {
        Some((false, rest))
    } else {
        None
    }
}

#[derive(Debug, Clone)]
struct Constraint {
    attr: SmolStr,
    values: Vec<Literal>,
    candidates: HashSet<EntityUID>,
}

/// O(1) direct lookup for whether a specific entity UID exists in the store,
/// used for `principal == X` / `resource == X` / `action == Y` scope
/// constraints. `Entities::entity` is backed by a hash map keyed on
/// `EntityUID`, so this never needs to scan the store.
fn entities_with_uid(entities: &Entities, uid: &EntityUID) -> HashSet<EntityUID> {
    match entities.entity(uid) {
        Dereference::Data(_) => HashSet::from([uid.clone()]),
        _ => HashSet::new(),
    }
}

/// Precomputed, one-time-scan indexes over the entity store, built once and
/// reused across every constraint of every policy while building a
/// `PolTreeIndex`. Without this, resolving each policy's attribute-value and
/// `is <Type>` scope constraints would otherwise re-scan the *entire* entity
/// store once per constraint, making total build cost O(constraints *
/// entities) instead of the O(entities * attrs_per_entity) a single pass
/// actually requires -- for a policy set of any real size (many policies,
/// each with several attribute constraints) this dominates build time.
struct EntityScanIndexes {
    attr_values: HashMap<SmolStr, HashSet<Literal>>,
    sv_map: HashMap<(SmolStr, Literal), Vec<EntityUID>>,
    type_index: HashMap<EntityType, HashSet<EntityUID>>,
}

fn scan_entities(entities: &Entities) -> EntityScanIndexes {
    let mut attr_values: HashMap<SmolStr, HashSet<Literal>> = HashMap::new();
    let mut sv_map: HashMap<(SmolStr, Literal), Vec<EntityUID>> = HashMap::new();
    let mut type_index: HashMap<EntityType, HashSet<EntityUID>> = HashMap::new();

    for entity in entities.iter() {
        let uid = entity.uid().clone();
        type_index
            .entry(uid.entity_type().clone())
            .or_default()
            .insert(uid.clone());
        for (attr, pval) in entity.attrs() {
            // Only index scalar (Literal) values; skip sets, records, residuals
            if let PartialValue::Value(v) = pval {
                if let Some(lit) = v.try_as_lit() {
                    let lit = lit.clone();
                    attr_values
                        .entry(attr.clone())
                        .or_default()
                        .insert(lit.clone());
                    sv_map
                        .entry((attr.clone(), lit))
                        .or_default()
                        .push(uid.clone());
                }
            }
        }
    }

    EntityScanIndexes {
        attr_values,
        sv_map,
        type_index,
    }
}

/// O(1) (after `scan_entities` has run once) replacement for scanning the
/// whole entity store to find entities with a given attribute value.
fn candidates_from_sv_map(
    sv_map: &HashMap<(SmolStr, Literal), Vec<EntityUID>>,
    attr: &SmolStr,
    lit: &Literal,
) -> HashSet<EntityUID> {
    sv_map
        .get(&(attr.clone(), lit.clone()))
        .map(|v| v.iter().cloned().collect())
        .unwrap_or_default()
}

/// O(1) (after `scan_entities` has run once) replacement for scanning the
/// whole entity store to find every entity of a given type.
fn candidates_from_type_index(
    type_index: &HashMap<EntityType, HashSet<EntityUID>>,
    entity_type: &EntityType,
) -> HashSet<EntityUID> {
    type_index.get(entity_type).cloned().unwrap_or_default()
}

// Scope attributes (__scope_principal / __scope_resource) are indexed under two
// different literal encodings depending on how the policy constrains them:
// `principal == X` / `resource == X` register the exact EntityUID, while
// `principal is T` / `resource is T` register the type name as a String (see
// `principal_or_resource_scope_constraints`). Return both candidate literals here
// so lookups match whichever encoding a given policy used to register its edge.
fn request_scope_literals(request: &Request, attr: &SmolStr) -> Vec<Literal> {
    match attr.as_str() {
        SCOPE_PRINCIPAL_ATTR => request
            .principal()
            .uid()
            .map(|uid| {
                vec![
                    Literal::EntityUID(Arc::new(uid.clone())),
                    Literal::String(uid.entity_type().to_smolstr()),
                ]
            })
            .unwrap_or_default(),
        SCOPE_RESOURCE_ATTR => request
            .resource()
            .uid()
            .map(|uid| {
                vec![
                    Literal::EntityUID(Arc::new(uid.clone())),
                    Literal::String(uid.entity_type().to_smolstr()),
                ]
            })
            .unwrap_or_default(),
        SCOPE_ACTION_ATTR => request
            .action()
            .uid()
            .map(|uid| vec![Literal::EntityUID(Arc::new(uid.clone()))])
            .unwrap_or_default(),
        _ => vec![],
    }
}

fn request_values_for_attr(request: &Request, entities: &Entities, attr: &SmolStr) -> Vec<Literal> {
    let scope_literals = request_scope_literals(request, attr);
    if !scope_literals.is_empty() {
        return scope_literals;
    }

    if is_context_attr(attr) {
        return request_context_literal(request, attr).into_iter().collect();
    }

    // Every non-scope, non-context constraint this tree can act on was
    // registered under a side-scoped key (see `side_scoped_attr`), so only
    // look up the ONE entity the key actually refers to -- never both. A key
    // that isn't side-scoped never has a matching pv_map entry (see
    // `build_from_entities`) and so is never chosen as a split attribute;
    // this path only exists as a safe default if that invariant is ever
    // violated.
    let Some((is_principal, raw_attr)) = split_side_scoped_attr(attr.as_str()) else {
        return Vec::new();
    };
    let entry = if is_principal {
        request.principal()
    } else {
        request.resource()
    };
    let Some(uid) = entry.uid() else {
        return Vec::new();
    };
    let Dereference::Data(entity) = entities.entity(uid) else {
        return Vec::new();
    };
    match entity.get(raw_attr) {
        Some(PartialValue::Value(v)) => v.try_as_lit().map(|lit| vec![lit.clone()]).unwrap_or_default(),
        _ => Vec::new(),
    }
}

// Each of these three constraint-extraction functions returns, alongside the
// extracted `Constraint`s, a `bool` indicating whether the constraint form was
// FULLY captured. `false` means the policy imposes a real restriction on this
// dimension that we could not represent (e.g. `in` hierarchy membership, a
// template slot, or -- for `collect_attr_constraints` -- anything other than a
// flat `entity.attr == <literal>` equality: cross-attribute comparisons,
// `!=`, `has`, `like`, `or`, `unless`, etc).
//
// This distinction matters: "no constraint extracted" must not be conflated
// with "policy is unconstrained on this attribute". A policy that returns
// `false` anywhere must NEVER be represented in the tree (see
// `PolTreeIndex::build_from_policy_set`), because the tree's wildcard-fallback
// path treats "absent from every pv_map entry" as "matches unconditionally" --
// which is only sound for constraints we actually understood.
fn principal_or_resource_scope_constraints(
    entities: &Entities,
    type_index: &HashMap<EntityType, HashSet<EntityUID>>,
    attr_name: &str,
    constraint: &PrincipalOrResourceConstraint,
) -> (Vec<Constraint>, bool) {
    let attr = SmolStr::from(attr_name);
    match constraint {
        PrincipalOrResourceConstraint::Any => (vec![], true),
        PrincipalOrResourceConstraint::Eq(EntityReference::EUID(uid)) => (
            vec![Constraint {
                attr,
                values: vec![Literal::EntityUID(uid.clone())],
                candidates: entities_with_uid(entities, uid),
            }],
            true,
        ),
        PrincipalOrResourceConstraint::Is(entity_type) => (
            vec![Constraint {
                attr,
                values: vec![Literal::String(entity_type.to_smolstr())],
                candidates: candidates_from_type_index(type_index, entity_type),
            }],
            true,
        ),
        PrincipalOrResourceConstraint::In(EntityReference::EUID(_))
        | PrincipalOrResourceConstraint::IsIn(_, EntityReference::EUID(_)) => (vec![], false),
        PrincipalOrResourceConstraint::Eq(EntityReference::Slot(_))
        | PrincipalOrResourceConstraint::In(EntityReference::Slot(_))
        | PrincipalOrResourceConstraint::IsIn(_, EntityReference::Slot(_)) => (vec![], false),
    }
}

fn action_scope_constraints(
    entities: &Entities,
    constraint: &ActionConstraint,
) -> (Vec<Constraint>, bool) {
    let attr = SmolStr::from(SCOPE_ACTION_ATTR);
    match constraint {
        ActionConstraint::Any => (vec![], true),
        ActionConstraint::Eq(uid) => (
            vec![Constraint {
                attr,
                values: vec![Literal::EntityUID(uid.clone())],
                candidates: entities_with_uid(entities, uid),
            }],
            true,
        ),
        ActionConstraint::In(_) => (vec![], false),
        #[cfg(feature = "tolerant-ast")]
        ActionConstraint::ErrorConstraint => (vec![], false),
    }
}

// Expr-tree walker: extract (attr, Literal) equality constraints from the non-scope
// condition of a policy. Returns whether `expr` was FULLY decomposed into such
// constraints with nothing left over -- see the module comment above.
fn collect_attr_constraints(expr: &Expr, constraints: &mut Vec<(SmolStr, Literal)>) -> bool {
    // Which side (principal/resource) `base` is, if it's one of those two vars.
    fn side_of(base: &Expr) -> Option<bool> {
        match base.expr_kind() {
            ExprKind::Var(Var::Principal) => Some(true),
            ExprKind::Var(Var::Resource) => Some(false),
            _ => None,
        }
    }
    fn is_context_var(base: &Expr) -> bool {
        matches!(base.expr_kind(), ExprKind::Var(Var::Context))
    }

    match expr.expr_kind() {
        ExprKind::And { left, right } => {
            let l = collect_attr_constraints(left, constraints);
            let r = collect_attr_constraints(right, constraints);
            l && r
        }
        ExprKind::BinaryApp {
            op: BinaryOp::Eq,
            arg1,
            arg2,
        } => {
            match (arg1.expr_kind(), arg2.expr_kind()) {
                (
                    ExprKind::GetAttr { expr: base, attr }, // rename to base to avoid conflict with function argument
                    ExprKind::Lit(lit),
                ) => {
                    if let Some(is_principal) = side_of(base) {
                        constraints.push((side_scoped_attr(is_principal, attr), lit.clone()));
                        true
                    } else if is_context_var(base) {
                        constraints.push((context_attr_key(attr), lit.clone()));
                        true
                    } else {
                        false
                    }
                }
                (ExprKind::Lit(lit), ExprKind::GetAttr { expr: base, attr }) => {
                    if let Some(is_principal) = side_of(base) {
                        constraints.push((side_scoped_attr(is_principal, attr), lit.clone()));
                        true
                    } else if is_context_var(base) {
                        constraints.push((context_attr_key(attr), lit.clone()));
                        true
                    } else {
                        false
                    }
                }
                _ => false,
            }
        }
        _ => false,
    }
}

/// Determine, for a single policy, whether every scope and non-scope constraint
/// could be soundly captured as flat equality constraints -- see the notes
/// above `principal_or_resource_scope_constraints` and `collect_attr_constraints`.
/// `forbid`-effect policies always report `false`: this tree has no notion of
/// forbid overriding permit, so a forbid can never be safely represented by it.
///
/// This is cheaper than `PolTreeIndex::build_from_policy_set` since it discards
/// the extracted constraints -- useful when only the indexed/residual split is
/// needed without paying for a full index/tree rebuild (e.g. when restoring a
/// previously-serialized `PolTree` from disk, which does not persist this split).
pub fn policy_is_fully_indexed(policy: &Policy, entities: &Entities) -> bool {
    if policy.effect() == Effect::Forbid {
        return false;
    }
    // The `Is` branch's `ok` is a constant `true` regardless of what
    // candidates end up in the discarded constraint list below, so an empty
    // type index is fine here -- this function only cares about the
    // fully-indexed boolean, never the actual candidate entity sets.
    let empty_type_index = HashMap::new();
    let (_, ok1) = principal_or_resource_scope_constraints(
        entities,
        &empty_type_index,
        SCOPE_PRINCIPAL_ATTR,
        policy.template().principal_constraint().as_inner(),
    );
    let (_, ok2) = principal_or_resource_scope_constraints(
        entities,
        &empty_type_index,
        SCOPE_RESOURCE_ATTR,
        policy.template().resource_constraint().as_inner(),
    );
    let (_, ok3) = action_scope_constraints(entities, policy.template().action_constraint());
    let ok4 = match policy.template().non_scope_constraints() {
        Some(expr) => collect_attr_constraints(expr, &mut Vec::new()),
        None => true,
    };
    ok1 && ok2 && ok3 && ok4
}

/// The IDs of every policy in `policy_set` that is NOT fully indexable (see
/// [`policy_is_fully_indexed`]) -- i.e. every policy that a [`PolTree`] must
/// exclude and that callers must instead evaluate with a real Cedar evaluator.
pub fn residual_policy_ids(policy_set: &PolicySet, entities: &Entities) -> Vec<PolicyID> {
    policy_set
        .policies()
        .filter(|p| !policy_is_fully_indexed(p, entities))
        .map(|p| p.id().clone())
        .collect()
}

/// Build a `PolicySet` containing exactly the policies in `policy_set` whose
/// IDs appear in `residual_ids` -- for real (non-indexed) evaluation of the
/// policies a [`PolTree`] had to exclude.
pub fn build_residual_policy_set_from_ids(
    policy_set: &PolicySet,
    residual_ids: &[PolicyID],
) -> PolicySet {
    let residual_ids: HashSet<&PolicyID> = residual_ids.iter().collect();
    let mut out = PolicySet::new();
    for policy in policy_set.policies() {
        if residual_ids.contains(policy.id()) {
            // `policy_set` is known-valid and we are only re-inserting
            // policies it already contains, so this cannot fail.
            let _ = out.add(policy.clone());
        }
    }
    out
}

/// Convenience combining [`residual_policy_ids`] and
/// [`build_residual_policy_set_from_ids`] for callers that don't already have
/// the residual ID list on hand (e.g. after restoring a serialized [`PolTree`]).
pub fn build_residual_policy_set(policy_set: &PolicySet, entities: &Entities) -> PolicySet {
    build_residual_policy_set_from_ids(policy_set, &residual_policy_ids(policy_set, entities))
}

/// struct representing the entire PolTree
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PolTree {
    /// Root node of the PolTree
    pub root: PolTreeNode,
}

impl PolTree {
    /// Build an N-PolTree from an initial policy set, attribute list, and entity set
    pub fn build_n_poltree(
        policy_ids: Vec<PolicyID>,
        attrs: Vec<SmolStr>,
        entities: Vec<EntityUID>,
        index: &PolTreeIndex,
    ) -> Self {
        fn make_leaf(policy_ids: Vec<PolicyID>, entities: Vec<EntityUID>) -> PolTreeNode {
            let decision = if policy_ids.is_empty() {
                Decision::Deny
            } else {
                Decision::Allow
            };
            PolTreeNode {
                attr_val: None,
                split_attr: None,
                children: vec![],
                sv: entities,
                pv: policy_ids,
                eval: Some(decision),
            }
        }

        fn build_node(
            policy_ids: Vec<PolicyID>,
            attrs: Vec<SmolStr>,
            entities: Vec<EntityUID>,
            index: &PolTreeIndex,
        ) -> PolTreeNode {
            if attrs.is_empty() {
                return make_leaf(policy_ids, entities);
            }

            // Find best attr; if entropy=0 for all, still pick one that has pv_map entries
            let best_attr = best_attribute(&policy_ids, &entities, index, &attrs).or_else(|| {
                // fallback: pick any attr that still has policy constraints
                attrs
                    .iter()
                    .find(|attr| {
                        let ps: HashSet<&PolicyID> = policy_ids.iter().collect();
                        !index.values_for_attr_in_policies(attr, &ps).is_empty()
                    })
                    .cloned()
            });

            let best_attr = match best_attr {
                Some(a) => a,
                None => return make_leaf(policy_ids, entities), // truly no constraints left
            };

            // Build HashSets once before the loop so every membership test is O(1) instead of O(n)
            let policy_set: HashSet<&PolicyID> = policy_ids.iter().collect();
            let entity_set: HashSet<&EntityUID> = entities.iter().collect();

            let values = index.values_for_attr_in_policies(&best_attr, &policy_set);
            if values.is_empty() {
                return make_leaf(policy_ids, entities);
            }

            // A − {a}: consume `attrs` in-place instead of iter + clone
            let remaining_attrs: Vec<SmolStr> =
                attrs.into_iter().filter(|a| *a != best_attr).collect();

            let children: Vec<Box<PolTreeNode>> = {
                let mut ch: Vec<Box<PolTreeNode>> = values
                    .iter()
                    .map(|val| {
                        // Pv: policies in the current set where best_attr = val
                        let pv: Vec<PolicyID> = index
                            .get_pv(&best_attr, val)
                            .iter()
                            .filter(|id| policy_set.contains(id))
                            .cloned()
                            .collect();

                        // Sv: entities covered by Pv, intersected with current partition
                        let sv: Vec<EntityUID> = index
                            .get_sv_for_policies(&pv)
                            .into_iter()
                            .filter(|e| entity_set.contains(e))
                            .collect();

                        let mut child = build_node(pv, remaining_attrs.clone(), sv, index);
                        child.attr_val = Some((best_attr.clone(), val.clone()));
                        Box::new(child)
                    })
                    .collect();

                // policies with NO constraint on best_attr go under "*" branch
                let constrained_policies: HashSet<&PolicyID> = values
                    .iter()
                    .flat_map(|val| index.get_pv(&best_attr, val))
                    .filter(|id| policy_set.contains(id))
                    .collect();

                let wildcard_pv: Vec<PolicyID> = policy_ids
                    .iter()
                    .filter(|id| !constrained_policies.contains(id))
                    .cloned()
                    .collect();

                if !wildcard_pv.is_empty() {
                    let wildcard_sv: Vec<EntityUID> = index
                        .get_sv_for_policies(&wildcard_pv)
                        .into_iter()
                        .filter(|e| entity_set.contains(e))
                        .collect();
                    let mut wildcard_child =
                        build_node(wildcard_pv, remaining_attrs.clone(), wildcard_sv, index);
                    wildcard_child.attr_val =
                        Some((best_attr.clone(), Literal::String("*".into())));
                    ch.push(Box::new(wildcard_child));
                }
                ch
            };

            PolTreeNode {
                attr_val: None,
                split_attr: Some(best_attr.clone()),
                children,
                sv: entities,
                pv: policy_ids,
                eval: None,
            }
        }

        PolTree {
            root: build_node(policy_ids, attrs, entities, index),
        }
    }

    /// Convenience constructor which derives all required PolTree inputs from a [`PolicySet`] and an [`Entities`] store.
    ///
    /// Returns the built tree together with the IDs of any policies that could
    /// not be soundly represented in it (see [`PolTreeIndex::build_from_policy_set`]).
    /// Those policies are entirely excluded from the tree -- not indexed, not on
    /// any wildcard branch -- and must be evaluated by a real Cedar evaluator by
    /// the caller and combined with this tree's result.
    pub fn from_policy_set_and_entities(
        policy_set: &PolicySet,
        entities: Arc<Entities>,
    ) -> (Self, Vec<PolicyID>) {
        let (index, residual) = PolTreeIndex::build_from_policy_set(policy_set, entities);
        let residual_set: HashSet<&PolicyID> = residual.iter().collect();
        let policy_ids: Vec<PolicyID> = policy_set
            .policies()
            .map(|p| p.id().clone())
            .filter(|id| !residual_set.contains(id))
            .collect();
        let mut attrs: Vec<SmolStr> = index.attr_values.keys().cloned().collect();
        attrs.sort();
        attrs.dedup();
        let entities: Vec<EntityUID> = index.entities.iter().map(|e| e.uid().clone()).collect();
        (
            Self::build_n_poltree(policy_ids, attrs, entities, &index),
            residual,
        )
    }

    /// Evaluate one access request against this N-PolTree.
    /// Traversal follows exact-value branches first and keeps `*` branches in tracker for backtracking if an explored branch denies
    pub fn evaluate_request(
        &self,
        request: &Request,
        entities: &Entities,
    ) -> (Decision, Diagnostics) {
        let mut current = &self.root;
        let mut tracker: Vec<&PolTreeNode> = Vec::new();
        loop {
            if current.children.is_empty() {
                if current.eval == Some(Decision::Allow) {
                    return (
                        Decision::Allow,
                        Diagnostics {
                            reason: current.pv.iter().cloned().collect(),
                            errors: vec![],
                        },
                    );
                }
                if let Some(next) = tracker.pop() {
                    current = next;
                    continue;
                }
                return (
                    Decision::Deny,
                    Diagnostics {
                        reason: HashSet::new(),
                        errors: vec![],
                    },
                );
            }
            let split_attr = match &current.split_attr {
                Some(attr) => attr,
                None => {
                    if let Some(next) = tracker.pop() {
                        current = next;
                        continue;
                    }
                    return (
                        Decision::Deny,
                        Diagnostics {
                            reason: HashSet::new(),
                            errors: vec![],
                        },
                    );
                }
            };
            let request_val = request_values_for_attr(request, entities, split_attr);
            let mut wildcard_child: Option<&PolTreeNode> = None;
            let mut exact_children: Vec<&PolTreeNode> = Vec::new();

            for child in &current.children {
                if let Some((_, edge_val)) = &child.attr_val {
                    if matches!(edge_val, Literal::String(s) if s == "*") {
                        wildcard_child = Some(child.as_ref());
                    }
                    if request_val.contains(edge_val) {
                        exact_children.push(child.as_ref());
                    }
                }
            }
            if let Some(wildcard) = wildcard_child {
                tracker.push(wildcard);
            }
            if let Some(next) = exact_children.into_iter().next() {
                current = next;
                continue;
            }
            if let Some(next) = tracker.pop() {
                current = next;
                continue;
            }
            return (
                Decision::Deny,
                Diagnostics {
                    reason: HashSet::new(),
                    errors: vec![],
                },
            );
        }
    }
}

/// Indexes built from a PolicySet + Entities for efficient N-PolTree construction
#[derive(Debug, Clone)]
pub struct PolTreeIndex {
    /// The entity hierarchy this index was built from
    pub entities: Arc<Entities>,
    /// All attribute names and the set of literal values they take across all entities
    pub attr_values: HashMap<SmolStr, HashSet<Literal>>,
    /// Given (attr, val), which policy IDs constrain attr == val
    pub pv_map: HashMap<(SmolStr, Literal), Vec<PolicyID>>,
    /// Given (attr, val), which entity UIDs have that attribute value (used for entropy)
    pub sv_map: HashMap<(SmolStr, Literal), Vec<EntityUID>>,
    /// Given a policy ID, the entity UIDs that policy covers
    pub policy_entities_map: HashMap<PolicyID, Vec<EntityUID>>,
}
impl PolTreeIndex {
    /// Build a `PolTreeIndex` directly from a [`PolicySet`] and an [`Entities`] store.
    ///
    /// This is the preferred constructor: it derives `pv_map` and
    /// `policy_entities_map` automatically by walking each policy's condition
    /// expression and matching the extracted attribute constraints against the
    /// entity store, so callers do not need to supply those maps manually.
    ///
    /// Only flat equality constraints of the form `resource.attr == <literal>`,
    /// `principal.attr == <literal>`, or `context.attr == <literal>` (in either
    /// operand order) are recognised; more complex conditions — including
    /// attribute-to-attribute comparisons — are ignored (safe under-approximation).
    ///
    /// Policies whose scope or non-scope condition could not be FULLY captured
    /// as flat equality constraints -- and any `forbid`-effect policy, since
    /// this tree has no notion of forbid overriding permit -- are excluded from
    /// the returned index entirely and reported as the second return value.
    /// They must be evaluated by a real Cedar evaluator and combined with this
    /// tree's result by the caller; the index must never place them on a
    /// wildcard fallback branch, since "we don't know this policy's condition"
    /// is not the same as "this policy has no condition".
    pub fn build_from_policy_set(
        policy_set: &PolicySet,
        entities: Arc<Entities>,
    ) -> (Self, Vec<PolicyID>) {
        // One single pass over the entity store, reused for every constraint
        // of every policy below -- see `scan_entities`'s doc comment for why
        // this matters.
        let EntityScanIndexes {
            mut attr_values,
            sv_map,
            type_index,
        } = scan_entities(entities.as_ref());

        let mut pv_map: HashMap<(SmolStr, Literal), Vec<PolicyID>> = HashMap::new();
        let mut policy_entities_map: HashMap<PolicyID, Vec<EntityUID>> = HashMap::new();
        let mut residual: Vec<PolicyID> = Vec::new();

        for policy in policy_set.policies() {
            let pid = policy.id().clone();

            if policy.effect() == Effect::Forbid {
                residual.push(pid);
                continue;
            }

            let mut constraints: Vec<Constraint> = Vec::new();
            let mut fully_indexed = true;

            let (c, ok) = principal_or_resource_scope_constraints(
                entities.as_ref(),
                &type_index,
                SCOPE_PRINCIPAL_ATTR,
                policy.template().principal_constraint().as_inner(),
            );
            constraints.extend(c);
            fully_indexed &= ok;

            let (c, ok) = principal_or_resource_scope_constraints(
                entities.as_ref(),
                &type_index,
                SCOPE_RESOURCE_ATTR,
                policy.template().resource_constraint().as_inner(),
            );
            constraints.extend(c);
            fully_indexed &= ok;

            let (c, ok) = action_scope_constraints(
                entities.as_ref(),
                policy.template().action_constraint(),
            );
            constraints.extend(c);
            fully_indexed &= ok;

            let mut non_scope_constraints: Vec<(SmolStr, Literal)> = Vec::new();

            // Walk the non-scope (when/unless) condition expression
            if let Some(expr) = policy.template().non_scope_constraints() {
                fully_indexed &= collect_attr_constraints(expr, &mut non_scope_constraints);
            }

            if !fully_indexed {
                residual.push(pid);
                continue;
            }

            constraints.extend(non_scope_constraints.into_iter().map(|(attr, lit)| {
                // `attr` is either a side-scoped index key (see `side_scoped_attr`)
                // for principal/resource attributes, or a context-namespaced key
                // (see `context_attr_key`) for context attributes. Context isn't a
                // property of any entity, so there's nothing to look up in the
                // entity-derived indexes; candidates is left empty and such
                // constraints are excluded from the coverage intersection below
                // instead.
                let candidates = if is_context_attr(&attr) {
                    HashSet::new()
                } else {
                    // `attr` is the side-scoped index key (see `side_scoped_attr`);
                    // `candidates_from_sv_map` needs the underlying entity
                    // attribute name to actually find matching entities.
                    let raw_attr = split_side_scoped_attr(attr.as_str())
                        .map(|(_, raw)| SmolStr::from(raw))
                        .unwrap_or_else(|| attr.clone());
                    candidates_from_sv_map(&sv_map, &raw_attr, &lit)
                };
                Constraint {
                    candidates,
                    attr,
                    values: vec![lit],
                }
            }));

            if constraints.is_empty() {
                // Genuinely unconditional policy (e.g. `permit(principal, action, resource);`).
                // Correctly represented by the tree's natural wildcard fallback: it is
                // present in every node's `policy_ids` but has no pv_map entry, so it is
                // found only once every more specific branch has been tried -- which is
                // exactly right, since it really does match everything.
                continue;
            }

            // Register each extracted constraint in pv_map
            for constraint in &constraints {
                for value in &constraint.values {
                    pv_map
                        .entry((constraint.attr.clone(), value.clone()))
                        .or_default()
                        .push(pid.clone());
                }
            }

            // Compute policy_entities_map: entities that satisfy ALL extracted
            // constraints for this policy (intersection across constraints)
            // Start with the candidates for the first constraint, then intersect with candidates for each subsequent constraint.
            let mut covered: Option<HashSet<EntityUID>> = None;
            for constraint in &constraints {
                // Context conditions don't narrow which entities a policy
                // covers, so they're excluded from the intersection: only
                // principal/resource (and scope) constraints affect Sv.
                if is_context_attr(&constraint.attr) {
                    continue;
                }
                covered = Some(match covered.take() {
                    None => constraint.candidates.clone(),
                    Some(existing) => existing
                        .intersection(&constraint.candidates)
                        .cloned()
                        .collect(),
                });
            }
            if let Some(set) = covered {
                policy_entities_map.insert(pid, set.into_iter().collect());
            }
        }

        // `attr_values` from `scan_entities` already covers every value that
        // actually appears on some entity; merge in any additional values
        // referenced only by policy constraints (e.g. a scope `is <Type>`
        // string, or a `principal == X` EntityUID literal, neither of which
        // necessarily also appears as a literal attribute value on some
        // entity).
        for (attr, val) in pv_map.keys() {
            attr_values
                .entry(attr.clone())
                .or_default()
                .insert(val.clone());
        }

        (
            Self {
                entities,
                attr_values,
                pv_map,
                sv_map,
                policy_entities_map,
            },
            residual,
        )
    }

    /// Build a `PolTreeIndex` from an `Entities` store and caller-provided policy maps
    pub fn build_from_entities(
        entities: Arc<Entities>,
        pv_map: HashMap<(SmolStr, Literal), Vec<PolicyID>>,
        policy_entities_map: HashMap<PolicyID, Vec<EntityUID>>,
    ) -> Self {
        let mut attr_values: HashMap<SmolStr, HashSet<Literal>> = HashMap::new();
        let mut sv_map: HashMap<(SmolStr, Literal), Vec<EntityUID>> = HashMap::new();

        for entity in entities.iter() {
            let uid = entity.uid().clone();
            for (attr, pval) in entity.attrs() {
                // Only index scalar (Literal) values; skip sets, records, residuals
                if let PartialValue::Value(v) = pval {
                    if let Some(lit) = v.try_as_lit() {
                        let lit = lit.clone();
                        attr_values
                            .entry(attr.clone())
                            .or_default()
                            .insert(lit.clone());
                        sv_map
                            .entry((attr.clone(), lit))
                            .or_default()
                            .push(uid.clone());
                    }
                }
            }
        }
        for (attr, val) in pv_map.keys() {
            attr_values
                .entry(attr.clone())
                .or_default()
                .insert(val.clone());
        }
        Self {
            entities,
            attr_values,
            pv_map,
            sv_map,
            policy_entities_map,
        }
    }

    /// Look up a full [`Entity`] by UID, delegating to the underlying [`Entities`] store
    pub fn get_entity(&self, uid: &EntityUID) -> Dereference<'_, Entity> {
        self.entities.entity(uid)
    }

    /// Get the policy IDs where attr equals val
    pub fn get_pv(&self, attr: &SmolStr, val: &Literal) -> &[PolicyID] {
        self.pv_map
            .get(&(attr.clone(), val.clone()))
            .map_or(&[], Vec::as_slice)
    }
    /// Get the entity UIDs whose attr equals val (used for entropy computation)
    pub fn get_sv(&self, attr: &SmolStr, val: &Literal) -> &[EntityUID] {
        self.sv_map
            .get(&(attr.clone(), val.clone()))
            .map_or(&[], Vec::as_slice)
    }
    /// Get all entity UIDs covered by the given set of policies
    pub fn get_sv_for_policies(&self, policy_ids: &[PolicyID]) -> Vec<EntityUID> {
        let mut seen: HashSet<&EntityUID> = HashSet::new();
        let mut result = Vec::new();
        for pid in policy_ids {
            if let Some(entities) = self.policy_entities_map.get(pid) {
                for e in entities {
                    if seen.insert(e) {
                        result.push(e.clone());
                    }
                }
            }
        }
        result
    }

    fn values_for_attr_in_policies(
        &self,
        attr: &SmolStr,
        policy_ids: &HashSet<&PolicyID>,
    ) -> Vec<Literal> {
        self.pv_map
            .iter()
            .filter(|((candidate_attr, _), ids)| {
                candidate_attr == attr && ids.iter().any(|id| policy_ids.contains(id))
            })
            .map(|((_, val), _)| val.clone())
            .collect::<HashSet<_>>()
            .into_iter()
            .collect()
    }
}

fn attr_entropy(sv: &[EntityUID], index: &PolTreeIndex, attr: &SmolStr) -> f64 {
    let values = match index.attr_values.get(attr) {
        Some(v) => v,
        None => return 0.0,
    };
    let total = sv.len() as f64;
    if total == 0.0 {
        return 0.0;
    }
    let sv_set: HashSet<&EntityUID> = sv.iter().collect();
    values
        .iter()
        .map(|val| {
            let count = index
                .get_sv(attr, val)
                .iter()
                .filter(|e| sv_set.contains(e))
                .count();
            if count == 0 {
                0.0
            } else {
                let p = count as f64 / total;
                -p * p.log2()
            }
        })
        .sum()
}

fn best_attribute(
    policy_ids: &[PolicyID],
    sv: &[EntityUID],
    index: &PolTreeIndex,
    attrs: &[SmolStr],
) -> Option<SmolStr> {
    let policy_set: HashSet<&PolicyID> = policy_ids.iter().collect();

    attrs
        .iter()
        .filter(|attr| {
            !index
                .values_for_attr_in_policies(attr, &policy_set)
                .is_empty()
        })
        .map(|attr| (attr, attr_entropy(sv, index, attr)))
        .filter(|(_, h)| h.is_finite() && *h > 0.0)
        .max_by(|(_, h1), (_, h2)| h1.partial_cmp(h2).unwrap())
        .map(|(attr, _)| attr.clone())
}

/// Node in the PolTree
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PolTreeNode {
    /// The attribute value pair this node got split on from its parent (Label on the incoming edge, None for root)
    pub attr_val: Option<(SmolStr, Literal)>,
    /// The attribute this node splits on
    pub split_attr: Option<SmolStr>,
    /// Child nodes
    pub children: Vec<Box<PolTreeNode>>,
    /// Sv: entity UIDs covered by the policies in this partition
    pub sv: Vec<EntityUID>,
    /// Pv: policy IDs that constrain given attribute value pair
    pub pv: Vec<PolicyID>,
    /// Final access decision for leaf nodes
    pub eval: Option<Decision>,
}
