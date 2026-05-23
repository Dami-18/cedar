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

#[derive(Debug, Clone)]
struct Constraint {
    attr: SmolStr,
    values: Vec<Literal>,
    candidates: HashSet<EntityUID>,
}

fn entities_with_attr_literal(
    entities: &Entities,
    attr: &SmolStr,
    lit: &Literal,
) -> HashSet<EntityUID> {
    entities
        .iter()
        .filter(|e| {
            e.get(attr).and_then(|pv| match pv {
                PartialValue::Value(v) => v.try_as_lit(),
                _ => None,
            }) == Some(lit)
        })
        .map(|e| e.uid().clone())
        .collect()
}

fn entities_with_uid(entities: &Entities, uid: &EntityUID) -> HashSet<EntityUID> {
    entities
        .iter()
        .filter(|e| e.uid() == uid)
        .map(|e| e.uid().clone())
        .collect()
}

fn entities_with_type(entities: &Entities, entity_type: &EntityType) -> HashSet<EntityUID> {
    entities
        .iter()
        .filter(|e| e.uid().entity_type() == entity_type)
        .map(|e| e.uid().clone())
        .collect()
}

fn request_scope_literal(request: &Request, attr: &SmolStr) -> Option<Literal> {
    match attr.as_str() {
        SCOPE_PRINCIPAL_ATTR => request
            .principal()
            .uid()
            .map(|uid| Literal::EntityUID(Arc::new(uid.clone()))),
        SCOPE_RESOURCE_ATTR => request
            .resource()
            .uid()
            .map(|uid| Literal::EntityUID(Arc::new(uid.clone()))),
        SCOPE_ACTION_ATTR => request
            .action()
            .uid()
            .map(|uid| Literal::EntityUID(Arc::new(uid.clone()))),
        _ => None,
    }
}

fn request_values_for_attr(request: &Request, entities: &Entities, attr: &SmolStr) -> Vec<Literal> {
    if let Some(scope_literal) = request_scope_literal(request, attr) {
        return vec![scope_literal];
    }

    let mut values: HashSet<Literal> = HashSet::new();

    for entry in [request.resource(), request.principal()] {
        let Some(uid) = entry.uid() else {
            continue;
        };
        if let Dereference::Data(entity) = entities.entity(uid) {
            if let Some(PartialValue::Value(v)) = entity.get(attr.as_str()) {
                if let Some(lit) = v.try_as_lit() {
                    values.insert(lit.clone());
                }
            }
        }
    }

    values.into_iter().collect()
}

fn principal_or_resource_scope_constraints(
    entities: &Entities,
    attr_name: &str,
    constraint: &PrincipalOrResourceConstraint,
) -> Vec<Constraint> {
    let attr = SmolStr::from(attr_name);
    match constraint {
        PrincipalOrResourceConstraint::Any => vec![],
        PrincipalOrResourceConstraint::Eq(EntityReference::EUID(uid)) => vec![Constraint {
            attr,
            values: vec![Literal::EntityUID(uid.clone())],
            candidates: entities_with_uid(entities, uid),
        }],
        PrincipalOrResourceConstraint::Is(entity_type) => vec![Constraint {
            attr,
            values: vec![Literal::String(entity_type.to_smolstr())],
            candidates: entities_with_type(entities, entity_type),
        }],
        PrincipalOrResourceConstraint::In(EntityReference::EUID(_))
        | PrincipalOrResourceConstraint::IsIn(_, EntityReference::EUID(_)) => vec![],
        PrincipalOrResourceConstraint::Eq(EntityReference::Slot(_))
        | PrincipalOrResourceConstraint::In(EntityReference::Slot(_))
        | PrincipalOrResourceConstraint::IsIn(_, EntityReference::Slot(_)) => vec![],
    }
}

fn action_scope_constraints(entities: &Entities, constraint: &ActionConstraint) -> Vec<Constraint> {
    let attr = SmolStr::from(SCOPE_ACTION_ATTR);
    match constraint {
        ActionConstraint::Any => vec![],
        ActionConstraint::Eq(uid) => vec![Constraint {
            attr,
            values: vec![Literal::EntityUID(uid.clone())],
            candidates: entities_with_uid(entities, uid),
        }],
        ActionConstraint::In(_) => vec![],
        #[cfg(feature = "tolerant-ast")]
        ActionConstraint::ErrorConstraint => vec![],
    }
}

// Expr-tree walker: extract (attr, Literal) equality constraints from the non-scope condition of a policy
fn collect_attr_constraints(expr: &Expr, constraints: &mut Vec<(SmolStr, Literal)>) {
    match expr.expr_kind() {
        ExprKind::And { left, right } => {
            collect_attr_constraints(left, constraints);
            collect_attr_constraints(right, constraints);
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
                ) if matches!(
                    base.expr_kind(),
                    ExprKind::Var(Var::Resource) | ExprKind::Var(Var::Principal)
                ) =>
                {
                    constraints.push((attr.clone(), lit.clone()));
                }
                (ExprKind::Lit(lit), ExprKind::GetAttr { expr: base, attr })
                    if matches!(
                        base.expr_kind(),
                        ExprKind::Var(Var::Resource) | ExprKind::Var(Var::Principal)
                    ) =>
                {
                    constraints.push((attr.clone(), lit.clone()));
                }
                _ => {}
            }
        }
        _ => {}
    }
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
    pub fn from_policy_set_and_entities(policy_set: &PolicySet, entities: Arc<Entities>) -> Self {
        let index = PolTreeIndex::build_from_policy_set(policy_set, entities);
        let policy_ids: Vec<PolicyID> = policy_set.policies().map(|p| p.id().clone()).collect();
        let mut attrs: Vec<SmolStr> = index.attr_values.keys().cloned().collect();
        attrs.sort();
        attrs.dedup();
        let entities: Vec<EntityUID> = index.entities.iter().map(|e| e.uid().clone()).collect();
        Self::build_n_poltree(policy_ids, attrs, entities, &index)
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
    /// Only flat equality constraints of the form
    /// `resource.attr == <literal>` (or `principal.attr == <literal>`) are
    /// recognised; more complex conditions are ignored (safe under-approximation).
    pub fn build_from_policy_set(policy_set: &PolicySet, entities: Arc<Entities>) -> Self {
        let mut pv_map: HashMap<(SmolStr, Literal), Vec<PolicyID>> = HashMap::new();
        let mut policy_entities_map: HashMap<PolicyID, Vec<EntityUID>> = HashMap::new();

        for policy in policy_set.policies() {
            let pid = policy.id().clone();
            let mut constraints: Vec<Constraint> = Vec::new();

            constraints.extend(principal_or_resource_scope_constraints(
                entities.as_ref(),
                SCOPE_PRINCIPAL_ATTR,
                policy.template().principal_constraint().as_inner(),
            ));
            constraints.extend(principal_or_resource_scope_constraints(
                entities.as_ref(),
                SCOPE_RESOURCE_ATTR,
                policy.template().resource_constraint().as_inner(),
            ));
            constraints.extend(action_scope_constraints(
                entities.as_ref(),
                policy.template().action_constraint(),
            ));

            let mut non_scope_constraints: Vec<(SmolStr, Literal)> = Vec::new();

            // Walk the non-scope (when/unless) condition expression
            if let Some(expr) = policy.template().non_scope_constraints() {
                collect_attr_constraints(expr, &mut non_scope_constraints);
            }

            constraints.extend(
                non_scope_constraints
                    .into_iter()
                    .map(|(attr, lit)| Constraint {
                        candidates: entities_with_attr_literal(entities.as_ref(), &attr, &lit),
                        attr,
                        values: vec![lit],
                    }),
            );

            if constraints.is_empty() {
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

        Self::build_from_entities(entities, pv_map, policy_entities_map)
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
