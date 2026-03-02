/*
 * Copyright Cedar Contributors
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
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
use crate::authorizer::Decision;
use crate::entities::Entities; // can we use this somehow, it already provides lookups by entity IDs
use smol_str::SmolStr;
use std::collections::{HashMap, HashSet};

#[derive(Debug)]
pub struct PolTree {
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
            let decision = if policy_ids.is_empty() { Decision::Deny } else { Decision::Allow };
            PolTreeNode {
                attr_val: None,
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

            // best_attribute uses only `entities` (sv), so call it directly
            // without constructing a probe node.
            let best_attr = match best_attribute(&entities, index, &attrs) {
                Some(a) => a,
                None => return make_leaf(policy_ids, entities), // no information gain
            };

            // Build HashSets once before the loop so every membership test
            // is O(1) instead of O(n).
            let policy_set: HashSet<&PolicyID> = policy_ids.iter().collect();
            let entity_set: HashSet<&EntityUID> = entities.iter().collect();

            // Borrow the value set — use a local empty set as fallback
            // so we never need to clone the whole HashSet.
            let empty_values = HashSet::new();
            let values: &HashSet<Literal> = index
                .attr_values
                .get(&best_attr)
                .unwrap_or(&empty_values);

            // A − {a}: consume `attrs` in-place instead of iter + clone
            let remaining_attrs: Vec<SmolStr> =
                attrs.into_iter().filter(|a| *a != best_attr).collect();

            let children: Vec<Box<PolTreeNode>> = values
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

                    // Set attr_val directly instead of mutating after construction.
                    let mut child = build_node(pv, remaining_attrs.clone(), sv, index);
                    child.attr_val = Some((best_attr.clone(), val.clone()));
                    Box::new(child)
                })
                .collect();

            PolTreeNode {
                attr_val: None,
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
}

/// Indexes built from a PolicySet + Entities for efficient N-PolTree construction
#[derive(Debug, Clone)]
pub struct PolTreeIndex {
    /// All attribute names and the set of values they are compared against across the policy set
    pub attr_values: HashMap<SmolStr, HashSet<Literal>>,
    /// Given (attr, val), which policy IDs constrain attr == val
    pub pv_map: HashMap<(SmolStr, Literal), Vec<PolicyID>>,
    /// Given (attr, val), which entity UIDs have that attribute value (used for entropy)
    pub sv_map: HashMap<(SmolStr, Literal), Vec<EntityUID>>,
    /// Given a policy ID, the entity UIDs that policy covers
    pub policy_entities_map: HashMap<PolicyID, Vec<EntityUID>>,
}
impl PolTreeIndex {
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
        let mut seen = HashSet::new();
        let mut result = Vec::new();
        for pid in policy_ids {
            if let Some(entities) = self.policy_entities_map.get(pid) {
                for e in entities {
                    if seen.insert(e.clone()) {
                        result.push(e.clone());
                    }
                }
            }
        }
        result
    }
}

/// Entropy of `attr` over `sv`.
/// Builds a `HashSet` from `sv` **once** so every per-value membership test
/// is O(1) rather than O(|sv|).
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

/// Pick the attribute with the highest entropy over `sv`.
fn best_attribute(sv: &[EntityUID], index: &PolTreeIndex, attrs: &[SmolStr]) -> Option<SmolStr> {
    attrs
        .iter()
        .map(|attr| (attr, attr_entropy(sv, index, attr)))
        .filter(|(_, h)| h.is_finite() && *h > 0.0)
        .max_by(|(_, h1), (_, h2)| h1.partial_cmp(h2).unwrap())
        .map(|(attr, _)| attr.clone())
}

/// Node in the PolTree
#[derive(Debug)]
pub struct PolTreeNode {
    /// The attribute value pair this node splits on (None for leaf nodes)
    pub attr_val: Option<(SmolStr,Literal)>,
    /// Child nodes
    pub children: Vec<Box<PolTreeNode>>,
    /// Sv: entity UIDs covered by the policies in this partition
    pub sv: Vec<EntityUID>,
    /// Pv: policy IDs that constrain given attribute value pair
    pub pv: Vec<PolicyID>,
    /// Final access decision for leaf nodes
    pub eval: Option<Decision>,
}

impl PolTreeNode {
    /// Entity UIDs in this node's sv that have attr = val
    pub fn get_sv<'a>(&self, index: &'a PolTreeIndex, attr: &SmolStr, val: &Literal) -> Vec<&'a EntityUID> {
        let sv_set: HashSet<&EntityUID> = self.sv.iter().collect();
        index
            .get_sv(attr, val)
            .iter()
            .filter(|e| sv_set.contains(e))
            .collect()
    }
    /// Entropy of attribute over this node's entity set
    pub fn entropy(&self, index: &PolTreeIndex, attr: &SmolStr) -> f64 {
        attr_entropy(&self.sv, index, attr)
    }
    /// Attribute with the highest entropy (best split)
    pub fn best_attribute(&self, index: &PolTreeIndex, attrs: &[SmolStr]) -> Option<SmolStr> {
        best_attribute(&self.sv, index, attrs)
    }
}