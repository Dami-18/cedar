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
use crate::entities::Entities;
use smol_str::SmolStr;
use std::collections::{HashMap, HashSet};

// pub struct PolTree {
//     pub root: PolTreeNode,
// }

/// Indexes built from a PolicySet + Entities for efficient N-PolTree construction
#[derive(Debug)]
pub struct PolTreeIndex {
    /// All attribute names and the set of values they are compared against across the policy set
    pub attr_values: HashMap<SmolStr, HashSet<Literal>>,
    /// Given (attr, val), which policy IDs constrain attr == val
    pub pv_map: HashMap<(SmolStr, Literal), Vec<PolicyID>>,
    /// Given (attr, val), which entity UIDs have that attribute value
    pub sv_map: HashMap<(SmolStr, Literal), Vec<EntityUID>>,
}
impl PolTreeIndex {
    /// Get the policy IDs where attr equals val
    pub fn get_pv(&self, attr: &SmolStr, val: &Literal) -> &[PolicyID] {
        self.pv_map
            .get(&(attr.clone(), val.clone()))
            .map_or(&[], Vec::as_slice)
    }
    /// Get the entity UIDs whose attr equals val
    pub fn get_sv(&self, attr: &SmolStr, val: &Literal) -> &[EntityUID] {
        self.sv_map
            .get(&(attr.clone(), val.clone()))
            .map_or(&[], Vec::as_slice)
    }
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
    /// Policy IDs in this node's pv that also constrain attr == val
    pub fn get_pv<'a>(&self, index: &'a PolTreeIndex, attr: &SmolStr, val: &Literal) -> Vec<&'a PolicyID> {
        index
            .get_pv(attr, val)
            .iter()
            .filter(|id| self.pv.contains(id))
            .collect()
    }
    /// Entity UIDs in this node's sv that have attr = val
    pub fn get_sv<'a>(&self, index: &'a PolTreeIndex, attr: &SmolStr, val: &Literal) -> Vec<&'a EntityUID> {
        index
            .get_sv(attr, val)
            .iter()
            .filter(|e| self.sv.contains(e))
            .collect()
    }
    /// Entropy of attribute
    pub fn entropy(&self, index: &PolTreeIndex, attr: &SmolStr) -> f64 {
        let values = match index.attr_values.get(attr) {
            Some(v) => v,
            None => return 0.0,
        };
        let total = self.sv.len() as f64;
        if total == 0.0 {
            return 0.0;
        }
        values
            .iter()
            .map(|val| {
                let count = self.get_sv(index, attr, val).len();
                if count == 0 {
                    0.0
                } else {
                    let p = count as f64 / total;
                    -p * p.log2()
                }
            })
            .sum()
    }
    /// Attribute to split
    pub fn best_attribute(&self, index: &PolTreeIndex, attrs: &[SmolStr]) -> Option<SmolStr> {
        attrs
            .iter()
            .map(|attr| (attr, self.entropy(index, attr)))
            .filter(|(_, h)| h.is_finite() && *h > 0.0)
            .max_by(|(_, h1), (_, h2)| h1.partial_cmp(h2).unwrap())
            .map(|(attr, _)| attr.clone())
    }
}