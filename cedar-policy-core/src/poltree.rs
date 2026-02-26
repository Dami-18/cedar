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
use crate::entities::{Dereference, Entities};
use smol_str::SmolStr;
use std::collections::{HashMap, HashSet};

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
/// Node in the PolTree
#[derive(Debug)]
pub struct PolTreeNode {
    /// The attribute value pair this node splits on (None for leaf nodes)
    pub attr_val: Option<(SmolStr,Literal)>,
    /// Child nodes
    pub children: Vec<Box<PolTreeNode>>,
    /// Sv: entity UIDs covered by the policies in this partition
    pub sv: Vec<EntityUID>,
    /// Pv: policy IDs that constrain `split_attr == split_val`
    pub pv: Vec<PolicyID>,
    /// Final access decision for leaf nodes
    pub eval: Option<Decision>,
}