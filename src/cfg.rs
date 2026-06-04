use std::collections::{HashMap, HashSet};

use indexmap::IndexSet;

use crate::{common::LineInfo, scope::ScopeId};

// ------------------------------------------------------------
// Control Flow Analysis structures
// ------------------------------------------------------------

#[derive(Clone, Hash, PartialEq, Eq)]
pub enum ControlInfo {
    VarDeclared {
        scope_id: ScopeId,
    },
    VarUsed {
        line_info: LineInfo,
        scope_id: ScopeId,
    },
    VarAssigned {
        line_info: LineInfo,
        scope_id: ScopeId,
    },
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub enum ControlNode {
    /// Start node of a control graph
    Start,
    /// A node where multiple nodes meet
    Junction,
    /// A node where some operation occurs
    Info(ControlInfo),
    /// A special node that indicates return from a function
    Return,
    /// End node of a control graph
    End,
    /// Any outgoing node from this node is never executed
    Unreachable,
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ControlNodeId(usize);

// INFO: No removal operations are possible on ControlGraph
pub struct ControlGraph {
    nodes: IndexSet<ControlNode>,
    outgoing: HashMap<ControlNodeId, HashSet<ControlNodeId>>,
}

impl ControlGraph {
    pub fn new() -> Self {
        Self {
            nodes: IndexSet::new(),
            outgoing: HashMap::new(),
        }
    }

    // pub fn vertex_count(&self) -> usize {
    //     // or using self.incoming both are equivalent in this case
    //     self.outgoing.len()
    // }
    // pub fn edge_count(&self) -> usize {
    //     // or using self.incoming both are equivalent in this case
    //     self.outgoing.iter().map(|(_, m)| m.len()).sum()
    // }

    pub fn get_vertex(&self, node_id: ControlNodeId) -> Option<&ControlNode> {
        self.nodes.get_index(node_id.0)
    }

    pub fn insert_vertex(&mut self, vertex: ControlNode) -> ControlNodeId {
        let (index, inserted) = self.nodes.insert_full(vertex);
        let index = ControlNodeId(index);
        if inserted {
            self.outgoing.insert(index, HashSet::new());
        }
        index
    }
    pub fn insert_edge(&mut self, from_id: ControlNodeId, to_id: ControlNodeId) -> bool {
        if from_id == to_id {
            log::warn!("insert_edge: from_id and to_id are same");
        }

        let Some(m) = self.outgoing.get_mut(&from_id) else {
            return false;
        };
        m.insert(to_id);
        true
    }

    pub fn outgoing(&self, node_id: ControlNodeId) -> HashSet<ControlNodeId> {
        if let Some(m) = self.outgoing.get(&node_id) {
            m.clone()
        } else {
            HashSet::new()
        }
    }
}
