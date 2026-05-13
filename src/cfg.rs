use std::{
    cell::RefCell,
    collections::{HashMap, HashSet},
    rc::Rc,
};

use indexmap::IndexSet;

use crate::{common::LineInfo, scope};

#[derive(Clone)]
pub enum ControlInfo<'a> {
    VarDeclared {
        scope: Rc<RefCell<scope::Scope<'a>>>,
    },
    VarUsed {
        line_info: LineInfo,
        scope: Rc<RefCell<scope::Scope<'a>>>,
    },
    VarAssigned {
        line_info: LineInfo,
        scope: Rc<RefCell<scope::Scope<'a>>>,
    },
}

impl<'a> std::hash::Hash for ControlInfo<'a> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        core::mem::discriminant(self).hash(state);
        match self {
            ControlInfo::VarDeclared { scope } => {
                std::ptr::hash(Rc::as_ptr(scope), state);
            }
            ControlInfo::VarUsed { line_info, scope } | ControlInfo::VarAssigned { line_info, scope } => {
                line_info.hash(state);
                std::ptr::hash(Rc::as_ptr(scope), state);
            }
        }
    }
}

impl<'a> PartialEq for ControlInfo<'a> {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (
                Self::VarUsed {
                    line_info: l_line_info,
                    scope: l_scope,
                },
                Self::VarUsed {
                    line_info: r_line_info,
                    scope: r_scope,
                },
            ) => l_line_info == r_line_info && Rc::ptr_eq(l_scope, r_scope),
            (
                Self::VarAssigned {
                    line_info: l_line_info,
                    scope: l_scope,
                },
                Self::VarAssigned {
                    line_info: r_line_info,
                    scope: r_scope,
                },
            ) => l_line_info == r_line_info && Rc::ptr_eq(l_scope, r_scope),
            _ => false,
        }
    }
}

impl<'a> Eq for ControlInfo<'a> {}

#[derive(Clone, PartialEq, Eq, Hash)]
pub enum ControlNode<'a> {
    /// Start node of a control graph
    Start,
    /// A node where multiple nodes meet
    Junction,
    /// A node where some operation occurs
    Info(ControlInfo<'a>),
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
pub struct ControlGraph<'a> {
    nodes: IndexSet<ControlNode<'a>>,
    outgoing: HashMap<ControlNodeId, HashSet<ControlNodeId>>,
}

impl<'a> ControlGraph<'a> {
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

    pub fn get_vertex(&self, node_id: ControlNodeId) -> Option<&ControlNode<'a>> {
        self.nodes.get_index(node_id.0)
    }

    pub fn insert_vertex(&mut self, vertex: ControlNode<'a>) -> ControlNodeId {
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
