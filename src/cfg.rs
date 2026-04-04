use std::{
    cell::RefCell,
    collections::HashMap,
    hash::{DefaultHasher, Hasher},
    rc::Rc,
};

use indexmap::IndexSet;

use crate::{
    common::{HasLineInfo, LineInfo},
    scope,
};

#[derive(Clone)]
pub enum ControlInfo<'a> {
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
            ControlInfo::VarUsed { line_info, scope } => {
                line_info.hash(state);
                std::ptr::hash(Rc::as_ptr(scope), state);
            }
            ControlInfo::VarAssigned { line_info, scope } => {
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

impl<'a> HasLineInfo for ControlInfo<'a> {
    fn get_line_info(&self) -> LineInfo {
        match self {
            ControlInfo::VarUsed { line_info, scope: _ } => *line_info,
            ControlInfo::VarAssigned { line_info, scope: _ } => *line_info,
        }
    }
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub enum ControlNode<'a> {
    Start,
    Info(ControlInfo<'a>),
    End,
}

type ControlNodeId = usize;

// INFO: No removal operations are possible on ControlGraph
pub struct ControlGraph<'a> {
    nodes: IndexSet<ControlNode<'a>>,
    outgoing: HashMap<ControlNodeId, HashMap<ControlNodeId, ()>>,
    incoming: HashMap<ControlNodeId, HashMap<ControlNodeId, ()>>,
}

impl<'a> ControlGraph<'a> {
    pub fn new() -> Self {
        Self {
            nodes: IndexSet::new(),
            outgoing: HashMap::new(),
            incoming: HashMap::new(),
        }
    }

    pub fn vertex_count(&self) -> usize {
        // or using self.incoming both are equivalent in this case
        self.outgoing.len()
    }
    pub fn edge_count(&self) -> usize {
        // or using self.incoming both are equivalent in this case
        self.outgoing.iter().map(|(_, m)| m.len()).sum()
    }

    pub fn insert_vertex(&mut self, vertex: ControlNode<'a>) -> ControlNodeId {
        let (index, inserted) = self.nodes.insert_full(vertex);
        if inserted {
            self.outgoing.insert(index, HashMap::new());
            self.incoming.insert(index, HashMap::new());
        }
        index
    }
    pub fn insert_edge(&mut self, from_id: ControlNodeId, to_id: ControlNodeId) -> bool {
        let Some(m) = self.outgoing.get_mut(&from_id) else {
            return false;
        };
        m.insert(to_id, ());
        let Some(m) = self.incoming.get_mut(&to_id) else {
            return false;
        };
        m.insert(from_id, ());
        true
    }
}
