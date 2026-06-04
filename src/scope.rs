use std::{collections::HashMap, fmt, sync::atomic::AtomicU64};

use indexmap::IndexMap;

use crate::{cfg::{ControlGraph, ControlNodeId}, common::{HasLineInfo, Layout, LineInfo}, context::{self, Context}};

// ------------------------------------------------------------
// Scope things
// ------------------------------------------------------------

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct SymbolPath {
    elms: Vec<String>,
}

impl From<&str> for SymbolPath {
    fn from(value: &str) -> Self {
        SymbolPath {
            elms: value
                .to_string()
                .split('.')
                .map(|item| item.to_owned())
                .collect::<Vec<String>>(),
        }
    }
}

impl fmt::Display for SymbolPath {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.elms.join("."))
    }
}

impl SymbolPath {
    pub fn new() -> Self {
        Self { elms: Vec::new() }
    }

    pub fn push_name(&mut self, name: &str) {
        self.elms.push(name.to_owned());
    }

    // pub fn is_empty(&self) -> bool {
    //     self.elms.is_empty()
    // }
    //
    // pub fn get_elements(&self) -> &[String] {
    //     &self.elms
    // }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct ScopeId {
    pub index: usize,
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ScopeKind {
    Module,
    Compound,
    Function,
    Param,
    Variable,
    Const,
    Typedef,
    Block,
    None,
}

pub enum Payload {
    Compound(CompoundInfo),
    Function(FunctionInfo),
    Global(GlobalInfo),
    Local(LocalInfo),
    Typedef(context::Type),
    Block(BlockInfo),
    Param(ParamInfo),
    LayoutResolutionInProgress,
    None
}

pub struct GlobalInfo {
    pub ctx: Context,
}

pub struct LocalInfo {
    pub taipe: context::Type,
}

#[derive(Clone)]
pub enum FieldInfo {
    Struct(Vec<FieldInfo>),
    Union(Vec<FieldInfo>),
    Field {
        file_path: String,
        line_info: LineInfo,
        name: String,
        taipe: context::Type,
    },
}

#[derive(Clone)]
pub struct FieldData {
    pub name: String,
    pub taipe: context::Type,
    pub file_path: String,
    pub line_info: LineInfo,
    
    pub offset: usize,
    pub size: usize,
    pub alignment: usize,
}

#[derive(Clone)]
pub struct CompoundInfo {
    pub field: FieldInfo,
    pub layout: Layout,
    pub field_data_table: HashMap<String, FieldData>,
}

impl CompoundInfo {
    pub fn new(field: FieldInfo) -> Self {
        CompoundInfo {
            field,
            layout: Default::default(),
            field_data_table: HashMap::new(),
        }
    }
}

#[derive(Copy, Clone)]
pub struct LoopInfo {
    pub cf_break: ControlNodeId,
    pub cf_continue: ControlNodeId,
}

pub struct ParamInfo {
    pub taipe: context::Type,
    pub default: Option<context::Value>,
    pub line_info: LineInfo,
}

pub struct FunctionInfo {
    pub taipe: context::Type,
    pub ctx: Option<Context>,
    pub param_table: IndexMap<String, ScopeId>,
    pub default_param_count: usize,
    pub loop_stack: IndexMap<String, LoopInfo>,
    pub ret_line_info: Option<LineInfo>,
}

impl FunctionInfo {
    pub fn get_return_type(&self) -> &context::Type {
        let context::Type::Function { ref ret, params: _ } = self.taipe else {
            unreachable!("probably some analyzer bug");
        };
        ret
    }
    pub fn get_total_param_count(&self) -> usize {
        self.param_table.len()
    }
    pub fn get_default_param_count(&self) -> usize {
        self.default_param_count
    }
    pub fn get_min_param_count(&self) -> usize {
        self.get_total_param_count() - self.get_default_param_count()
    }
    pub fn has_default_params(&self) -> bool {
        self.get_default_param_count() > 0
    }
}

pub struct BlockInfo {
    /// Context containing the code of the block
    pub ctx: Context,
    /// Control flow graph of the block
    pub cfg: ControlGraph,
    /// The start node of the graph
    pub cf_start: ControlNodeId,
    /// The end node of the graph
    pub cf_end: ControlNodeId,
    /// The node that was last added to the graph
    pub cf_last: ControlNodeId,
    /// An isolated unreachable node for attaching unreachable code
    pub cf_unreachable: ControlNodeId,
}

pub struct Scope {
    pub id: ScopeId,
    pub kind: ScopeKind,
    pub file_path: Option<String>,
    pub sym_path: SymbolPath,
    pub name: String,
    pub line_info: LineInfo,
    pub payload: Payload,
    
    pub parent: Option<ScopeId>,
    pub children: IndexMap<String, ScopeId>,

    /// Counter for generating unique names of anonymous scopes
    pub unique_counter: AtomicU64,
    /// Counter for generating unique names of blocks
    pub block_counter: AtomicU64,
    /// Counter for generating unique names of anonymous loop labels
    pub loop_counter: AtomicU64,
}

impl Scope {
    pub fn is_module(&self) -> bool {
        match self.kind {
            ScopeKind::Module => true,
            _ => false,
        }
    }

    pub fn is_const(&self) -> bool {
        match self.kind {
            ScopeKind::Const => true,
            _ => false,
        }
    }

    pub fn is_variable(&self) -> bool {
        match self.kind {
            ScopeKind::Variable => true,
            _ => false,
        }
    }

    pub fn is_typedef(&self) -> bool {
        match self.kind {
            ScopeKind::Typedef => true,
            _ => false,
        }
    }

    pub fn is_function(&self) -> bool {
        match self.kind {
            ScopeKind::Function => true,
            _ => false,
        }
    }

    pub fn is_block(&self) -> bool {
        match self.kind {
            ScopeKind::Block => true,
            _ => false,
        }
    }

    pub fn get_type(&self) -> &context::Type {
        match self.kind {
            ScopeKind::Module => &context::Type::Module,
            ScopeKind::Compound => &context::Type::Typedef,
            ScopeKind::Function => {
                let Payload::Function(ref info) = self.payload else {
                    unreachable!("probably some analyzer bug");
                };
                &info.taipe
            },
            ScopeKind::Param => {
                let Payload::Param(ref info) = self.payload else {
                    unreachable!("probably some analyzer bug");
                };
                &info.taipe
            },
            ScopeKind::Variable => {
                match self.payload {
                    Payload::Global(ref info) => &info.ctx.taipe,
                    Payload::Local(ref info) => &info.taipe,
                    _ => unreachable!("probably some analyzer bug"),
                }
            },
            ScopeKind::Const => {
                match self.payload {
                    Payload::Global(ref info) => &info.ctx.taipe,
                    Payload::Local(ref info) => &info.taipe,
                    _ => unreachable!("probably some analyzer bug"),
                }
            },
            ScopeKind::Typedef => panic!("type has no type"),
            ScopeKind::Block => {
                let Payload::Block(ref info) = self.payload else {
                    unreachable!("probably some analyzer bug");
                };
                &info.ctx.taipe
            },
            ScopeKind::None => unreachable!("probably some analyzer bug"),
        }
    }
}

impl HasLineInfo for Scope {
    fn get_line_info(&self) -> LineInfo {
        self.line_info
    }
}
