use indexmap::IndexMap;

use crate::{
    ast,
    common::{HasLineInfo, Layout, LineInfo},
    context::{self, Context},
};
use std::{
    cell::RefCell,
    collections::HashMap,
    rc::{Rc, Weak},
};

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

impl ToString for SymbolPath {
    fn to_string(&self) -> String {
        self.elms.join(".")
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

#[derive(Clone)]
pub enum ScopeNode<'a> {
    Decl(&'a ast::Decl),
    Field(&'a ast::Field),
    Object(&'a ast::Object),
}

impl<'a> HasLineInfo for ScopeNode<'a> {
    fn get_line_info(&self) -> LineInfo {
        match self {
            ScopeNode::Decl(decl) => decl.get_line_info(),
            ScopeNode::Field(field) => field.get_line_info(),
            ScopeNode::Object(object) => object.get_line_info(),
        }
    }
}

#[derive(Clone)]
pub enum State<'a> {
    /// Scope is not visited yet
    NotVisited(ScopeNode<'a>),
    /// Visitation is in progress
    VisitInProg,
    /// Scope has been visited
    Visited(Context<'a>),
}

#[derive(Clone)]
pub enum Payload<'a> {
    Compound(Compound<'a>),
    Function(Function<'a>),
    Block,
    LayoutResolutionInProg,
    None,
}

#[derive(Clone)]
pub struct LoopInfo;

#[derive(Clone)]
pub struct ParamInfo<'a> {
    pub taipe: context::Type<'a>,
    pub default: Option<context::Value<'a>>,
    pub line_info: LineInfo,
}

#[derive(Clone)]
pub struct Function<'a> {
    pub param_infos: IndexMap<String, ParamInfo<'a>>,
    pub loop_stack: IndexMap<String, LoopInfo>,
    pub ret_line_info: Option<LineInfo>,
}

impl<'a> Function<'a> {
    pub fn get_total_param_count(&self) -> usize {
        self.param_infos.len()
    }
    pub fn get_default_param_count(&self) -> usize {
        self.param_infos
            .iter()
            .filter(|(_, param)| param.default.is_some())
            .count()
    }
    pub fn get_min_param_count(&self) -> usize {
        self.param_infos
            .iter()
            .filter(|(_, param)| param.default.is_none())
            .count()
    }
    pub fn has_default_params(&self) -> bool {
        self.param_infos
            .iter()
            .any(|(_, param)| param.default.is_some())
    }
}

#[derive(Clone)]
pub enum Field<'a> {
    Struct(Vec<Field<'a>>),
    Union(Vec<Field<'a>>),
    Field {
        file_path: String,
        line_info: LineInfo,
        name: String,
        ctx: Context<'a>,
    },
}

#[derive(Clone, Copy, Debug)]
pub struct FieldData {
    pub offset: usize,
    pub size: usize,
    pub alignment: usize,
}

#[derive(Clone)]
pub struct Compound<'a> {
    pub field: Field<'a>,
    pub layout: Layout,
    pub offsets: HashMap<String, FieldData>,
}

impl<'a> Compound<'a> {
    pub fn new(field: Field<'a>) -> Self {
        Compound {
            field,
            layout: Default::default(),
            offsets: HashMap::new(),
        }
    }
}

pub type Map<K, V> = IndexMap<K, V>;

#[derive(Clone)]
pub struct Scope<'a> {
    /// Weak reference to the parent scope
    pub parent: Weak<RefCell<Scope<'a>>>,
    /// The file path to which this scope belongs to.
    /// If this is None, then the file path of this scope
    /// is the file path of the parent scope.
    pub file_path: Option<String>,
    /// The symbol path of the scope
    pub sym_path: SymbolPath,
    /// The name of the scope in the form of a token. (to improve error output)
    pub name: String,
    /// The line info of the scope.
    line_info: LineInfo,
    /// The state for the context evaluation of this scope
    pub state: State<'a>,
    /// The payload data for this scope.
    /// For example, a struct scope can have a payload related to field layout, padding, etc.
    pub payload: Payload<'a>,
    /// The children of this scope
    pub children: Map<String, Rc<RefCell<Scope<'a>>>>,
}

impl<'a> Scope<'a> {
    pub fn new_root(file_path: &str, node: &'a ast::Object) -> Rc<RefCell<Self>> {
        Rc::new(RefCell::new(Self {
            parent: Weak::new(),
            file_path: Some(file_path.to_owned()),
            sym_path: SymbolPath::new(),
            name: "".to_string(),
            line_info: node.get_line_info(),
            state: State::NotVisited(ScopeNode::Object(node)),
            payload: Payload::None,
            children: Map::new(),
        }))
    }

    pub fn add_child(
        parent: &Rc<RefCell<Scope<'a>>>,
        name: &str,
        state: State<'a>,
        line_info: &impl HasLineInfo,
    ) -> Rc<RefCell<Scope<'a>>> {
        // Create the symbol path
        let mut sym_path = parent.borrow().sym_path.clone();
        sym_path.push_name(name);
        // Create the child scope
        let child = Rc::new(RefCell::new(Self {
            parent: Rc::downgrade(parent),
            file_path: None,
            sym_path,
            name: name.to_string(),
            line_info: line_info.get_line_info(),
            state,
            payload: Payload::None,
            children: Map::new(),
        }));
        // Clone it so we can return later
        let result = Rc::clone(&child);
        // Finishing up
        let ret = parent.borrow_mut().children.insert(name.to_owned(), child);
        if name != "_" {
            assert!(
                ret.is_none(),
                "redeclaration should be prohibited from analyzer"
            );
        }
        result
    }

    pub fn is_function(&self) -> bool {
        match &self.state {
            State::NotVisited(_) => panic!("impossible to know"),
            State::VisitInProg => {
                if self.is_block() {
                    false
                } else {
                    panic!("impossible to know")
                }
            }
            State::Visited(ctx) => ctx.taipe.is_function(),
        }
    }

    pub fn get_enclosing_function(&self) -> Option<Rc<RefCell<Scope<'a>>>> {
        if let Some(parent) = self.parent.upgrade() {
            match &parent.borrow().state {
                State::NotVisited(_) => panic!("impossible to know"),
                State::VisitInProg => {
                    if self.is_block() {
                        parent.borrow().get_enclosing_function()
                    } else {
                        panic!("impossible to know")
                    }
                }
                State::Visited(ctx) => {
                    if ctx.taipe.is_function() {
                        Some(Rc::clone(&parent))
                    } else {
                        parent.borrow().get_enclosing_function()
                    }
                }
            }
        } else {
            None
        }
    }

    pub fn is_block(&self) -> bool {
        match self.payload {
            Payload::Block => true,
            _ => false,
        }
    }

    pub fn get_enclosing_block(&self) -> Option<Rc<RefCell<Scope<'a>>>> {
        if let Some(parent) = self.parent.upgrade() {
            match parent.borrow().payload {
                Payload::Block => Some(Rc::clone(&parent)),
                _ => None,
            }
        } else {
            None
        }
    }
}

pub trait HasSrcInfo: HasLineInfo {
    fn get_src_path(&self) -> String;
}

impl<'a> HasLineInfo for Scope<'a> {
    fn get_line_info(&self) -> LineInfo {
        self.line_info
    }
}

impl<'a> HasSrcInfo for Scope<'a> {
    fn get_src_path(&self) -> String {
        if let Some(path) = &self.file_path {
            path.clone()
        } else if let Some(parent) = self.parent.upgrade() {
            parent.borrow().get_src_path()
        } else {
            panic!("all scopes must designated to some source file");
        }
    }
}
