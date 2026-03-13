use std::{
    cell::RefCell,
    collections::HashMap,
    fmt,
    rc::{Rc, Weak},
};

use crate::{
    ast,
    common::{HasLineInfo, LineInfo},
    context::Context,
    lexer::Token,
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

    pub fn is_empty(&self) -> bool {
        self.elms.is_empty()
    }

    pub fn get_elements(&self) -> &[String] {
        &self.elms
    }
}

#[derive(Clone)]
pub enum State<'a> {
    NotEvaled(&'a ast::Decl),
    EvalInProg,
    Evaled(Context<'a>),
}

pub enum Payload<'a> {
    Compound(Compound<'a>),
}

#[derive(Clone)]
pub struct Compound<'a> {
    fields: Vec<(String, Context<'a>)>,
    pub node: &'a ast::Object,
}

impl<'a> Compound<'a> {
    pub fn new(fields: &[(String, Context<'a>)], node: &'a ast::Object) -> Self {
        Compound {
            fields: fields.to_vec(),
            node,
        }
    }
}

impl<'a> fmt::Debug for Compound<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Compound")
            .field("fields", &self.fields)
            .finish()
    }
}

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
    pub name: Option<Token>,
    /// The ast node of the scope. This is None only in the case of folder modules
    pub node: Option<&'a ast::Object>,
    /// The state for the context evaluation of this scope
    pub state: State<'a>,
    /// The payload data for this scope. For example, a struct scope can have a payload
    /// related to field layout, padding, etc.
    pub payload: Option<Payload<'a>>,
    /// The children of this scope
    pub children: HashMap<String, Rc<RefCell<Scope<'a>>>>,
}

impl<'a> Scope<'a> {
    pub fn new_root(file_path: &str, node: &'a ast::Object) -> Rc<RefCell<Self>> {
        Rc::new_cyclic(|module| {
            RefCell::new(Self {
                parent: Weak::new(),
                file_path: Some(file_path.to_owned()),
                sym_path: SymbolPath::new(),
                name: None,
                node: Some(node),
                state: State::Evaled(Context::from_module(module.clone())),
                payload: None,
                children: HashMap::new(),
            })
        })
    }

    pub fn add_child(
        parent: &Rc<RefCell<Scope<'a>>>,
        name: &str,
        name_tok: Option<Token>,
        state: State<'a>,
        node: Option<&'a ast::Object>,
    ) -> Rc<RefCell<Scope<'a>>> {
        // Create the symbol path
        let mut sym_path = parent.borrow().sym_path.clone();
        sym_path.push_name(name);
        // Create the child scope
        let child = Rc::new(RefCell::new(Self {
            parent: Rc::downgrade(parent),
            file_path: None,
            sym_path,
            name: name_tok,
            node,
            state,
            payload: None,
            children: HashMap::new(),
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
}

pub trait HasSrcInfo: HasLineInfo {
    fn get_src_path(&self) -> String;
}

impl<'a> HasLineInfo for Scope<'a> {
    fn get_line_info(&self) -> LineInfo {
        if let Some(tok) = &self.name {
            return tok.get_line_info();
        }
        if let Some(node) = &self.node {
            return node.get_line_info();
        }
        panic!("oops! no line info...");
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
