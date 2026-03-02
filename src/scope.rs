use std::{
    cell::RefCell,
    collections::HashMap,
    rc::{Rc, Weak},
};

use crate::{
    ast,
    common::{HasLineInfo, LineInfo},
    context::Context,
    lexer::Token,
};

#[derive(Clone)]
pub enum State<'a> {
    NotEvaled(&'a ast::Decl),
    EvalInProg,
    Evaled(Context<'a>),
}

pub struct Scope<'a> {
    pub parent: Weak<RefCell<Scope<'a>>>,
    pub file_path: Option<String>,
    pub name: Option<Token>,
    pub node: Option<&'a ast::Object>,
    pub state: State<'a>,
    pub children: HashMap<String, Rc<RefCell<Scope<'a>>>>,
}

impl<'a> Scope<'a> {
    pub fn new_root(file_path: &str, node: &'a ast::Object) -> Rc<RefCell<Self>> {
        Rc::<RefCell<Self>>::new_cyclic(|module| {
            RefCell::new(Self {
                parent: Weak::new(),
                file_path: Some(file_path.to_owned()),
                name: None,
                node: Some(node),
                state: State::Evaled(Context::from_module(module.clone())),
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
    ) -> Option<Rc<RefCell<Scope<'a>>>> {
        let result = Rc::new(RefCell::new(Self {
            parent: Rc::downgrade(parent),
            file_path: None,
            name: name_tok,
            node,
            state,
            children: HashMap::new(),
        }));
        parent.borrow_mut().children.insert(name.to_owned(), result)
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
