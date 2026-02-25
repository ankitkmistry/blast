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

pub struct Scope<'a> {
    pub parent: Weak<RefCell<Scope<'a>>>,
    pub file_path: Option<String>,
    pub name: Option<Token>,
    pub node: &'a ast::Object,
    pub ctx: Context<'a>,
    pub children: HashMap<String, Rc<RefCell<Scope<'a>>>>,
}

impl<'a> Scope<'a> {
    pub fn new_root(file_path: &str, node: &'a ast::Object) -> Rc<RefCell<Self>> {
        Rc::<RefCell<Self>>::new_cyclic(|module| {
            RefCell::new(Self {
                parent: Weak::new(),
                file_path: Some(file_path.to_owned()),
                name: None,
                node,
                ctx: Context::from_module(module.clone()),
                children: HashMap::new(),
            })
        })
    }

    pub fn add_child(
        scope: &Rc<RefCell<Scope<'a>>>,
        name: &str,
        name_tok: Option<Token>,
        ctx: Context<'a>,
        node: &'a ast::Object,
    ) {
        let result = Rc::new(RefCell::new(Self {
            parent: Rc::downgrade(scope),
            file_path: None,
            name: name_tok,
            node,
            ctx,
            children: HashMap::new(),
        }));
        scope.borrow_mut().children.insert(name.to_owned(), result);
    }
}

pub trait HasSrcInfo: HasLineInfo {
    fn get_src_path(&self) -> String;
}

impl<'a> HasLineInfo for Scope<'a> {
    fn get_line_info(&self) -> LineInfo {
        match &self.name {
            Some(tok) => tok.get_line_info(),
            _ => self.node.get_line_info(),
        }
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
