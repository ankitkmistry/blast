use core::fmt;
use std::{
    cell::RefCell,
    collections::HashMap,
    rc::{Rc, Weak},
};

use crate::{ast, scope};

#[derive(Clone)]
pub struct Param<'a> {
    pub name: Option<String>,
    pub taipe: Type<'a>,
    pub node: &'a ast::TypeFunctionParam,
}

impl<'a> ToString for Param<'a> {
    fn to_string(&self) -> String {
        match &self.name {
            Some(name) => format!("{}: {}", name, self.taipe.to_string()),
            None => self.taipe.to_string(),
        }
    }
}

impl<'a> fmt::Debug for Param<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Param")
            .field("name", &self.name)
            .field("taipe", &self.taipe)
            .finish()
    }
}

#[derive(Clone, Debug)]
pub enum Type<'a> {
    Bool,
    Char,
    Const(Box<Type<'a>>),
    Basic(Weak<RefCell<scope::Scope<'a>>>),
    Function {
        ret: Box<Type<'a>>,
        params: Vec<Param<'a>>,
    },
    Pointer(Box<Type<'a>>),
    Array {
        count: usize,
        taipe: Box<Type<'a>>,
    },
    Fat(Box<Type<'a>>),
    Tuple(Vec<Type<'a>>),
    Module,
    Typedef,
    Noreturn,
}

impl<'a> ToString for Type<'a> {
    fn to_string(&self) -> String {
        match self {
            Type::Bool => "__bool".to_string(),
            Type::Char => "__char".to_string(),
            Type::Const(taipe) => format!("const {}", taipe.to_string()),
            Type::Basic(weak) => todo!(),
            Type::Function { ret, params } => format!(
                "fun ({}) -> ({})",
                params
                    .iter()
                    .map(|param| param.to_string())
                    .collect::<Vec<_>>()
                    .join(", "),
                ret.to_string()
            ),
            Type::Pointer(taipe) => format!("*{}", taipe.to_string()),
            Type::Array { count, taipe } => format!("[{}]{}", count, taipe.to_string()),
            Type::Fat(taipe) => format!("[]{}", taipe.to_string()),
            Type::Tuple(items) => format!(
                "({})",
                items
                    .iter()
                    .map(|item| item.to_string())
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
            Type::Module => "module".to_string(),
            Type::Typedef => "typedef".to_string(),
            Type::Noreturn => "noreturn".to_string(),
        }
    }
}

#[derive(Clone)]
pub struct Struct<'a> {
    pub fields: HashMap<String, Context<'a>>,
    pub node: &'a ast::Object,
}

impl<'a> fmt::Debug for Struct<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Struct")
            .field("fields", &self.fields)
            .finish()
    }
}

#[derive(Clone, Debug)]
pub enum Value<'a> {
    Bool(bool),
    Char(char),
    Array(Vec<Value<'a>>),
    Tuple(Vec<Value<'a>>),
    // Typedef values
    Type(Type<'a>),
    Struct(Struct<'a>),
    Noreturn,
    // Module
    Module(Weak<RefCell<scope::Scope<'a>>>),
}

impl<'a> Value<'a> {
    pub fn from_str(text: &str) -> Self {
        Self::Array(text.chars().map(|c| Value::Char(c)).collect::<Vec<_>>())
    }
}

#[derive(Clone, Debug)]
pub struct Context<'a> {
    pub taipe: Type<'a>,
    pub value: Option<Value<'a>>,
}

impl<'a> Context<'a> {
    pub fn from_bool(value: bool) -> Self {
        Self {
            taipe: Type::Bool,
            value: Some(Value::Bool(value)),
        }
    }
    pub fn from_char(c: char) -> Self {
        Self {
            taipe: Type::Char,
            value: Some(Value::Char(c)),
        }
    }
    pub fn from_str(text: &str) -> Self {
        let chars = text.chars().map(|c| Value::Char(c)).collect::<Vec<_>>();
        Context {
            taipe: Type::Array {
                count: chars.len(),
                taipe: Box::new(Type::Char),
            },
            value: Some(Value::Array(chars)),
        }
    }
    pub fn from_tuple(types: Vec<Type<'a>>, values: Vec<Value<'a>>) -> Self {
        Context {
            taipe: Type::Tuple(types),
            value: Some(Value::Tuple(values)),
        }
    }
    pub fn from_type(taipe: Type<'a>) -> Self {
        Self {
            taipe: Type::Typedef,
            value: Some(Value::Type(taipe)),
        }
    }
    pub fn from_type_literal() -> Self {
        Self {
            taipe: Type::Typedef,
            value: Some(Value::Type(Type::Typedef)),
        }
    }
    pub fn from_noreturn() -> Self {
        Self {
            taipe: Type::Noreturn,
            value: Some(Value::Noreturn),
        }
    }
    pub fn from_module(module: Weak<RefCell<scope::Scope<'a>>>) -> Self {
        Self {
            taipe: Type::Module,
            value: Some(Value::Module(module)),
        }
    }
}

impl<'a> ToString for Context<'a> {
    fn to_string(&self) -> String {
        self.taipe.to_string()
    }
}
