use core::fmt;
use std::{
    cell::RefCell,
    collections::HashMap,
    rc::{Rc, Weak},
};

use crate::{ast, common::Int, scope};

#[derive(Clone)]
pub struct Param<'a> {
    pub name: Option<String>,
    pub taipe: Type<'a>,
    pub node: &'a ast::TypeFunctionParam,
}

impl<'a> PartialEq for Param<'a> {
    fn eq(&self, other: &Self) -> bool {
        self.name == other.name && self.taipe == other.taipe
    }
}

impl<'a> Eq for Param<'a> {}

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
    // Value can be:
    // - Value::Bool => boolean value
    Bool,
    // Value can be:
    // - Value::Char => char value
    Char,
    // Value can be:
    // - Value::Int => integer value
    Int,
    // Value can be:
    // - Value::Float32 => float32 value
    Float32,
    // Value can be:
    // - Value::Float64 => float64 value
    Float64,
    // Value can be:
    // - depending on Type::Const.0
    Const(Box<Type<'a>>),
    // Value can be:
    // - TODO: object
    Basic(Weak<RefCell<scope::Scope<'a>>>),
    // Value can be:
    // - TODO: function
    Function {
        ret: Box<Type<'a>>,
        params: Vec<Param<'a>>,
    },
    // Value can be:
    // - depending on Type::Const.0
    Pointer(Box<Type<'a>>),
    // Value can be:
    // - depending on Type::Const.taipe
    Array {
        count: usize,
        taipe: Box<Type<'a>>,
    },
    // Value can be:
    // - depending on Type::Const.0
    Fat(Box<Type<'a>>),
    // Value can be:
    // - Value::Tuple => tuple value
    Tuple(Vec<Type<'a>>),
    // Value can be:
    // - Value::Module => module reference
    Module,
    // Value can be:
    // - None => type literal itself: 'typedef'
    // - Value::Type => type reference
    Typedef,
    // Value can be:
    // - Value::Noreturn => just a noreturn marker
    Noreturn,
}

impl<'a> Type<'a> {
    pub fn remove_const(&self) -> Self {
        match self.clone() {
            Type::Const(taipe) => *taipe,
            taipe => taipe,
        }
    }
    pub fn is_integer(&self) -> bool {
        match self {
            Type::Int => true,
            Type::Const(taipe) => taipe.is_integer(),
            _ => false,
        }
    }
    pub fn is_typedef(&self) -> bool {
        match self {
            Type::Typedef => true,
            _ => false,
        }
    }
    pub fn is_const(&self) -> bool {
        match self {
            Type::Const(_) => true,
            Type::Function { ret, params } => true,
            Type::Module => true,
            Type::Typedef => true,
            _ => false,
        }
    }
    pub fn is_module(&self) -> bool {
        match self {
            Type::Module => true,
            _ => false,
        }
    }
}

impl<'a> PartialEq for Type<'a> {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Const(l0), Self::Const(r0)) => l0 == r0,
            (Self::Basic(l0), Self::Basic(r0)) => Weak::ptr_eq(l0, r0),
            (
                Self::Function {
                    ret: l_ret,
                    params: l_params,
                },
                Self::Function {
                    ret: r_ret,
                    params: r_params,
                },
            ) => l_ret == r_ret && l_params == r_params,
            (Self::Pointer(l0), Self::Pointer(r0)) => l0 == r0,
            (
                Self::Array {
                    count: l_count,
                    taipe: l_taipe,
                },
                Self::Array {
                    count: r_count,
                    taipe: r_taipe,
                },
            ) => l_count == r_count && l_taipe == r_taipe,
            (Self::Fat(l0), Self::Fat(r0)) => l0 == r0,
            (Self::Tuple(l0), Self::Tuple(r0)) => l0 == r0,
            _ => core::mem::discriminant(self) == core::mem::discriminant(other),
        }
    }
}

impl<'a> Eq for Type<'a> {}

impl<'a> ToString for Type<'a> {
    fn to_string(&self) -> String {
        match self {
            Type::Bool => "__bool".to_string(),
            Type::Char => "__char".to_string(),
            Type::Int => "__int".to_string(),
            Type::Float32 => "__f32".to_string(),
            Type::Float64 => "__f64".to_string(),
            Type::Const(taipe) => format!("const {}", taipe.to_string()),
            Type::Basic(scope) => scope.upgrade().unwrap().borrow().sym_path.to_string(),
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

#[derive(Clone, Debug)]
pub enum Value<'a> {
    Bool(bool),
    Char(char),
    Int(Int),
    Float32(f32),
    Float64(f64),
    Array(Vec<Value<'a>>),
    Tuple(Vec<Value<'a>>),
    // Typedef values
    Type(Type<'a>),
    // Noreturn
    Noreturn,
    // Module
    Module(Weak<RefCell<scope::Scope<'a>>>),
}

impl<'a> Value<'a> {
    pub fn from_str(text: &str) -> Self {
        Self::Array(text.chars().map(|c| Value::Char(c)).collect::<Vec<_>>())
    }

    pub fn negate(mut self) -> Option<Self> {
        match self {
            Value::Int(int) => Some(Value::Int(int.negate())),
            Value::Float32(val) => Some(Value::Float32(-val)),
            Value::Float64(val) => Some(Value::Float64(-val)),
            _ => None,
        }
    }
}

impl<'a> ToString for Value<'a> {
    fn to_string(&self) -> String {
        match self {
            Value::Bool(b) => b.to_string(),
            Value::Char(c) => format!("'{}'", c.to_string()),
            Value::Int(num) => num.to_string(),
            Value::Float32(num) => num.to_string(),
            Value::Float64(num) => num.to_string(),
            Value::Array(values) => {
                let mut result = String::new();
                let mut is_string = false;
                for value in values {
                    match value {
                        Value::Char(c) => {
                            is_string = true;
                            result.push(*c);
                        }
                        other => {
                            result.push_str(&other.to_string());
                            result.push_str(", ");
                        }
                    }
                }
                if is_string {
                    format!("\"{}\"", result)
                } else {
                    result.pop();
                    result.pop();
                    result
                }
            }
            Value::Tuple(values) => format!(
                "({})",
                values
                    .iter()
                    .map(|value| value.to_string())
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
            Value::Type(t) => t.to_string(),
            Value::Noreturn => String::new(),
            Value::Module(weak) => String::new(),
        }
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
            // TODO: making this const has implications on
            // assigning a simple string to a variable (that is not const)
            taipe: Type::Const(Box::new(Type::Bool)),
            value: Some(Value::Bool(value)),
        }
    }
    pub fn from_char(c: char) -> Self {
        Self {
            // TODO: making this const has implications on
            // assigning a simple string to a variable (that is not const)
            taipe: Type::Const(Box::new(Type::Char)),
            value: Some(Value::Char(c)),
        }
    }
    pub fn from_str(text: &str) -> Self {
        let chars = text.chars().map(|c| Value::Char(c)).collect::<Vec<_>>();
        Context {
            taipe: Type::Array {
                count: chars.len(),
                taipe: Box::new(Type::Const(Box::new(Type::Char))),
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
            value: None,
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
