use std::{cell::RefCell, rc::Rc};

use indexmap::IndexMap;

use crate::{common::Int, scope};

#[derive(Clone)]
pub struct Param<'a> {
    pub taipe: Type<'a>,
}

impl<'a> PartialEq for Param<'a> {
    fn eq(&self, other: &Self) -> bool {
        self.taipe == other.taipe
    }
}

impl<'a> Eq for Param<'a> {}

impl<'a> ToString for Param<'a> {
    fn to_string(&self) -> String {
        self.taipe.to_string()
    }
}

#[derive(Clone)]
pub enum Type<'a> {
    /// Value can be:
    /// - Value::Bool => boolean value
    Bool,
    /// Value can be:
    /// - Value::Char => char value
    Char,
    /// Value can be:
    /// - Value::Int => integer value
    VarInt,
    Int8,
    Int16,
    Int32,
    Int64,
    Int128,
    Uint8,
    Uint16,
    Uint32,
    Uint64,
    Uint128,
    // Int,
    /// Value can be:
    /// - Value::Float32 => float32 value
    Float32,
    /// Value can be:
    /// - Value::Float64 => float64 value
    Float64,
    /// Value can be:
    /// - depending on Type::Const.0
    Const(Box<Type<'a>>),
    /// Value can be:
    /// - TODO: object
    Basic(Rc<RefCell<scope::Scope<'a>>>),
    /// Value can be:
    /// - Value::Function => Function value
    Function {
        ret: Box<Type<'a>>,
        params: Vec<Param<'a>>,
    },
    /// Value can be:
    /// - TODO: pointer
    Pointer(Box<Type<'a>>),
    /// Value can be:
    /// - Value::Array => array value
    Array {
        count: usize,
        taipe: Box<Type<'a>>,
    },
    /// Value can be:
    /// - Value::Array => array value
    Fat(Box<Type<'a>>),
    /// Value can be:
    /// - Value::Tuple => tuple value
    Tuple(Vec<Type<'a>>),
    /// Value can be:
    /// - Value::Module => module reference
    Module,
    /// Value can be:
    /// - None => type literal itself: 'typedef'
    /// - Value::Type => type reference
    Typedef,
    /// Value can be:
    /// - None
    Void,
    /// Value can be:
    /// - None
    Noreturn,
}

impl<'a> Type<'a> {
    pub fn add_const(self) -> Self {
        if self.is_const() {
            self
        } else {
            Type::Const(Box::new(self))
        }
    }

    pub fn remove_const(&self) -> Self {
        match self.clone() {
            Type::Const(taipe) => *taipe,
            taipe => taipe,
        }
    }
    pub fn is_bool(&self) -> bool {
        match self {
            Type::Bool => true,
            Type::Const(taipe) => taipe.is_bool(),
            _ => false,
        }
    }
    pub fn is_varint(&self) -> bool {
        match self {
            Type::VarInt => true,
            Type::Const(taipe) => taipe.is_varint(),
            _ => false,
        }
    }
    pub fn is_integer(&self) -> bool {
        match self {
            Type::VarInt
            | Type::Int8
            | Type::Int16
            | Type::Int32
            | Type::Int64
            | Type::Int128
            | Type::Uint8
            | Type::Uint16
            | Type::Uint32
            | Type::Uint64
            | Type::Uint128 => true,
            Type::Const(taipe) => taipe.is_integer(),
            _ => false,
        }
    }
    pub fn is_unsigned_integer(&self) -> bool {
        match self {
            Type::VarInt | Type::Uint8 | Type::Uint16 | Type::Uint32 | Type::Uint64 | Type::Uint128 => true,
            Type::Const(taipe) => taipe.is_unsigned_integer(),
            _ => false,
        }
    }
    pub fn is_float(&self) -> bool {
        match self {
            Type::Float32 | Type::Float64 => true,
            Type::Const(taipe) => taipe.is_float(),
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
            Type::Function { ret: _, params: _ } => true,
            Type::Module => true,
            Type::Typedef => true,
            Type::Noreturn => true,
            _ => false,
        }
    }
    pub fn is_module(&self) -> bool {
        match self {
            Type::Module => true,
            _ => false,
        }
    }
    pub fn is_function(&self) -> bool {
        match self {
            Type::Function { ret: _, params: _ } => true,
            _ => false,
        }
    }
    pub fn is_void(&self) -> bool {
        match self {
            Type::Void => true,
            Type::Const(taipe) => taipe.is_void(),
            _ => false,
        }
    }
    pub fn is_noreturn(&self) -> bool {
        match self {
            Type::Noreturn => true,
            _ => false,
        }
    }
}

impl<'a> PartialEq for Type<'a> {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Const(l0), Self::Const(r0)) => l0 == r0,
            (Self::Basic(l0), Self::Basic(r0)) => Rc::ptr_eq(l0, r0),
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
            Type::VarInt => "{integer}".to_string(),
            Type::Int8 => "__i8".to_string(),
            Type::Int16 => "__i16".to_string(),
            Type::Int32 => "__i32".to_string(),
            Type::Int64 => "__i64".to_string(),
            Type::Int128 => "__i128".to_string(),
            Type::Uint8 => "__u8".to_string(),
            Type::Uint16 => "__u16".to_string(),
            Type::Uint32 => "__u32".to_string(),
            Type::Uint64 => "__u64".to_string(),
            Type::Uint128 => "__u128".to_string(),
            Type::Float32 => "__f32".to_string(),
            Type::Float64 => "__f64".to_string(),
            Type::Const(taipe) => format!("const {}", taipe.to_string()),
            Type::Basic(scope) => scope.borrow().sym_path.to_string(),
            Type::Function { ret, params } => format!(
                "fun ({}) -> {}",
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
                items.iter().map(|item| item.to_string()).collect::<Vec<_>>().join(", ")
            ),
            Type::Module => "module".to_string(),
            Type::Typedef => "typedef".to_string(),
            Type::Void => "void".to_string(),
            Type::Noreturn => "noreturn".to_string(),
        }
    }
}

#[derive(Clone)]
pub enum Imm<'a> {
    Bool(bool),
    Char(char),
    VarInt(Int),
    Int8(i8),
    Int16(i16),
    Int32(i32),
    Int64(i64),
    Int128(i128),
    Uint8(u8),
    Uint16(u16),
    Uint32(u32),
    Uint64(u64),
    Uint128(u128),
    Float32(f32),
    Float64(f64),
    // Typedef values
    Type(Type<'a>),
    // Represents nothing
    Nil,
}

impl<'a> Imm<'a> {
    pub fn to_usize(&self) -> Option<usize> {
        match self {
            Imm::Int8(val) => usize::try_from(*val).ok(),
            Imm::Int16(val) => usize::try_from(*val).ok(),
            Imm::Int32(val) => usize::try_from(*val).ok(),
            Imm::Int64(val) => usize::try_from(*val).ok(),
            Imm::Int128(val) => usize::try_from(*val).ok(),
            Imm::Uint8(val) => usize::try_from(*val).ok(),
            Imm::Uint16(val) => usize::try_from(*val).ok(),
            Imm::Uint32(val) => usize::try_from(*val).ok(),
            Imm::Uint64(val) => usize::try_from(*val).ok(),
            Imm::Uint128(val) => usize::try_from(*val).ok(),
            _ => None,
        }
    }
    pub fn negate(self) -> Self {
        match self {
            Imm::Float32(val) => Imm::Float32(-val),
            Imm::Float64(val) => Imm::Float64(-val),
            Imm::Int8(val) => Imm::Int8(-val),
            Imm::Int16(val) => Imm::Int16(-val),
            Imm::Int32(val) => Imm::Int32(-val),
            Imm::Int64(val) => Imm::Int64(-val),
            Imm::Int128(val) => Imm::Int128(-val),
            _ => panic!("invalid operation on value"),
        }
    }
    pub fn flip_bits(self) -> Self {
        match self {
            Imm::Int8(val) => Imm::Int8(!val),
            Imm::Int16(val) => Imm::Int16(!val),
            Imm::Int32(val) => Imm::Int32(!val),
            Imm::Int64(val) => Imm::Int64(!val),
            Imm::Int128(val) => Imm::Int128(!val),
            Imm::Uint8(val) => Imm::Uint8(!val),
            Imm::Uint16(val) => Imm::Uint16(!val),
            Imm::Uint32(val) => Imm::Uint32(!val),
            Imm::Uint64(val) => Imm::Uint64(!val),
            Imm::Uint128(val) => Imm::Uint128(!val),
            _ => panic!("invalid operation on value"),
        }
    }
}

impl<'a> ToString for Imm<'a> {
    fn to_string(&self) -> String {
        match self {
            Imm::Bool(val) => val.to_string(),
            Imm::Char(val) => val.to_string(),
            Imm::VarInt(int) => int.to_string(),
            Imm::Int8(val) => val.to_string(),
            Imm::Int16(val) => val.to_string(),
            Imm::Int32(val) => val.to_string(),
            Imm::Int64(val) => val.to_string(),
            Imm::Int128(val) => val.to_string(),
            Imm::Uint8(val) => val.to_string(),
            Imm::Uint16(val) => val.to_string(),
            Imm::Uint32(val) => val.to_string(),
            Imm::Uint64(val) => val.to_string(),
            Imm::Uint128(val) => val.to_string(),
            Imm::Float32(val) => val.to_string(),
            Imm::Float64(val) => val.to_string(),
            Imm::Type(t) => t.to_string(),
            Imm::Nil => String::from("nil"),
        }
    }
}

// Cloning Value is strongly discouraged
#[derive(Clone)]
pub enum Value<'a> {
    Imm(Imm<'a>),
    Array(Vec<Value<'a>>),
    Tuple(Vec<Value<'a>>),
    /// Anything that can be referenced by an identifier
    Reference(Rc<RefCell<scope::Scope<'a>>>),
    // Unary Instructions
    Negate(Box<Context<'a>>),
    FlipBits(Box<Context<'a>>),
    Deref(Box<Context<'a>>),
    AddrOf(Box<Context<'a>>),
    Not(Box<Context<'a>>),
    // Binary Instructions
    Add(Box<Context<'a>>, Box<Context<'a>>),
    Sub(Box<Context<'a>>, Box<Context<'a>>),
    Mul(Box<Context<'a>>, Box<Context<'a>>),
    Div(Box<Context<'a>>, Box<Context<'a>>),
    Rem(Box<Context<'a>>, Box<Context<'a>>),
    Shl(Box<Context<'a>>, Box<Context<'a>>),
    Shr(Box<Context<'a>>, Box<Context<'a>>),
    BitAnd(Box<Context<'a>>, Box<Context<'a>>),
    BitXor(Box<Context<'a>>, Box<Context<'a>>),
    BitOr(Box<Context<'a>>, Box<Context<'a>>),
    Lt(Box<Context<'a>>, Box<Context<'a>>),
    Le(Box<Context<'a>>, Box<Context<'a>>),
    Eq(Box<Context<'a>>, Box<Context<'a>>),
    Ne(Box<Context<'a>>, Box<Context<'a>>),
    Ge(Box<Context<'a>>, Box<Context<'a>>),
    Gt(Box<Context<'a>>, Box<Context<'a>>),
    LogicAnd(Box<Context<'a>>, Box<Context<'a>>),
    LogicOr(Box<Context<'a>>, Box<Context<'a>>),
    // Postfix op instructions
    Index(Box<Context<'a>>, Box<Context<'a>>),
    Call(Rc<RefCell<scope::Scope<'a>>>, IndexMap<String, Context<'a>>),
    // Statement instructions
    Assign(Vec<Context<'a>>, Vec<Context<'a>>),
    IfElse(Box<Context<'a>>, Box<Context<'a>>, Box<Context<'a>>),
    If(Box<Context<'a>>, Box<Context<'a>>),
    While(Box<Context<'a>>, Box<Context<'a>>),
    Block(Vec<Context<'a>>),
    Ret(Box<Context<'a>>),
    Eval(Box<Context<'a>>),
    RetVoid,
    // Cast instructions
    // from: fX         to: fY
    // from: iX         to: iY
    // from: [N]T       to: []T
    Cast(Box<Context<'a>>),
}

impl<'a> Value<'a> {
    pub fn from_nil() -> Self {
        Self::Imm(Imm::Nil)
    }
    pub fn from_bool(b: bool) -> Self {
        Self::Imm(Imm::Bool(b))
    }
    // pub fn is_imm(&self) -> bool {
    //     match self {
    //         Value::Imm(_) => true,
    //         _ => false,
    //     }
    // }
}

// Cloning Context is strongly discouraged
#[derive(Clone)]
pub struct Context<'a> {
    pub is_lvalue: bool,
    pub taipe: Type<'a>,
    pub value: Value<'a>,
}

impl<'a> Context<'a> {
    pub fn from_module(module_ref: &Rc<RefCell<scope::Scope<'a>>>) -> Self {
        Self {
            is_lvalue: true,
            taipe: Type::Module,
            value: Value::Reference(Rc::clone(module_ref)),
        }
    }
    pub fn from_scope(taipe: &Type<'a>, scope_ref: &Rc<RefCell<scope::Scope<'a>>>) -> Self {
        Self {
            is_lvalue: true,
            taipe: taipe.clone(),
            value: Value::Reference(Rc::clone(scope_ref)),
        }
    }
    // Creating immediate values
    pub fn from_bool(value: bool) -> Self {
        Self {
            is_lvalue: false,
            taipe: Type::Bool,
            value: Value::Imm(Imm::Bool(value)),
        }
    }
    pub fn from_str(text: &str) -> Self {
        let chars = text.chars().map(|c| Value::Imm(Imm::Char(c))).collect::<Vec<_>>();
        Context {
            is_lvalue: false,
            taipe: Type::Array {
                count: chars.len(),
                taipe: Box::new(Type::Char),
            },
            value: Value::Array(chars),
        }
    }
    pub fn from_type(taipe: Type<'a>) -> Self {
        Self {
            is_lvalue: false,
            taipe: Type::Typedef,
            value: Value::Imm(Imm::Type(taipe)),
        }
    }
    pub fn from_void() -> Self {
        Self {
            is_lvalue: false,
            taipe: Type::Void,
            value: Value::Imm(Imm::Nil),
        }
    }
    pub fn from_noreturn() -> Self {
        Self {
            is_lvalue: false,
            taipe: Type::Noreturn,
            value: Value::Imm(Imm::Nil),
        }
    }
}

impl<'a> ToString for Context<'a> {
    fn to_string(&self) -> String {
        self.taipe.to_string()
    }
}

// impl<'a> Value<'a> {
//     pub fn add(self, other: Value<'a>) -> Option<Self> {
//         match (self, other) {
//             (Value::Int8(a), Value::Int8(b)) => a.checked_add(b).map(|value| Value::Int8(value)),
//             (Value::Int16(a), Value::Int16(b)) => a.checked_add(b).map(|value| Value::Int16(value)),
//             (Value::Int32(a), Value::Int32(b)) => a.checked_add(b).map(|value| Value::Int32(value)),
//             (Value::Int64(a), Value::Int64(b)) => a.checked_add(b).map(|value| Value::Int64(value)),
//             (Value::Int128(a), Value::Int128(b)) => {
//                 a.checked_add(b).map(|value| Value::Int128(value))
//             }
//             (Value::Uint8(a), Value::Uint8(b)) => a.checked_add(b).map(|value| Value::Uint8(value)),
//             (Value::Uint16(a), Value::Uint16(b)) => {
//                 a.checked_add(b).map(|value| Value::Uint16(value))
//             }
//             (Value::Uint32(a), Value::Uint32(b)) => {
//                 a.checked_add(b).map(|value| Value::Uint32(value))
//             }
//             (Value::Uint64(a), Value::Uint64(b)) => {
//                 a.checked_add(b).map(|value| Value::Uint64(value))
//             }
//             (Value::Uint128(a), Value::Uint128(b)) => {
//                 a.checked_add(b).map(|value| Value::Uint128(value))
//             }
//             (Value::Float32(a), Value::Float32(b)) => Some(Value::Float32(a + b)),
//             (Value::Float64(a), Value::Float64(b)) => Some(Value::Float64(a + b)),
//             _ => panic!("invalid operation on value"),
//         }
//     }
//     pub fn sub(self, other: Value<'a>) -> Option<Self> {
//         match (self, other) {
//             (Value::Int8(a), Value::Int8(b)) => a.checked_sub(b).map(|value| Value::Int8(value)),
//             (Value::Int16(a), Value::Int16(b)) => a.checked_sub(b).map(|value| Value::Int16(value)),
//             (Value::Int32(a), Value::Int32(b)) => a.checked_sub(b).map(|value| Value::Int32(value)),
//             (Value::Int64(a), Value::Int64(b)) => a.checked_sub(b).map(|value| Value::Int64(value)),
//             (Value::Int128(a), Value::Int128(b)) => {
//                 a.checked_sub(b).map(|value| Value::Int128(value))
//             }
//             (Value::Uint8(a), Value::Uint8(b)) => a.checked_sub(b).map(|value| Value::Uint8(value)),
//             (Value::Uint16(a), Value::Uint16(b)) => {
//                 a.checked_sub(b).map(|value| Value::Uint16(value))
//             }
//             (Value::Uint32(a), Value::Uint32(b)) => {
//                 a.checked_sub(b).map(|value| Value::Uint32(value))
//             }
//             (Value::Uint64(a), Value::Uint64(b)) => {
//                 a.checked_sub(b).map(|value| Value::Uint64(value))
//             }
//             (Value::Uint128(a), Value::Uint128(b)) => {
//                 a.checked_sub(b).map(|value| Value::Uint128(value))
//             }
//             (Value::Float32(a), Value::Float32(b)) => Some(Value::Float32(a - b)),
//             (Value::Float64(a), Value::Float64(b)) => Some(Value::Float64(a - b)),
//             _ => panic!("invalid operation on value"),
//         }
//     }
//     pub fn mul(self, other: Value<'a>) -> Option<Self> {
//         match (self, other) {
//             (Value::Int8(a), Value::Int8(b)) => a.checked_mul(b).map(|value| Value::Int8(value)),
//             (Value::Int16(a), Value::Int16(b)) => a.checked_mul(b).map(|value| Value::Int16(value)),
//             (Value::Int32(a), Value::Int32(b)) => a.checked_mul(b).map(|value| Value::Int32(value)),
//             (Value::Int64(a), Value::Int64(b)) => a.checked_mul(b).map(|value| Value::Int64(value)),
//             (Value::Int128(a), Value::Int128(b)) => {
//                 a.checked_mul(b).map(|value| Value::Int128(value))
//             }
//             (Value::Uint8(a), Value::Uint8(b)) => a.checked_mul(b).map(|value| Value::Uint8(value)),
//             (Value::Uint16(a), Value::Uint16(b)) => {
//                 a.checked_mul(b).map(|value| Value::Uint16(value))
//             }
//             (Value::Uint32(a), Value::Uint32(b)) => {
//                 a.checked_mul(b).map(|value| Value::Uint32(value))
//             }
//             (Value::Uint64(a), Value::Uint64(b)) => {
//                 a.checked_mul(b).map(|value| Value::Uint64(value))
//             }
//             (Value::Uint128(a), Value::Uint128(b)) => {
//                 a.checked_mul(b).map(|value| Value::Uint128(value))
//             }
//             (Value::Float32(a), Value::Float32(b)) => Some(Value::Float32(a * b)),
//             (Value::Float64(a), Value::Float64(b)) => Some(Value::Float64(a * b)),
//             _ => panic!("invalid operation on value"),
//         }
//     }
//     pub fn div(self, other: Value<'a>) -> Option<Self> {
//         match (self, other) {
//             (Value::Int8(a), Value::Int8(b)) => a.checked_div(b).map(|value| Value::Int8(value)),
//             (Value::Int16(a), Value::Int16(b)) => a.checked_div(b).map(|value| Value::Int16(value)),
//             (Value::Int32(a), Value::Int32(b)) => a.checked_div(b).map(|value| Value::Int32(value)),
//             (Value::Int64(a), Value::Int64(b)) => a.checked_div(b).map(|value| Value::Int64(value)),
//             (Value::Int128(a), Value::Int128(b)) => {
//                 a.checked_div(b).map(|value| Value::Int128(value))
//             }
//             (Value::Uint8(a), Value::Uint8(b)) => a.checked_div(b).map(|value| Value::Uint8(value)),
//             (Value::Uint16(a), Value::Uint16(b)) => {
//                 a.checked_div(b).map(|value| Value::Uint16(value))
//             }
//             (Value::Uint32(a), Value::Uint32(b)) => {
//                 a.checked_div(b).map(|value| Value::Uint32(value))
//             }
//             (Value::Uint64(a), Value::Uint64(b)) => {
//                 a.checked_div(b).map(|value| Value::Uint64(value))
//             }
//             (Value::Uint128(a), Value::Uint128(b)) => {
//                 a.checked_div(b).map(|value| Value::Uint128(value))
//             }
//             (Value::Float32(a), Value::Float32(b)) => Some(Value::Float32(a / b)),
//             (Value::Float64(a), Value::Float64(b)) => Some(Value::Float64(a / b)),
//             _ => panic!("invalid operation on value"),
//         }
//     }
//     pub fn modulo(self, other: Value<'a>) -> Option<Self> {
//         match (self, other) {
//             (Value::Int8(a), Value::Int8(b)) => a.checked_rem(b).map(|value| Value::Int8(value)),
//             (Value::Int16(a), Value::Int16(b)) => a.checked_rem(b).map(|value| Value::Int16(value)),
//             (Value::Int32(a), Value::Int32(b)) => a.checked_rem(b).map(|value| Value::Int32(value)),
//             (Value::Int64(a), Value::Int64(b)) => a.checked_rem(b).map(|value| Value::Int64(value)),
//             (Value::Int128(a), Value::Int128(b)) => {
//                 a.checked_rem(b).map(|value| Value::Int128(value))
//             }
//             (Value::Uint8(a), Value::Uint8(b)) => a.checked_rem(b).map(|value| Value::Uint8(value)),
//             (Value::Uint16(a), Value::Uint16(b)) => {
//                 a.checked_rem(b).map(|value| Value::Uint16(value))
//             }
//             (Value::Uint32(a), Value::Uint32(b)) => {
//                 a.checked_rem(b).map(|value| Value::Uint32(value))
//             }
//             (Value::Uint64(a), Value::Uint64(b)) => {
//                 a.checked_rem(b).map(|value| Value::Uint64(value))
//             }
//             (Value::Uint128(a), Value::Uint128(b)) => {
//                 a.checked_rem(b).map(|value| Value::Uint128(value))
//             }
//             _ => panic!("invalid operation on value"),
//         }
//     }
//     pub fn shl(self, other: Value<'a>) -> Self {
//         match (self, other) {
//             (Value::Int8(a), Value::Uint32(b)) => Value::Int8(a.wrapping_shl(b)),
//             (Value::Int16(a), Value::Uint32(b)) => Value::Int16(a.wrapping_shl(b)),
//             (Value::Int32(a), Value::Uint32(b)) => Value::Int32(a.wrapping_shl(b)),
//             (Value::Int64(a), Value::Uint32(b)) => Value::Int64(a.wrapping_shl(b)),
//             (Value::Int128(a), Value::Uint32(b)) => Value::Int128(a.wrapping_shl(b)),
//             (Value::Uint8(a), Value::Uint32(b)) => Value::Uint8(a.wrapping_shl(b)),
//             (Value::Uint16(a), Value::Uint32(b)) => Value::Uint16(a.wrapping_shl(b)),
//             (Value::Uint32(a), Value::Uint32(b)) => Value::Uint32(a.wrapping_shl(b)),
//             (Value::Uint64(a), Value::Uint32(b)) => Value::Uint64(a.wrapping_shl(b)),
//             (Value::Uint128(a), Value::Uint32(b)) => Value::Uint128(a.wrapping_shl(b)),
//             _ => panic!("invalid operation on value"),
//         }
//     }
//     pub fn shr(self, other: Value<'a>) -> Self {
//         match (self, other) {
//             (Value::Int8(a), Value::Uint32(b)) => Value::Int8(a.wrapping_shr(b)),
//             (Value::Int16(a), Value::Uint32(b)) => Value::Int16(a.wrapping_shr(b)),
//             (Value::Int32(a), Value::Uint32(b)) => Value::Int32(a.wrapping_shr(b)),
//             (Value::Int64(a), Value::Uint32(b)) => Value::Int64(a.wrapping_shr(b)),
//             (Value::Int128(a), Value::Uint32(b)) => Value::Int128(a.wrapping_shr(b)),
//             (Value::Uint8(a), Value::Uint32(b)) => Value::Uint8(a.wrapping_shr(b)),
//             (Value::Uint16(a), Value::Uint32(b)) => Value::Uint16(a.wrapping_shr(b)),
//             (Value::Uint32(a), Value::Uint32(b)) => Value::Uint32(a.wrapping_shr(b)),
//             (Value::Uint64(a), Value::Uint32(b)) => Value::Uint64(a.wrapping_shr(b)),
//             (Value::Uint128(a), Value::Uint32(b)) => Value::Uint128(a.wrapping_shr(b)),
//             _ => panic!("invalid operation on value"),
//         }
//     }
//     pub fn bit_or(self, other: Value<'a>) -> Self {
//         match (self, other) {
//             (Value::Int8(a), Value::Int8(b)) => Value::Int8(a | b),
//             (Value::Int16(a), Value::Int16(b)) => Value::Int16(a | b),
//             (Value::Int32(a), Value::Int32(b)) => Value::Int32(a | b),
//             (Value::Int64(a), Value::Int64(b)) => Value::Int64(a | b),
//             (Value::Int128(a), Value::Int128(b)) => Value::Int128(a | b),
//             (Value::Uint8(a), Value::Uint8(b)) => Value::Uint8(a | b),
//             (Value::Uint16(a), Value::Uint16(b)) => Value::Uint16(a | b),
//             (Value::Uint32(a), Value::Uint32(b)) => Value::Uint32(a | b),
//             (Value::Uint64(a), Value::Uint64(b)) => Value::Uint64(a | b),
//             (Value::Uint128(a), Value::Uint128(b)) => Value::Uint128(a | b),
//             _ => panic!("invalid operation on value"),
//         }
//     }
//     pub fn bit_xor(self, other: Value<'a>) -> Self {
//         match (self, other) {
//             (Value::Int8(a), Value::Int8(b)) => Value::Int8(a ^ b),
//             (Value::Int16(a), Value::Int16(b)) => Value::Int16(a ^ b),
//             (Value::Int32(a), Value::Int32(b)) => Value::Int32(a ^ b),
//             (Value::Int64(a), Value::Int64(b)) => Value::Int64(a ^ b),
//             (Value::Int128(a), Value::Int128(b)) => Value::Int128(a ^ b),
//             (Value::Uint8(a), Value::Uint8(b)) => Value::Uint8(a ^ b),
//             (Value::Uint16(a), Value::Uint16(b)) => Value::Uint16(a ^ b),
//             (Value::Uint32(a), Value::Uint32(b)) => Value::Uint32(a ^ b),
//             (Value::Uint64(a), Value::Uint64(b)) => Value::Uint64(a ^ b),
//             (Value::Uint128(a), Value::Uint128(b)) => Value::Uint128(a ^ b),
//             _ => panic!("invalid operation on value"),
//         }
//     }
//     pub fn bit_and(self, other: Value<'a>) -> Self {
//         match (self, other) {
//             (Value::Int8(a), Value::Int8(b)) => Value::Int8(a & b),
//             (Value::Int16(a), Value::Int16(b)) => Value::Int16(a & b),
//             (Value::Int32(a), Value::Int32(b)) => Value::Int32(a & b),
//             (Value::Int64(a), Value::Int64(b)) => Value::Int64(a & b),
//             (Value::Int128(a), Value::Int128(b)) => Value::Int128(a & b),
//             (Value::Uint8(a), Value::Uint8(b)) => Value::Uint8(a & b),
//             (Value::Uint16(a), Value::Uint16(b)) => Value::Uint16(a & b),
//             (Value::Uint32(a), Value::Uint32(b)) => Value::Uint32(a & b),
//             (Value::Uint64(a), Value::Uint64(b)) => Value::Uint64(a & b),
//             (Value::Uint128(a), Value::Uint128(b)) => Value::Uint128(a & b),
//             _ => panic!("invalid operation on value"),
//         }
//     }
//     pub fn compare(&self, other: &Value<'a>) -> Option<Ordering> {
//         match (self, other) {
//             (Value::Bool(a), Value::Bool(b)) => a.partial_cmp(b),
//             (Value::Char(a), Value::Char(b)) => a.partial_cmp(b),
//             (Value::Int8(a), Value::Int8(b)) => a.partial_cmp(b),
//             (Value::Int16(a), Value::Int16(b)) => a.partial_cmp(b),
//             (Value::Int32(a), Value::Int32(b)) => a.partial_cmp(b),
//             (Value::Int64(a), Value::Int64(b)) => a.partial_cmp(b),
//             (Value::Int128(a), Value::Int128(b)) => a.partial_cmp(b),
//             (Value::Uint8(a), Value::Uint8(b)) => a.partial_cmp(b),
//             (Value::Uint16(a), Value::Uint16(b)) => a.partial_cmp(b),
//             (Value::Uint32(a), Value::Uint32(b)) => a.partial_cmp(b),
//             (Value::Uint64(a), Value::Uint64(b)) => a.partial_cmp(b),
//             (Value::Uint128(a), Value::Uint128(b)) => a.partial_cmp(b),
//             (Value::Float32(a), Value::Float32(b)) => a.partial_cmp(b),
//             (Value::Float64(a), Value::Float64(b)) => a.partial_cmp(b),
//             _ => panic!("invalid operation on value"),
//         }
//     }
//
//     pub fn to_usize(&self) -> Option<usize> {
//         match self {
//             Value::Int8(val) => usize::try_from(*val).ok(),
//             Value::Int16(val) => usize::try_from(*val).ok(),
//             Value::Int32(val) => usize::try_from(*val).ok(),
//             Value::Int64(val) => usize::try_from(*val).ok(),
//             Value::Int128(val) => usize::try_from(*val).ok(),
//             Value::Uint8(val) => usize::try_from(*val).ok(),
//             Value::Uint16(val) => usize::try_from(*val).ok(),
//             Value::Uint32(val) => usize::try_from(*val).ok(),
//             Value::Uint64(val) => usize::try_from(*val).ok(),
//             Value::Uint128(val) => usize::try_from(*val).ok(),
//             _ => None,
//         }
//     }
// }
//
// impl<'a> Context<'a> {
//     pub fn from_char(c: char) -> Self {
//         Self {
//             is_lvalue: false,
//             taipe: Type::Char,
//             value: Some(Value::Char(c)),
//         }
//     }
// }
