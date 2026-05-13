use std::{cell::RefCell, cmp::Ordering, fmt, rc::Rc};

use indexmap::IndexMap;

use crate::{
    common::{Int, LineInfo},
    scope,
};

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
    pub fn is_signed_integer(&self) -> bool {
        match self {
            Type::VarInt | Type::Int8 | Type::Int16 | Type::Int32 | Type::Int64 | Type::Int128 => true,
            Type::Const(taipe) => taipe.is_signed_integer(),
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
    pub fn is_array(&self) -> bool {
        match self {
            Type::Const(taipe) => taipe.is_array(),
            Type::Array { count: _, taipe: _ } => true,
            _ => false,
        }
    }
    pub fn is_fat_ptr(&self) -> bool {
        match self {
            Type::Const(taipe) => taipe.is_fat_ptr(),
            Type::Fat(_) => true,
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

impl<'a> fmt::Display for Type<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Type::Bool => write!(f, "__bool"),
            Type::Char => write!(f, "__char"),
            Type::VarInt => write!(f, "{}", "{integer}"),
            Type::Int8 => write!(f, "__i8"),
            Type::Int16 => write!(f, "__i16"),
            Type::Int32 => write!(f, "__i32"),
            Type::Int64 => write!(f, "__i64"),
            Type::Int128 => write!(f, "__i128"),
            Type::Uint8 => write!(f, "__u8"),
            Type::Uint16 => write!(f, "__u16"),
            Type::Uint32 => write!(f, "__u32"),
            Type::Uint64 => write!(f, "__u64"),
            Type::Uint128 => write!(f, "__u128"),
            Type::Float32 => write!(f, "__f32"),
            Type::Float64 => write!(f, "__f64"),
            Type::Const(taipe) => write!(f, "const {}", taipe),
            Type::Basic(scope) => write!(f, "{}", scope.borrow().sym_path),
            Type::Function { ret, params } => write!(
                f,
                "fun ({}) -> {}",
                params
                    .iter()
                    .map(|param| param.to_string())
                    .collect::<Vec<_>>()
                    .join(", "),
                ret.to_string()
            ),
            Type::Pointer(taipe) => write!(f, "*{}", taipe.to_string()),
            Type::Array { count, taipe } => write!(f, "[{}]{}", count, taipe.to_string()),
            Type::Fat(taipe) => write!(f, "[]{}", taipe.to_string()),
            Type::Tuple(items) => write!(
                f,
                "({})",
                items.iter().map(|item| item.to_string()).collect::<Vec<_>>().join(", ")
            ),
            Type::Module => write!(f, "module"),
            Type::Typedef => write!(f, "typedef"),
            Type::Void => write!(f, "void"),
            Type::Noreturn => write!(f, "noreturn"),
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
    pub fn add(self, other: Imm<'a>) -> Option<Self> {
        match (self, other) {
            (Imm::Int8(a), Imm::Int8(b)) => a.checked_add(b).map(|value| Imm::Int8(value)),
            (Imm::Int16(a), Imm::Int16(b)) => a.checked_add(b).map(|value| Imm::Int16(value)),
            (Imm::Int32(a), Imm::Int32(b)) => a.checked_add(b).map(|value| Imm::Int32(value)),
            (Imm::Int64(a), Imm::Int64(b)) => a.checked_add(b).map(|value| Imm::Int64(value)),
            (Imm::Int128(a), Imm::Int128(b)) => a.checked_add(b).map(|value| Imm::Int128(value)),
            (Imm::Uint8(a), Imm::Uint8(b)) => a.checked_add(b).map(|value| Imm::Uint8(value)),
            (Imm::Uint16(a), Imm::Uint16(b)) => a.checked_add(b).map(|value| Imm::Uint16(value)),
            (Imm::Uint32(a), Imm::Uint32(b)) => a.checked_add(b).map(|value| Imm::Uint32(value)),
            (Imm::Uint64(a), Imm::Uint64(b)) => a.checked_add(b).map(|value| Imm::Uint64(value)),
            (Imm::Uint128(a), Imm::Uint128(b)) => a.checked_add(b).map(|value| Imm::Uint128(value)),
            (Imm::Float32(a), Imm::Float32(b)) => Some(Imm::Float32(a + b)),
            (Imm::Float64(a), Imm::Float64(b)) => Some(Imm::Float64(a + b)),
            _ => panic!("invalid operation on imm"),
        }
    }
    pub fn sub(self, other: Imm<'a>) -> Option<Self> {
        match (self, other) {
            (Imm::Int8(a), Imm::Int8(b)) => a.checked_sub(b).map(|value| Imm::Int8(value)),
            (Imm::Int16(a), Imm::Int16(b)) => a.checked_sub(b).map(|value| Imm::Int16(value)),
            (Imm::Int32(a), Imm::Int32(b)) => a.checked_sub(b).map(|value| Imm::Int32(value)),
            (Imm::Int64(a), Imm::Int64(b)) => a.checked_sub(b).map(|value| Imm::Int64(value)),
            (Imm::Int128(a), Imm::Int128(b)) => a.checked_sub(b).map(|value| Imm::Int128(value)),
            (Imm::Uint8(a), Imm::Uint8(b)) => a.checked_sub(b).map(|value| Imm::Uint8(value)),
            (Imm::Uint16(a), Imm::Uint16(b)) => a.checked_sub(b).map(|value| Imm::Uint16(value)),
            (Imm::Uint32(a), Imm::Uint32(b)) => a.checked_sub(b).map(|value| Imm::Uint32(value)),
            (Imm::Uint64(a), Imm::Uint64(b)) => a.checked_sub(b).map(|value| Imm::Uint64(value)),
            (Imm::Uint128(a), Imm::Uint128(b)) => a.checked_sub(b).map(|value| Imm::Uint128(value)),
            (Imm::Float32(a), Imm::Float32(b)) => Some(Imm::Float32(a - b)),
            (Imm::Float64(a), Imm::Float64(b)) => Some(Imm::Float64(a - b)),
            _ => panic!("invalid operation on imm"),
        }
    }
    pub fn mul(self, other: Imm<'a>) -> Option<Self> {
        match (self, other) {
            (Imm::Int8(a), Imm::Int8(b)) => a.checked_mul(b).map(|value| Imm::Int8(value)),
            (Imm::Int16(a), Imm::Int16(b)) => a.checked_mul(b).map(|value| Imm::Int16(value)),
            (Imm::Int32(a), Imm::Int32(b)) => a.checked_mul(b).map(|value| Imm::Int32(value)),
            (Imm::Int64(a), Imm::Int64(b)) => a.checked_mul(b).map(|value| Imm::Int64(value)),
            (Imm::Int128(a), Imm::Int128(b)) => a.checked_mul(b).map(|value| Imm::Int128(value)),
            (Imm::Uint8(a), Imm::Uint8(b)) => a.checked_mul(b).map(|value| Imm::Uint8(value)),
            (Imm::Uint16(a), Imm::Uint16(b)) => a.checked_mul(b).map(|value| Imm::Uint16(value)),
            (Imm::Uint32(a), Imm::Uint32(b)) => a.checked_mul(b).map(|value| Imm::Uint32(value)),
            (Imm::Uint64(a), Imm::Uint64(b)) => a.checked_mul(b).map(|value| Imm::Uint64(value)),
            (Imm::Uint128(a), Imm::Uint128(b)) => a.checked_mul(b).map(|value| Imm::Uint128(value)),
            (Imm::Float32(a), Imm::Float32(b)) => Some(Imm::Float32(a * b)),
            (Imm::Float64(a), Imm::Float64(b)) => Some(Imm::Float64(a * b)),
            _ => panic!("invalid operation on imm"),
        }
    }
    pub fn div(self, other: Imm<'a>) -> Option<Self> {
        match (self, other) {
            (Imm::Int8(a), Imm::Int8(b)) => a.checked_div(b).map(|value| Imm::Int8(value)),
            (Imm::Int16(a), Imm::Int16(b)) => a.checked_div(b).map(|value| Imm::Int16(value)),
            (Imm::Int32(a), Imm::Int32(b)) => a.checked_div(b).map(|value| Imm::Int32(value)),
            (Imm::Int64(a), Imm::Int64(b)) => a.checked_div(b).map(|value| Imm::Int64(value)),
            (Imm::Int128(a), Imm::Int128(b)) => a.checked_div(b).map(|value| Imm::Int128(value)),
            (Imm::Uint8(a), Imm::Uint8(b)) => a.checked_div(b).map(|value| Imm::Uint8(value)),
            (Imm::Uint16(a), Imm::Uint16(b)) => a.checked_div(b).map(|value| Imm::Uint16(value)),
            (Imm::Uint32(a), Imm::Uint32(b)) => a.checked_div(b).map(|value| Imm::Uint32(value)),
            (Imm::Uint64(a), Imm::Uint64(b)) => a.checked_div(b).map(|value| Imm::Uint64(value)),
            (Imm::Uint128(a), Imm::Uint128(b)) => a.checked_div(b).map(|value| Imm::Uint128(value)),
            (Imm::Float32(a), Imm::Float32(b)) => Some(Imm::Float32(a / b)),
            (Imm::Float64(a), Imm::Float64(b)) => Some(Imm::Float64(a / b)),
            _ => panic!("invalid operation on imm"),
        }
    }
    pub fn modulo(self, other: Imm<'a>) -> Option<Self> {
        match (self, other) {
            (Imm::Int8(a), Imm::Int8(b)) => a.checked_rem(b).map(|value| Imm::Int8(value)),
            (Imm::Int16(a), Imm::Int16(b)) => a.checked_rem(b).map(|value| Imm::Int16(value)),
            (Imm::Int32(a), Imm::Int32(b)) => a.checked_rem(b).map(|value| Imm::Int32(value)),
            (Imm::Int64(a), Imm::Int64(b)) => a.checked_rem(b).map(|value| Imm::Int64(value)),
            (Imm::Int128(a), Imm::Int128(b)) => a.checked_rem(b).map(|value| Imm::Int128(value)),
            (Imm::Uint8(a), Imm::Uint8(b)) => a.checked_rem(b).map(|value| Imm::Uint8(value)),
            (Imm::Uint16(a), Imm::Uint16(b)) => a.checked_rem(b).map(|value| Imm::Uint16(value)),
            (Imm::Uint32(a), Imm::Uint32(b)) => a.checked_rem(b).map(|value| Imm::Uint32(value)),
            (Imm::Uint64(a), Imm::Uint64(b)) => a.checked_rem(b).map(|value| Imm::Uint64(value)),
            (Imm::Uint128(a), Imm::Uint128(b)) => a.checked_rem(b).map(|value| Imm::Uint128(value)),
            _ => panic!("invalid operation on imm"),
        }
    }
    pub fn shl(self, other: Imm<'a>) -> Self {
        match (self, other) {
            (Imm::Int8(a), Imm::Uint32(b)) => Imm::Int8(a.wrapping_shl(b)),
            (Imm::Int16(a), Imm::Uint32(b)) => Imm::Int16(a.wrapping_shl(b)),
            (Imm::Int32(a), Imm::Uint32(b)) => Imm::Int32(a.wrapping_shl(b)),
            (Imm::Int64(a), Imm::Uint32(b)) => Imm::Int64(a.wrapping_shl(b)),
            (Imm::Int128(a), Imm::Uint32(b)) => Imm::Int128(a.wrapping_shl(b)),
            (Imm::Uint8(a), Imm::Uint32(b)) => Imm::Uint8(a.wrapping_shl(b)),
            (Imm::Uint16(a), Imm::Uint32(b)) => Imm::Uint16(a.wrapping_shl(b)),
            (Imm::Uint32(a), Imm::Uint32(b)) => Imm::Uint32(a.wrapping_shl(b)),
            (Imm::Uint64(a), Imm::Uint32(b)) => Imm::Uint64(a.wrapping_shl(b)),
            (Imm::Uint128(a), Imm::Uint32(b)) => Imm::Uint128(a.wrapping_shl(b)),
            _ => panic!("invalid operation on imm"),
        }
    }
    pub fn shr(self, other: Imm<'a>) -> Self {
        match (self, other) {
            (Imm::Int8(a), Imm::Uint32(b)) => Imm::Int8(a.wrapping_shr(b)),
            (Imm::Int16(a), Imm::Uint32(b)) => Imm::Int16(a.wrapping_shr(b)),
            (Imm::Int32(a), Imm::Uint32(b)) => Imm::Int32(a.wrapping_shr(b)),
            (Imm::Int64(a), Imm::Uint32(b)) => Imm::Int64(a.wrapping_shr(b)),
            (Imm::Int128(a), Imm::Uint32(b)) => Imm::Int128(a.wrapping_shr(b)),
            (Imm::Uint8(a), Imm::Uint32(b)) => Imm::Uint8(a.wrapping_shr(b)),
            (Imm::Uint16(a), Imm::Uint32(b)) => Imm::Uint16(a.wrapping_shr(b)),
            (Imm::Uint32(a), Imm::Uint32(b)) => Imm::Uint32(a.wrapping_shr(b)),
            (Imm::Uint64(a), Imm::Uint32(b)) => Imm::Uint64(a.wrapping_shr(b)),
            (Imm::Uint128(a), Imm::Uint32(b)) => Imm::Uint128(a.wrapping_shr(b)),
            _ => panic!("invalid operation on imm"),
        }
    }
    pub fn bit_or(self, other: Imm<'a>) -> Self {
        match (self, other) {
            (Imm::Int8(a), Imm::Int8(b)) => Imm::Int8(a | b),
            (Imm::Int16(a), Imm::Int16(b)) => Imm::Int16(a | b),
            (Imm::Int32(a), Imm::Int32(b)) => Imm::Int32(a | b),
            (Imm::Int64(a), Imm::Int64(b)) => Imm::Int64(a | b),
            (Imm::Int128(a), Imm::Int128(b)) => Imm::Int128(a | b),
            (Imm::Uint8(a), Imm::Uint8(b)) => Imm::Uint8(a | b),
            (Imm::Uint16(a), Imm::Uint16(b)) => Imm::Uint16(a | b),
            (Imm::Uint32(a), Imm::Uint32(b)) => Imm::Uint32(a | b),
            (Imm::Uint64(a), Imm::Uint64(b)) => Imm::Uint64(a | b),
            (Imm::Uint128(a), Imm::Uint128(b)) => Imm::Uint128(a | b),
            _ => panic!("invalid operation on imm"),
        }
    }
    pub fn bit_xor(self, other: Imm<'a>) -> Self {
        match (self, other) {
            (Imm::Int8(a), Imm::Int8(b)) => Imm::Int8(a ^ b),
            (Imm::Int16(a), Imm::Int16(b)) => Imm::Int16(a ^ b),
            (Imm::Int32(a), Imm::Int32(b)) => Imm::Int32(a ^ b),
            (Imm::Int64(a), Imm::Int64(b)) => Imm::Int64(a ^ b),
            (Imm::Int128(a), Imm::Int128(b)) => Imm::Int128(a ^ b),
            (Imm::Uint8(a), Imm::Uint8(b)) => Imm::Uint8(a ^ b),
            (Imm::Uint16(a), Imm::Uint16(b)) => Imm::Uint16(a ^ b),
            (Imm::Uint32(a), Imm::Uint32(b)) => Imm::Uint32(a ^ b),
            (Imm::Uint64(a), Imm::Uint64(b)) => Imm::Uint64(a ^ b),
            (Imm::Uint128(a), Imm::Uint128(b)) => Imm::Uint128(a ^ b),
            _ => panic!("invalid operation on imm"),
        }
    }
    pub fn bit_and(self, other: Imm<'a>) -> Self {
        match (self, other) {
            (Imm::Int8(a), Imm::Int8(b)) => Imm::Int8(a & b),
            (Imm::Int16(a), Imm::Int16(b)) => Imm::Int16(a & b),
            (Imm::Int32(a), Imm::Int32(b)) => Imm::Int32(a & b),
            (Imm::Int64(a), Imm::Int64(b)) => Imm::Int64(a & b),
            (Imm::Int128(a), Imm::Int128(b)) => Imm::Int128(a & b),
            (Imm::Uint8(a), Imm::Uint8(b)) => Imm::Uint8(a & b),
            (Imm::Uint16(a), Imm::Uint16(b)) => Imm::Uint16(a & b),
            (Imm::Uint32(a), Imm::Uint32(b)) => Imm::Uint32(a & b),
            (Imm::Uint64(a), Imm::Uint64(b)) => Imm::Uint64(a & b),
            (Imm::Uint128(a), Imm::Uint128(b)) => Imm::Uint128(a & b),
            _ => panic!("invalid operation on imm"),
        }
    }
    pub fn compare(&self, other: &Imm<'a>) -> Option<Ordering> {
        match (self, other) {
            (Imm::Bool(a), Imm::Bool(b)) => a.partial_cmp(b),
            (Imm::Char(a), Imm::Char(b)) => a.partial_cmp(b),
            (Imm::Int8(a), Imm::Int8(b)) => a.partial_cmp(b),
            (Imm::Int16(a), Imm::Int16(b)) => a.partial_cmp(b),
            (Imm::Int32(a), Imm::Int32(b)) => a.partial_cmp(b),
            (Imm::Int64(a), Imm::Int64(b)) => a.partial_cmp(b),
            (Imm::Int128(a), Imm::Int128(b)) => a.partial_cmp(b),
            (Imm::Uint8(a), Imm::Uint8(b)) => a.partial_cmp(b),
            (Imm::Uint16(a), Imm::Uint16(b)) => a.partial_cmp(b),
            (Imm::Uint32(a), Imm::Uint32(b)) => a.partial_cmp(b),
            (Imm::Uint64(a), Imm::Uint64(b)) => a.partial_cmp(b),
            (Imm::Uint128(a), Imm::Uint128(b)) => a.partial_cmp(b),
            (Imm::Float32(a), Imm::Float32(b)) => a.partial_cmp(b),
            (Imm::Float64(a), Imm::Float64(b)) => a.partial_cmp(b),
            _ => panic!("invalid operation on imm"),
        }
    }
}

impl<'a> fmt::Display for Imm<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Imm::Bool(val) => write!(f, "{}", val),
            Imm::Char(val) => write!(f, "{}", val),
            Imm::VarInt(int) => write!(f, "{}", int),
            Imm::Int8(val) => write!(f, "{}", val),
            Imm::Int16(val) => write!(f, "{}", val),
            Imm::Int32(val) => write!(f, "{}", val),
            Imm::Int64(val) => write!(f, "{}", val),
            Imm::Int128(val) => write!(f, "{}", val),
            Imm::Uint8(val) => write!(f, "{}", val),
            Imm::Uint16(val) => write!(f, "{}", val),
            Imm::Uint32(val) => write!(f, "{}", val),
            Imm::Uint64(val) => write!(f, "{}", val),
            Imm::Uint128(val) => write!(f, "{}", val),
            Imm::Float32(val) => write!(f, "{}", val),
            Imm::Float64(val) => write!(f, "{}", val),
            Imm::Type(t) => write!(f, "{}", t),
            Imm::Nil => write!(f, "nil"),
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
    Negate {
        line_info: LineInfo,
        ctx: Box<Context<'a>>,
    },
    FlipBits {
        line_info: LineInfo,
        ctx: Box<Context<'a>>,
    },
    Deref {
        line_info: LineInfo,
        ctx: Box<Context<'a>>,
    },
    AddrOf {
        line_info: LineInfo,
        ctx: Box<Context<'a>>,
    },
    Not {
        line_info: LineInfo,
        ctx: Box<Context<'a>>,
    },
    // Binary Instructions
    Add {
        line_info: LineInfo,
        lhs: Box<Context<'a>>,
        rhs: Box<Context<'a>>,
    },
    Sub {
        line_info: LineInfo,
        lhs: Box<Context<'a>>,
        rhs: Box<Context<'a>>,
    },
    Mul {
        line_info: LineInfo,
        lhs: Box<Context<'a>>,
        rhs: Box<Context<'a>>,
    },
    Div {
        line_info: LineInfo,
        lhs: Box<Context<'a>>,
        rhs: Box<Context<'a>>,
    },
    Rem {
        line_info: LineInfo,
        lhs: Box<Context<'a>>,
        rhs: Box<Context<'a>>,
    },
    Shl {
        line_info: LineInfo,
        lhs: Box<Context<'a>>,
        rhs: Box<Context<'a>>,
    },
    Shr {
        line_info: LineInfo,
        lhs: Box<Context<'a>>,
        rhs: Box<Context<'a>>,
    },
    BitAnd {
        line_info: LineInfo,
        lhs: Box<Context<'a>>,
        rhs: Box<Context<'a>>,
    },
    BitXor {
        line_info: LineInfo,
        lhs: Box<Context<'a>>,
        rhs: Box<Context<'a>>,
    },
    BitOr {
        line_info: LineInfo,
        lhs: Box<Context<'a>>,
        rhs: Box<Context<'a>>,
    },
    Lt {
        line_info: LineInfo,
        lhs: Box<Context<'a>>,
        rhs: Box<Context<'a>>,
    },
    Le {
        line_info: LineInfo,
        lhs: Box<Context<'a>>,
        rhs: Box<Context<'a>>,
    },
    Eq {
        line_info: LineInfo,
        lhs: Box<Context<'a>>,
        rhs: Box<Context<'a>>,
    },
    Ne {
        line_info: LineInfo,
        lhs: Box<Context<'a>>,
        rhs: Box<Context<'a>>,
    },
    Ge {
        line_info: LineInfo,
        lhs: Box<Context<'a>>,
        rhs: Box<Context<'a>>,
    },
    Gt {
        line_info: LineInfo,
        lhs: Box<Context<'a>>,
        rhs: Box<Context<'a>>,
    },
    LogicAnd {
        line_info: LineInfo,
        lhs: Box<Context<'a>>,
        rhs: Box<Context<'a>>,
    },
    LogicOr {
        line_info: LineInfo,
        lhs: Box<Context<'a>>,
        rhs: Box<Context<'a>>,
    },
    // Postfix op instructions
    Index {
        line_info: LineInfo,
        lhs: Box<Context<'a>>,
        index: Box<Context<'a>>,
    },
    Call {
        line_info: LineInfo,
        fun_scope: Rc<RefCell<scope::Scope<'a>>>,
        args: IndexMap<String, Context<'a>>,
    },
    // Statement instructions
    Assign(Vec<Context<'a>>, Vec<Context<'a>>),
    IfElse {
        line_info: LineInfo,
        cond: Box<Context<'a>>,
        then_ctx: Box<Context<'a>>,
        else_ctx: Box<Context<'a>>,
    },
    If {
        line_info: LineInfo,
        cond: Box<Context<'a>>,
        then_ctx: Box<Context<'a>>,
    },
    While {
        line_info: LineInfo,
        cond: Box<Context<'a>>,
        body_ctx: Box<Context<'a>>,
    },
    Block(Vec<Context<'a>>),
    Ret(Box<Context<'a>>),
    RetVoid,
    Eval(Box<Context<'a>>),
    // Cast instructions
    // * from: uX     to: iX
    // * from: iX     to: uX
    // * from: fX     to: iX
    // * from: fX     to: uX
    // * from: iX     to: fX
    // * from: uX     to: fX
    // * from: [N]T   to: []T
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
    // Helper functions
    pub fn add_const(self) -> Self {
        Context {
            is_lvalue: self.is_lvalue,
            taipe: Type::Const(Box::new(self.taipe)),
            value: self.value,
        }
    }

    // Construction functions
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
    pub fn from_char(c: char) -> Self {
        Self {
            is_lvalue: false,
            taipe: Type::Char,
            value: Value::Imm(Imm::Char(c)),
        }
    }
    pub fn from_i8(value: i8) -> Self {
        Self {
            is_lvalue: false,
            taipe: Type::Int8,
            value: Value::Imm(Imm::Int8(value)),
        }
    }
    pub fn from_i16(value: i16) -> Self {
        Self {
            is_lvalue: false,
            taipe: Type::Int16,
            value: Value::Imm(Imm::Int16(value)),
        }
    }
    pub fn from_i32(value: i32) -> Self {
        Self {
            is_lvalue: false,
            taipe: Type::Int32,
            value: Value::Imm(Imm::Int32(value)),
        }
    }
    pub fn from_i64(value: i64) -> Self {
        Self {
            is_lvalue: false,
            taipe: Type::Int64,
            value: Value::Imm(Imm::Int64(value)),
        }
    }
    pub fn from_i128(value: i128) -> Self {
        Self {
            is_lvalue: false,
            taipe: Type::Int128,
            value: Value::Imm(Imm::Int128(value)),
        }
    }
    pub fn from_u8(value: u8) -> Self {
        Self {
            is_lvalue: false,
            taipe: Type::Uint8,
            value: Value::Imm(Imm::Uint8(value)),
        }
    }
    pub fn from_u16(value: u16) -> Self {
        Self {
            is_lvalue: false,
            taipe: Type::Uint16,
            value: Value::Imm(Imm::Uint16(value)),
        }
    }
    pub fn from_u32(value: u32) -> Self {
        Self {
            is_lvalue: false,
            taipe: Type::Uint32,
            value: Value::Imm(Imm::Uint32(value)),
        }
    }
    pub fn from_u64(value: u64) -> Self {
        Self {
            is_lvalue: false,
            taipe: Type::Uint64,
            value: Value::Imm(Imm::Uint64(value)),
        }
    }
    pub fn from_u128(value: u128) -> Self {
        Self {
            is_lvalue: false,
            taipe: Type::Uint128,
            value: Value::Imm(Imm::Uint128(value)),
        }
    }
    pub fn from_f32(value: f32) -> Self {
        Self {
            is_lvalue: false,
            taipe: Type::Float32,
            value: Value::Imm(Imm::Float32(value)),
        }
    }
    pub fn from_f64(value: f64) -> Self {
        Self {
            is_lvalue: false,
            taipe: Type::Float64,
            value: Value::Imm(Imm::Float64(value)),
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

impl<'a> fmt::Display for Context<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.taipe)
    }
}
