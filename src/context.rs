use std::{cmp::Ordering, fmt};

use indexmap::IndexMap;
use num_bigint::BigInt;

use crate::{common::LineInfo, scope::ScopeId};

// ------------------------------------------------------------
// Context structures (Storing a tree based IR)
// ------------------------------------------------------------

#[derive(Clone, PartialEq, Eq)]
pub struct Param {
    pub taipe: Type,
}

impl fmt::Display for Param {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.taipe)
    }
}

#[derive(Clone)]
pub enum Type {
    /// Imm can be:
    /// - Value::Bool => boolean value
    Bool,
    /// Imm can be:
    /// - Value::Char => char value
    Char,
    /// Imm can be:
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
    /// Imm can be:
    /// - Value::Float32 => float32 value
    Float32,
    /// Imm can be:
    /// - Value::Float64 => float64 value
    Float64,
    /// Imm can be:
    /// - depending on Type::Const.0
    Const(Box<Type>),
    /// Imm can be:
    /// - TODO: object
    Basic(ScopeId),
    /// Imm can be:
    /// - Value::Function => Function value
    Function {
        ret: Box<Type>,
        params: Vec<Param>,
    },
    /// Imm can be:
    /// - TODO: pointer
    Pointer(Box<Type>),
    /// Imm can be:
    /// - Value::Array => array value
    Array {
        count: usize,
        taipe: Box<Type>,
    },
    /// Imm can be:
    /// - Value::Array => array value
    Fat(Box<Type>),
    /// Imm can be:
    /// - Value::Tuple => tuple value
    Tuple(Vec<Type>),
    /// Imm can be:
    /// - Value::Module => module reference
    Module,
    /// Imm can be:
    /// - None => type literal itself: 'typedef'
    /// - Value::Type => type reference
    Typedef,
    /// Imm can be:
    /// - None
    Void,
    /// Imm can be:
    /// - None
    Noreturn,
}

impl Type {
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

impl PartialEq for Type {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Const(l0), Self::Const(r0)) => l0 == r0,
            (Self::Basic(l0), Self::Basic(r0)) => l0 == r0,
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

impl Eq for Type {}

impl fmt::Display for Type {
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
            Type::Basic(scope_id) => write!(f, "{}", scope_id.sym_path),
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
            Type::Pointer(taipe) => write!(f, "*{}", taipe),
            Type::Array { count, taipe } => write!(f, "[{}]{}", count, taipe),
            Type::Fat(taipe) => write!(f, "[]{}", taipe),
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
pub enum Imm {
    /// Represents a boolean value
    Bool(bool),
    /// Represents a char value
    Char(char),
    /// Represents a compiler internal variable length integer
    VarInt(BigInt),
    /// Represents a 8 bit signed integer
    Int8(i8),
    /// Represents a 16 bit signed integer
    Int16(i16),
    /// Represents a 32 bit signed integer
    Int32(i32),
    /// Represents a 64 bit signed integer
    Int64(i64),
    /// Represents a 128 bit signed integer
    Int128(i128),
    /// Represents a 8 bit unsigned integer
    Uint8(u8),
    /// Represents a 16 bit unsigned integer
    Uint16(u16),
    /// Represents a 32 bit unsigned integer
    Uint32(u32),
    /// Represents a 64 bit unsigned integer
    Uint64(u64),
    /// Represents a 128 bit unsigned integer
    Uint128(u128),
    /// Represents a 32 bit floating point
    Float32(f32),
    /// Represents a 64 bit floating point
    Float64(f64),
    /// Represents a typedef
    Type(Type),
    /// Represents a module
    Module(ScopeId),
    /// Represents a null pointer
    Null,
    /// Represents nothing (used in void context)
    Void,
}

impl Imm {
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
    pub fn add(self, other: Imm) -> Option<Self> {
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
    pub fn sub(self, other: Imm) -> Option<Self> {
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
    pub fn mul(self, other: Imm) -> Option<Self> {
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
    pub fn div(self, other: Imm) -> Option<Self> {
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
    pub fn modulo(self, other: Imm) -> Option<Self> {
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
    pub fn shl(self, other: Imm) -> Self {
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
    pub fn shr(self, other: Imm) -> Self {
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
    pub fn bit_or(self, other: Imm) -> Self {
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
    pub fn bit_xor(self, other: Imm) -> Self {
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
    pub fn bit_and(self, other: Imm) -> Self {
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
    pub fn compare(&self, other: &Imm) -> Option<Ordering> {
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

impl fmt::Display for Imm {
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
            Imm::Module(scope_id) => write!(f, "module {}", scope_id),
            Imm::Null => write!(f, "null"),
            Imm::Void => write!(f, "void"),
        }
    }
}

#[derive(Clone)]
pub enum Value {
    // Immediate or partially immediate ones 
    /// Represents an immediate value
    Imm(Imm),
    /// Array of values
    Array(Vec<Value>),
    /// Tuple of values
    Tuple(Vec<Value>),

    // Instructions
    // Get things
    /// type: type of global
    GetGlobal {
        line_info: LineInfo,
        scope_id: ScopeId,
    },
    /// type: type of local
    GetLocal {
        line_info: LineInfo,
        scope_id: ScopeId,
    },
    /// type: type of field
    GetField {
        line_info: LineInfo,
        lhs: Box<Context>,
        scope_id: ScopeId,
    },
    // Set things
    /// type: void 
    SetGlobal {
        line_info: LineInfo,
        scope_id: ScopeId,
        rhs: Box<Context>,
    },
    /// type: void 
    SetLocal {
        line_info: LineInfo,
        scope_id: ScopeId,
        rhs: Box<Context>,
    },
    /// type: void 
    SetField {
        line_info: LineInfo,
        lhs: Box<Context>,
        scope_id: ScopeId,
        rhs: Box<Context>,
    },
    
    // Unary Instructions
    Negate {
        line_info: LineInfo,
        ctx: Box<Context>,
    },
    FlipBits {
        line_info: LineInfo,
        ctx: Box<Context>,
    },
    Deref {
        line_info: LineInfo,
        ctx: Box<Context>,
    },
    AddrOf {
        line_info: LineInfo,
        ctx: Box<Context>,
    },
    Not {
        line_info: LineInfo,
        ctx: Box<Context>,
    },

    // Binary Instructions
    Add {
        line_info: LineInfo,
        lhs: Box<Context>,
        rhs: Box<Context>,
    },
    Sub {
        line_info: LineInfo,
        lhs: Box<Context>,
        rhs: Box<Context>,
    },
    Mul {
        line_info: LineInfo,
        lhs: Box<Context>,
        rhs: Box<Context>,
    },
    Div {
        line_info: LineInfo,
        lhs: Box<Context>,
        rhs: Box<Context>,
    },
    Rem {
        line_info: LineInfo,
        lhs: Box<Context>,
        rhs: Box<Context>,
    },
    Shl {
        line_info: LineInfo,
        lhs: Box<Context>,
        rhs: Box<Context>,
    },
    Shr {
        line_info: LineInfo,
        lhs: Box<Context>,
        rhs: Box<Context>,
    },
    BitAnd {
        line_info: LineInfo,
        lhs: Box<Context>,
        rhs: Box<Context>,
    },
    BitXor {
        line_info: LineInfo,
        lhs: Box<Context>,
        rhs: Box<Context>,
    },
    BitOr {
        line_info: LineInfo,
        lhs: Box<Context>,
        rhs: Box<Context>,
    },
    Lt {
        line_info: LineInfo,
        lhs: Box<Context>,
        rhs: Box<Context>,
    },
    Le {
        line_info: LineInfo,
        lhs: Box<Context>,
        rhs: Box<Context>,
    },
    Eq {
        line_info: LineInfo,
        lhs: Box<Context>,
        rhs: Box<Context>,
    },
    Ne {
        line_info: LineInfo,
        lhs: Box<Context>,
        rhs: Box<Context>,
    },
    Ge {
        line_info: LineInfo,
        lhs: Box<Context>,
        rhs: Box<Context>,
    },
    Gt {
        line_info: LineInfo,
        lhs: Box<Context>,
        rhs: Box<Context>,
    },
    LogicAnd {
        line_info: LineInfo,
        lhs: Box<Context>,
        rhs: Box<Context>,
    },
    LogicOr {
        line_info: LineInfo,
        lhs: Box<Context>,
        rhs: Box<Context>,
    },

    // Postfix op instructions
    Index {
        line_info: LineInfo,
        lhs: Box<Context>,
        index: Box<Context>,
    },
    DirectCall {
        line_info: LineInfo,
        fun_scope_id: ScopeId,
        args: IndexMap<String, Context>,
    },
    IndirectCall {
        line_info: LineInfo,
        lhs: Box<Context>,
        args: IndexMap<String, Context>,
    },

    // Statement instructions
    /// type: type of both branch
    IfElse {
        line_info: LineInfo,
        cond: Box<Context>,
        then_ctx: Box<Context>,
        else_ctx: Box<Context>,
    },
    /// type: void
    While {
        line_info: LineInfo,
        cond: Box<Context>,
        body_ctx: Box<Context>,
    },
    /// type: type of last stmt
    Block(Vec<Context>),
    /// type: noreturn
    Ret(Box<Context>),
    /// type: noreturn
    RetVoid,
    /// type: void
    Eval(Box<Context>),
    // Cast instructions
    // * from: uX     to: iX
    // * from: iX     to: uX
    // * from: fX     to: iX
    // * from: fX     to: uX
    // * from: iX     to: fX
    // * from: uX     to: fX
    // * from: [N]T   to: []T
    Cast(Box<Context>),
}

impl Value {
    pub fn from_nil() -> Self {
        Self::Imm(Imm::Null)
    }
    pub fn from_bool(b: bool) -> Self {
        Self::Imm(Imm::Bool(b))
    }
    pub fn from_module(scope_id: ScopeId) -> Self {
        Self::Imm(Imm::Module(scope_id))
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
pub struct Context {
    pub is_lvalue: bool,
    pub taipe: Type,
    pub value: Value,
}

impl Context {
    // Helper functions
    pub fn add_const(self) -> Self {
        Context {
            is_lvalue: self.is_lvalue,
            taipe: Type::Const(Box::new(self.taipe)),
            value: self.value,
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
    pub fn from_type(taipe: Type) -> Self {
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
            value: Value::Imm(Imm::Void),
        }
    }
    pub fn from_noreturn() -> Self {
        Self {
            is_lvalue: false,
            taipe: Type::Noreturn,
            value: Value::Imm(Imm::Null),
        }
    }
}

impl fmt::Display for Context {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.taipe)
    }
}
