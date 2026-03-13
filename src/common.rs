use std::cell::Ref;
use std::ops::Deref;
use std::{error::Error, fmt};

use num_bigint::{BigInt, ToBigInt};

// line_start and line_end is inclusive
// col_start and col_end is exclusive
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct LineInfo {
    pub line_start: usize,
    pub line_end: usize,
    pub col_start: usize,
    pub col_end: usize,
}

impl Default for LineInfo {
    fn default() -> Self {
        Self {
            line_start: 1,
            line_end: 1,
            col_start: 1,
            col_end: 1,
        }
    }
}

impl HasLineInfo for LineInfo {
    fn get_line_info(&self) -> LineInfo {
        *self
    }
}

impl LineInfo {
    pub fn from_range(start: &impl HasLineInfo, end: &impl HasLineInfo) -> Self {
        Self {
            line_start: start.get_line_info().line_start,
            line_end: end.get_line_info().line_end,
            col_start: start.get_line_info().col_start,
            col_end: end.get_line_info().col_end,
        }
    }

    // pub fn from_items(items: &[impl HasLineInfo]) -> Self {
    //     assert!(items.len() > 0);
    //     Self::from_range(items.first().unwrap(), items.last().unwrap())
    // }
}

pub trait HasLineInfo {
    fn get_line_info(&self) -> LineInfo;
}

impl<T> HasLineInfo for Vec<T>
where
    T: HasLineInfo,
{
    fn get_line_info(&self) -> LineInfo {
        assert!(self.len() > 0);
        LineInfo::from_range(self.first().unwrap(), self.last().unwrap())
    }
}

impl<T> HasLineInfo for Box<T>
where
    T: HasLineInfo,
{
    fn get_line_info(&self) -> LineInfo {
        self.deref().get_line_info()
    }
}

impl<'a, T> HasLineInfo for Ref<'a, T>
where
    T: HasLineInfo,
{
    fn get_line_info(&self) -> LineInfo {
        self.deref().get_line_info()
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CompileError {
    // FileNotFound(String),
    LexerError {
        file_path: String,
        line_info: LineInfo,
        msg: String,
    },
    ParserError {
        file_path: String,
        line_info: LineInfo,
        msg: String,
    },
    SemError {
        file_path: String,
        line_info: LineInfo,
        msg: String,
    },
    SemWarning {
        file_path: String,
        line_info: LineInfo,
        msg: String,
    },
    SemNote {
        file_path: String,
        line_info: LineInfo,
        msg: String,
    },
    SemCyclic {
        file_path: String,
        line_info: LineInfo,
    },
    Errors(Vec<CompileError>),
}

impl CompileError {
    pub fn chain(self, other: CompileError) -> Self {
        let mut vec = Vec::new();
        if let CompileError::Errors(mut errs) = self {
            vec.append(&mut errs);
        } else {
            vec.push(self.clone());
        }
        vec.push(other);
        CompileError::Errors(vec)
    }
}

impl fmt::Display for CompileError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Use printer::print_error instead")
    }
}

impl Error for CompileError {}

pub type CompileResult<T> = Result<T, CompileError>;

#[derive(Clone, Debug)]
pub struct Int {
    pub num: BigInt,
    max: Option<BigInt>,
    min: Option<BigInt>,
}

impl Int {
    pub fn new() -> Self {
        Self {
            num: BigInt::ZERO,
            max: None,
            min: None,
        }
    }

    // pub fn from_i8(num: i8) -> Self {
    //     Self {
    //         num: num.to_bigint().unwrap(),
    //         max: i8::MAX.to_bigint(),
    //         min: i8::MIN.to_bigint(),
    //     }
    // }
    //
    // pub fn from_i16(num: i16) -> Self {
    //     Self {
    //         num: num.to_bigint().unwrap(),
    //         max: i16::MAX.to_bigint(),
    //         min: i16::MIN.to_bigint(),
    //     }
    // }
    //
    // pub fn from_i32(num: i32) -> Self {
    //     Self {
    //         num: num.to_bigint().unwrap(),
    //         max: i32::MAX.to_bigint(),
    //         min: i32::MIN.to_bigint(),
    //     }
    // }
    //
    // pub fn from_i64(num: i64) -> Self {
    //     Self {
    //         num: num.to_bigint().unwrap(),
    //         max: i64::MAX.to_bigint(),
    //         min: i64::MIN.to_bigint(),
    //     }
    // }

    pub fn parse(buf: &[u8], radix: u32, signed: bool, size: u32) -> Self {
        let max = match size {
            8 => {
                if signed {
                    i8::MAX.to_bigint()
                } else {
                    u8::MAX.to_bigint()
                }
            }
            16 => {
                if signed {
                    i16::MAX.to_bigint()
                } else {
                    u16::MAX.to_bigint()
                }
            }
            32 => {
                if signed {
                    i32::MAX.to_bigint()
                } else {
                    u32::MAX.to_bigint()
                }
            }
            64 => {
                if signed {
                    i64::MAX.to_bigint()
                } else {
                    u64::MAX.to_bigint()
                }
            }
            _ => None,
        };
        let min = match size {
            8 => {
                if signed {
                    i8::MIN.to_bigint()
                } else {
                    u8::MIN.to_bigint()
                }
            }
            16 => {
                if signed {
                    i16::MIN.to_bigint()
                } else {
                    u16::MIN.to_bigint()
                }
            }
            32 => {
                if signed {
                    i32::MIN.to_bigint()
                } else {
                    u32::MIN.to_bigint()
                }
            }
            64 => {
                if signed {
                    i64::MIN.to_bigint()
                } else {
                    u64::MIN.to_bigint()
                }
            }
            _ => None,
        };
        Self::parse_helper(buf, radix, max, min)
    }

    pub fn parse_arbitrary(buf: &[u8], radix: u32) -> Self {
        Self::parse_helper(buf, radix, None, None)
    }

    fn parse_helper(buf: &[u8], radix: u32, max: Option<BigInt>, min: Option<BigInt>) -> Self {
        Self {
            num: BigInt::parse_bytes(buf, radix).unwrap(),
            max,
            min,
        }
    }

    pub fn from_arbitrary(num: u64) -> Self {
        Self::from_helper(num, None, None)
    }

    fn from_helper(num: u64, max: Option<BigInt>, min: Option<BigInt>) -> Self {
        Self {
            num: num.to_bigint().unwrap(),
            max,
            min,
        }
    }
}

impl fmt::Display for Int {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.num)
    }
}

impl Default for Int {
    fn default() -> Self {
        Self::new()
    }
}
