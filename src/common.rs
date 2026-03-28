use std::cell::Ref;
use std::collections::{BTreeSet, HashSet};
use std::ops::Deref;
use std::{error::Error, fmt};

use num_bigint::{BigInt, ToBigInt};
use num_traits::ToPrimitive;

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

impl<T> HasLineInfo for &[T]
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
    SemHelp {
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

#[derive(Clone, Copy, Debug)]
pub struct Layout {
    pub size: usize,
    pub alignment: usize,
}

impl Default for Layout {
    fn default() -> Self {
        Self {
            size: 1,
            alignment: 1,
        }
    }
}

#[derive(Clone, Debug)]
pub struct Int {
    pub num: BigInt,
}

impl Int {
    pub fn new() -> Self {
        Self {
            num: BigInt::ZERO,
        }
    }

    pub fn parse(buf: &[u8], radix: u32) -> Self {
        Self::parse_helper(buf, radix)
    }

    pub fn parse_arbitrary(buf: &[u8], radix: u32) -> Self {
        Self::parse_helper(buf, radix)
    }

    fn parse_helper(buf: &[u8], radix: u32) -> Self {
        Self {
            num: BigInt::parse_bytes(buf, radix).unwrap(),
        }
    }

    pub fn from_arbitrary(num: u64) -> Self {
        Self::from_helper(num)
    }

    fn from_helper(num: u64) -> Self {
        Self {
            num: num.to_bigint().unwrap(),
        }
    }

    pub fn to_usize(&self) -> Option<usize> {
        self.num.to_usize()
    }

    pub fn to_f32(&self) -> Option<f32> {
        self.num.to_f32()
    }

    pub fn to_f64(&self) -> Option<f64> {
        self.num.to_f64()
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

pub struct Settings {
    // Register size of the architecture in bytes
    pub register_size: usize,
    // Pointer size of the architecture in bytes
    pub pointer_size:  usize,
}

/// Optimized Levenshtein distance function (O(min(m, n)) space)
pub fn levenshtein(s1_str: &str, s2_str: &str) -> usize {
    let s1 = s1_str.chars().collect::<Vec<_>>();
    let s2 = s2_str.chars().collect::<Vec<_>>();
    let m = s1.len();
    let n = s2.len();
    if m == 0 {
        return n;
    }
    if n == 0 {
        return m;
    }
    // Always use the smaller string for the row
    if m < n {
        return levenshtein(s2_str, s1_str);
    }
    // Procedure
    let mut prev = vec![0; n + 1];
    let mut curr = vec![0; n + 1];
    for j in 0..=n {
        prev[j] = j;
    }
    for i in 1..=m {
        curr[0] = i;
        for j in 1..=n {
            if s1[i - 1] == s2[j - 1] {
                curr[j] = prev[j - 1];
            } else {
                curr[j] = 1 + prev[j].min(curr[j - 1]).min(prev[j - 1]);
            }
        }
        std::mem::swap(&mut prev, &mut curr);
    }
    prev[n]
}

pub fn fuzzy_search_best(
    query: &str,
    candidates: &HashSet<String>,
    max_results: Option<usize>,
) -> BTreeSet<String> {
    let max_results = max_results.unwrap_or(6);
    let mut min_distance = usize::MAX;
    let mut results = BTreeSet::new();
    for candidate in candidates {
        // Ignore internal names
        if candidate.ends_with("$") {
            continue;
        }
        // Calaculate the levenshtein distance
        let distance = levenshtein(query, candidate);
        if distance < min_distance {
            min_distance = distance;
            results.clear();
            results.insert(candidate.clone());
        } else if distance == min_distance {
            results.insert(candidate.clone());
        }
        // Check whether we reach max results or not
        if results.len() >= max_results && distance == min_distance {
            break;
        }
    }
    results
}
