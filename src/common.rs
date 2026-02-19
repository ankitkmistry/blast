use std::{error::Error, fmt};

// line_start and line_end is inclusive
// col_start and col_end is exclusive
#[derive(Copy, Clone, Debug)]
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

impl LineInfo {
    pub fn from_range(start: &impl HasLineInfo, end: &impl HasLineInfo) -> Self {
        Self {
            line_start: start.get_line_info().line_start,
            line_end: end.get_line_info().line_end,
            col_start: start.get_line_info().col_start,
            col_end: end.get_line_info().col_end,
        }
    }

    pub fn from_items(items: &[impl HasLineInfo]) -> Self {
        assert!(items.len() > 0);
        Self::from_range(items.first().unwrap(), items.last().unwrap())
    }
}

pub trait HasLineInfo {
    fn get_line_info(&self) -> LineInfo;
}

impl<T> HasLineInfo for Box<T>
where
    T: HasLineInfo,
{
    fn get_line_info(&self) -> LineInfo {
        self.get_line_info()
    }
}

#[derive(Clone, Debug)]
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
}

impl fmt::Display for CompileError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "TODO: implement this")
    }
}

impl Error for CompileError {}

pub type CompileResult<T> = Result<T, CompileError>;
