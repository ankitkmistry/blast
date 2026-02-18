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

pub trait HasLineInfo {
    fn get_line_info(&self) -> LineInfo;
}

#[derive(Clone, Debug)]
pub enum CompilerError {
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

impl fmt::Display for CompilerError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "TODO: implement this")
    }
}

impl Error for CompilerError {}

pub type CompilerResult<T> = Result<T, CompilerError>;
