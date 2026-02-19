use std::fs;

use crate::common::{CompileError, LineInfo};

pub fn print_error(err: CompileError) {
    match err {
        CompileError::LexerError {
            file_path,
            line_info,
            msg,
        } => print_file_error(&file_path, line_info, &msg),
        CompileError::ParserError {
            file_path,
            line_info,
            msg,
        } => print_file_error(&file_path, line_info, &msg),
    }
}

fn interpolate_chars(c1: char, c2: char) -> char {
    // This function handles \t and other kind of whitespaces
    // But ignores normal ' '
    if c1 != ' ' && c1.is_whitespace() {
        c1
    } else {
        c2
    }
}

const UNDERLINE_CHAR: char = '^';

fn num_digits(x: usize) -> usize {
    if x < 10 {
        1
    } else if x < 100 {
        2
    } else if x < 1000 {
        3
    } else if x < 10000 {
        4
    } else if x < 100000 {
        5
    } else if x < 1000000 {
        6
    } else if x < 10000000 {
        7
    } else if x < 100000000 {
        8
    } else if x < 1000000000 {
        9
    } else if x < 10000000000 {
        10
    } else {
        x.to_string().len()
    }
}

fn print_file_error(file_path: &str, line_info: LineInfo, msg: &str) {
    println!("error: {}", msg);
    println!(
        "in file: {}:{}:{}",
        file_path, line_info.line_start, line_info.col_start
    );

    let line_column_width = num_digits(line_info.line_end) + 2;

    for (i, line) in fs::read_to_string(file_path)
        .unwrap()
        .split('\n')
        .skip(line_info.line_start - 1)
        .take(line_info.line_end - line_info.line_start + 1)
        .enumerate()
    {
        let lineno = line_info.line_start + i;
        let mut underline = String::new();
        if lineno == line_info.line_start && lineno == line_info.line_end {
            for (j, c) in line.chars().enumerate() {
                let col = j + 1;
                if line_info.col_start <= col && col < line_info.col_end {
                    underline.push(interpolate_chars(c, UNDERLINE_CHAR));
                } else {
                    underline.push(interpolate_chars(c, ' '));
                }
            }
        } else if lineno == line_info.line_start {
            for (j, c) in line.chars().enumerate() {
                let col = j + 1;
                if line_info.col_start <= col {
                    underline.push(interpolate_chars(c, UNDERLINE_CHAR));
                } else {
                    underline.push(interpolate_chars(c, ' '));
                }
            }
        } else if lineno == line_info.line_end {
            for (j, c) in line.chars().enumerate() {
                let col = j + 1;
                if col < line_info.col_end {
                    underline.push(interpolate_chars(c, UNDERLINE_CHAR));
                } else {
                    underline.push(interpolate_chars(c, ' '));
                }
            }
        } else {
            for c in line.chars() {
                underline.push(interpolate_chars(c, UNDERLINE_CHAR));
            }
        }

        println!("{:>line_column_width$} | {}", lineno, line);
        println!("{: >line_column_width$} | {}", "", underline);
    }
}
