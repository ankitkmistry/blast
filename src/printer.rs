use std::{fmt::Write, fs};

use color_print::{cprintln, cwrite};

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

fn interpolate_char(c1: char, c2: char) -> char {
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
    let mut result = String::new();
    let mut flag = None;
    let mut flag_color_r = 0xFF;
    let mut flag_color_g = 0xFF;
    let mut flag_color_b = 0xFF;
    for i in 0..msg.chars().count() {
        let c = msg.chars().nth(i).unwrap();
        if c == '\'' {
            if let Some(c) = flag
                && c == '\''
            {
                flag = None;
                continue;
            }
            flag = Some('\'');
            flag_color_r = 214;
            flag_color_g = 25;
            flag_color_b = 224;
        } else if c == '<' {
            flag = Some('<');
            flag_color_r = 3;
            flag_color_g = 189;
            flag_color_b = 187;
        } else if c == '>'
            && let Some(c) = flag
            && c == '<'
        {
            flag = None;
        } else {
            if flag.is_some() {
                result = format!(
                    "{}\x1b[1m\x1b[38;2;{};{};{}m{}\x1b[0m",
                    result, flag_color_r, flag_color_g, flag_color_b, c
                );
            } else {
                result.push(c);
            }
        }
    }
    cprintln!("<r,s>error</>: <s>{}</>", result);
    cprintln!(
        "in file: {}:<m!>{}</>:<m!>{}</>",
        file_path,
        line_info.line_start,
        line_info.col_start
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
            let count = line.chars().count().max(line_info.col_end - 1);
            for j in 0..count {
                let col = j + 1;
                let c = line.chars().nth(j).unwrap_or(' ');
                if line_info.col_start <= col && col < line_info.col_end {
                    let _ = cwrite!(
                        &mut underline,
                        "<y!>{}</>",
                        interpolate_char(c, UNDERLINE_CHAR)
                    );
                } else {
                    underline.push(interpolate_char(c, ' '));
                }
            }
        } else if lineno == line_info.line_start {
            let count = line.chars().count().max(line_info.col_end - 1);
            for j in 0..count {
                let col = j + 1;
                let c = line.chars().nth(j).unwrap_or(' ');
                if line_info.col_start <= col {
                    let _ = cwrite!(
                        &mut underline,
                        "<y!>{}</>",
                        interpolate_char(c, UNDERLINE_CHAR)
                    );
                } else {
                    underline.push(interpolate_char(c, ' '));
                }
            }
        } else if lineno == line_info.line_end {
            let count = line.chars().count().max(line_info.col_end - 1);
            for j in 0..count {
                let col = j + 1;
                let c = line.chars().nth(j).unwrap_or(' ');
                if col < line_info.col_end {
                    let _ = cwrite!(
                        &mut underline,
                        "<y!>{}</>",
                        interpolate_char(c, UNDERLINE_CHAR)
                    );
                } else {
                    underline.push(interpolate_char(c, ' '));
                }
            }
        } else {
            let count = line.chars().count().max(line_info.col_end - 1);
            for j in 0..count {
                let col = j + 1;
                let c = line.chars().nth(j).unwrap_or(' ');
                let _ = cwrite!(
                    &mut underline,
                    "<y!>{}</>",
                    interpolate_char(c, UNDERLINE_CHAR)
                );
            }
        }

        cprintln!("<m!,s>{:>line_column_width$}</> <b!>|</> {}", lineno, line);
        cprintln!(
            "<m!,s>{: >line_column_width$}</> <b!>|</> {}",
            "",
            underline
        );
    }
}
