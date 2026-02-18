use std::fs;

use crate::{
    common::CompilerResult,
    lexer::Lexer,
    parser::Parser,
};

mod common;
mod lexer;
mod parser;
mod printer;

fn compile_file(file_path: &str) -> CompilerResult<()> {
    let contents = fs::read_to_string(file_path).unwrap();

    let mut lexer = Lexer::new(file_path, &contents);
    let mut parser = Parser::new(&mut lexer)?;
    parser.parse()?;
    Ok(())
}

fn main() {
    if let Err(err) = compile_file("examples/program.bl") {
        printer::print_error(err);
    }
}
