use std::{fs, path::Path};

use crate::{analyzer::Analyzer, common::CompileResult, lexer::Lexer, parser::Parser};
use clap::{self, ArgAction, command};

mod analyzer;
mod ast;
mod common;
mod context;
mod lexer;
mod parser;
mod printer;
mod scope;
mod taipe;

fn compile_file(file_path: &str) -> CompileResult<()> {
    let matches = command!()
        .about("The compiler for the Blast programming language.")
        .arg(
            clap::Arg::new("show_lex")
                .short('l')
                .long("lex")
                .help("Shows lexer output")
                .required(false)
                .action(ArgAction::SetTrue),
        )
        .arg(
            clap::Arg::new("show_ast")
                .short('p')
                .long("ast")
                .help("Shows parser AST output")
                .required(false)
                .action(ArgAction::SetTrue),
        )
        .get_matches();

    let contents = fs::read_to_string(file_path).unwrap();

    let mut lexer = Lexer::new(file_path, &contents);
    let mut tokens = Vec::new();
    while lexer.has_next_token() {
        tokens.push(lexer.next_token()?);
        if matches.get_flag("show_lex") {
            printer::print_token(tokens.last().unwrap());
        }
    }
    let mut parser = Parser::new(file_path, &tokens)?;
    let ast = parser.parse()?;
    if matches.get_flag("show_ast") {
        printer::print_ast("program", &ast);
    }
    let mut analyzer = Analyzer::new(
        file_path,
        Path::new(file_path).file_stem().unwrap().to_str().unwrap(),
        &ast,
    );
    analyzer.analyze()?;
    Ok(())
}

fn main() {
    if let Err(err) = compile_file("examples/program.bl") {
        printer::print_error(err);
    }
}
