use std::{fs, path::Path, process::ExitCode};

use crate::{
    analyzer::Analyzer,
    common::{CompileResult, Settings},
    lexer::Lexer,
    parser::Parser,
};
use clap::{self, ArgAction, command};

pub(crate) mod analyzer;
pub(crate) mod ast;
pub(crate) mod cfg;
pub(crate) mod common;
pub(crate) mod context;
pub(crate) mod lexer;
pub(crate) mod parser;
pub(crate) mod printer;
pub(crate) mod scope;
pub(crate) mod codegen;

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
        .arg(
            clap::Arg::new("show_ctx")
                .short('x')
                .long("ctx")
                .help("Shows semantic analyzer context output")
                .required(false)
                .action(ArgAction::SetTrue),
        )
        .get_matches();

    let settings = Settings {
        register_size: std::mem::size_of::<usize>(),
        pointer_size: std::mem::size_of::<*const u8>(),
    };

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
    let analyzer = Analyzer::new(
        settings,
        file_path,
        Path::new(file_path).file_stem().unwrap().to_str().unwrap(),
        &ast,
    );
    let sem_result = analyzer.analyze()?;
    if !sem_result.warnings.is_empty() {
        printer::print_error(common::CompileError::Errors(sem_result.warnings));
    }
    let roots = sem_result.roots;
    printer::print_scopes(&roots);
    if matches.get_flag("show_ctx") {
        println!();
        printer::print_ir_of_all_scopes(&roots);
    }
    // codegen::generate_code("main", roots);

    Ok(())
}

fn main() -> ExitCode {
    stderrlog::new()
        .module(module_path!())
        .color(stderrlog::ColorChoice::Auto)
        .verbosity(4)
        .init()
        .unwrap();

    if let Err(err) = compile_file("examples/program.bl") {
        printer::print_error(err);
        println!();
        if cfg!(debug_assertions) {
            ExitCode::SUCCESS
        } else {
            ExitCode::FAILURE
        }
    } else {
        ExitCode::SUCCESS
    }
}
