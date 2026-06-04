use std::{fs, path::Path, process::ExitCode};

use crate::{
    analyzer::Analyzer, common::{CompileResult, Settings}, lexer::Lexer, parser::Parser
};
use clap::{self, ArgAction, command};

/// Common utilities for everyone
pub(crate) mod common;

/// Lexical analysis for the language
pub(crate) mod lexer;

/// Recursive descent parser for the language
pub(crate) mod parser;
/// AST definitions
pub(crate) mod ast;

/// Semantic analyzer for the language
pub(crate) mod analyzer;
/// Scope tree for all possible code constructs
pub(crate) mod scope;
/// Context for storing code in a tree based IR
pub(crate) mod context;
/// Defintions for the control flow graph
pub(crate) mod cfg;

// pub(crate) mod codegen;
pub(crate) mod printer;

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
        printer::print_error(sem_result.warnings);
    }
    let scope_pool = sem_result.scope_pool;
    let roots = sem_result.roots;
    printer::print_scopes(&scope_pool, &roots);
    if matches.get_flag("show_ctx") {
        println!();
        printer::print_ir_of_all_scopes(&scope_pool, &roots);
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
