use std::path::PathBuf;

use crate::{
    common::error::CompilerError,
    frontend::{lexer::Lexer, parser::Parser, reader::FileReader},
};

use self::ast::Ast;

pub mod ast;
pub mod lexer;
pub mod parser;
pub mod position;
pub mod reader;

pub fn parse_file(path: PathBuf) -> Result<Ast, CompilerError> {
    let reader = FileReader::new(path)?;
    let lexer = Lexer::new(reader);
    let parse_tree = Parser::parse(lexer)?;

    println!("{}", &parse_tree.root);

    let ast = Ast::build_from(parse_tree);

    Ok(ast)
}

pub fn parse_string(source: String) -> Result<Ast, CompilerError> {
    let reader = FileReader::from(source);
    let lexer = Lexer::new(reader);
    let parse_tree = Parser::parse(lexer)?;

    println!("{}", &parse_tree.root);

    let ast = Ast::build_from(parse_tree);

    Ok(ast)
}
