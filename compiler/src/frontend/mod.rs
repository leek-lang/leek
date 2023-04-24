use std::path::PathBuf;

use crate::{
    common::error::LeekCompilerError,
    frontend::{
        lexer::LeekLexer,
        parser::{LeekParser, Parser},
        reader::FileReader,
    },
};

use self::ast::LeekAst;

pub mod ast;
pub mod lexer;
pub mod parser;
pub mod position;
pub mod reader;

pub fn parse_file(path: PathBuf) -> Result<LeekAst, LeekCompilerError> {
    let reader = FileReader::new(path)?;
    let lexer = LeekLexer::new(reader);
    let parse_tree = LeekParser::parse(lexer)?;

    let ast = LeekAst::build_from(parse_tree);

    Ok(ast)
}

pub fn parse_string(source: String) -> Result<LeekAst, LeekCompilerError> {
    let reader = FileReader::from(source);
    let lexer = LeekLexer::new(reader);
    let parse_tree = LeekParser::parse(lexer)?;

    let ast = LeekAst::build_from(parse_tree);

    Ok(ast)
}
