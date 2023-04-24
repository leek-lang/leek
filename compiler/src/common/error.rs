use std::fmt::Display;

use crate::{
    backend::CodeGenError,
    frontend::{
        ast::builder::AstBuildError, lexer::LexerError, parser::ParserError, reader::FileReadError,
    },
    middle::type_checking::TypeCheckingError,
};

// TODO: Refactor with thiserror

#[derive(Debug)]
pub enum LeekCompilerError {
    FileReadError(FileReadError),         // File -> Chars
    LexerError(LexerError),               // Chars -> Tokens
    ParserError(ParserError),             // Tokens -> Parse Tree
    AstBuildError(AstBuildError),         // Parse Tree -> AST
    AstLoweringError,                     // AST -> HIR
    TypeCheckingError(TypeCheckingError), // HIR -> MIR
    LowLevelLoweringError,                // MIR -> LIR
    CodeGenError(CodeGenError),           // LIR -> ASM
}

impl LeekCompilerError {
    /// Should print to the stderr and exit with a non-zero exit code
    pub fn report(&self) -> ! {
        eprintln!("{self}");

        std::process::exit(1);
    }
}

impl Display for LeekCompilerError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            LeekCompilerError::FileReadError(e) => write!(f, "File Read Error: \n{e}"),
            LeekCompilerError::LexerError(e) => write!(f, "Lexer Error: \n{e}"),
            LeekCompilerError::ParserError(e) => {
                write!(
                    f,
                    "Parser Error: {e}\n=================================\n\n{e:#?}\n"
                )
            }
            LeekCompilerError::AstBuildError(e) => {
                write!(
                    f,
                    "Ast Build Error: \n{e}\n=================================\n\n{e:#?}\n"
                )
            }
            LeekCompilerError::TypeCheckingError(e) => {
                write!(
                    f,
                    "Type Error: \n{e}\n=================================\n\n{e:#?}\n"
                )
            }

            _ => todo!("Implement other error messages"),
        }
    }
}

impl From<FileReadError> for LeekCompilerError {
    fn from(error: FileReadError) -> Self {
        LeekCompilerError::FileReadError(error)
    }
}

impl From<LexerError> for LeekCompilerError {
    fn from(error: LexerError) -> Self {
        LeekCompilerError::LexerError(error)
    }
}

impl From<ParserError> for LeekCompilerError {
    fn from(error: ParserError) -> Self {
        LeekCompilerError::ParserError(error)
    }
}

impl From<AstBuildError> for LeekCompilerError {
    fn from(error: AstBuildError) -> Self {
        LeekCompilerError::AstBuildError(error)
    }
}

impl From<CodeGenError> for LeekCompilerError {
    fn from(error: CodeGenError) -> Self {
        LeekCompilerError::CodeGenError(error)
    }
}
