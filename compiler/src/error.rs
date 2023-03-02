use std::fmt::Display;

use crate::{lexer::LexerError, parser::ParserError, reader::FileReadError, ast::AstBuildError};

#[derive(Debug)]
pub enum LeekCompilerError {
    FileReadError(FileReadError),
    LexerError(LexerError),
    ParserError(ParserError),
    AstBuildError(AstBuildError),
    TypeCheckerError,
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
                    "Parser Error: \n{e}\n=================================\n\n{e:#?}\n"
                )
            }
            LeekCompilerError::AstBuildError(e) => {
                write!(
                    f,
                    "Ast Build Error: \n{e}\n=================================\n\n{e:#?}\n"
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
