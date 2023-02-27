use std::{fmt::Display, path::PathBuf};

#[derive(Debug, Clone)]
pub struct SourceFile {
    pub path: Option<PathBuf>,
    pub content: String,
}

#[derive(Debug, Clone)]
pub struct Position {
    pub row: u32,
    pub col: u32,
}

impl Position {
    pub fn new() -> Self {
        Position { row: 0, col: 0 }
    }

    #[inline]
    pub fn get_row(&self) -> u32 {
        self.row
    }

    #[inline]
    pub fn get_col(&self) -> u32 {
        self.col
    }
}

impl<T> From<T> for Position
where
    T: Into<PathBuf> + Sized,
{
    fn from(file: T) -> Self {
        Position { row: 0, col: 0 }
    }
}

impl Display for Position {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "{}:{}", self.row + 1, self.col + 1)
    }
}

#[derive(Debug, Clone)]
pub struct Span {
    start: Position,
    end: Position,
}

impl Span {
    pub fn new(start: Position, end: Position) -> Self {
        Self { start, end }
    }

    pub fn start(&self) -> &Position {
        &self.start
    }

    pub fn end(&self) -> &Position {
        &self.end
    }
}

impl From<Position> for Span {
    fn from(value: Position) -> Self {
        Self {
            start: value.clone(),
            end: value,
        }
    }
}

impl From<&Position> for Span {
    fn from(value: &Position) -> Self {
        Self {
            start: value.clone(),
            end: value.clone(),
        }
    }
}
