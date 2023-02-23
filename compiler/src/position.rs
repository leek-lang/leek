use std::{fmt::Display, path::PathBuf};

// FIXME: Don't allocate strings all the time when this is cloned. Global file table?
#[derive(Debug, Clone)]
pub struct Position {
    file: Option<PathBuf>,
    pub row: u32,
    pub col: u32,
}

impl Position {
    pub fn new() -> Self {
        Position {
            file: None,
            row: 0,
            col: 0,
        }
    }

    #[inline]
    pub fn get_file(&self) -> Option<&PathBuf> {
        self.file.as_ref().map(|f| f)
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
        Position {
            file: Some(file.into()),
            row: 0,
            col: 0,
        }
    }
}

impl Display for Position {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if let Some(file) = &self.file {
            writeln!(
                f,
                "{}:{}:{}",
                file.canonicalize()
                    .expect("Could not canonicalize file path")
                    .to_str()
                    .expect("Could not convert file path to string")
                    .trim_start_matches(r"\\?\"),
                self.row + 1,
                self.col + 1
            )
        } else {
            writeln!(f, "<literal contents>:{}:{}", self.row + 1, self.col + 1)
        }
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
