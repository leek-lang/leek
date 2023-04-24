use std::{fmt::Display, path::PathBuf};

#[derive(Debug, Clone)]
pub struct SourceFile {
    pub path: Option<PathBuf>,
    pub content: String,
}

#[derive(Debug, Clone, Copy, PartialEq)]
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
    fn from(_file: T) -> Self {
        Position { row: 0, col: 0 }
    }
}

impl Display for Position {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}:{}", self.row + 1, self.col + 1)
    }
}

#[derive(Debug, Clone, Copy, PartialEq)]
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

pub fn highlight_span(
    f: &mut std::fmt::Formatter<'_>,
    source_file: &SourceFile,
    span: Span,
) -> std::fmt::Result {
    if let Some(path) = &source_file.path {
        writeln!(
            f,
            "{}:{}",
            path.file_name().unwrap().to_str().unwrap(),
            span.start(),
        )?;
    } else {
        writeln!(f, "{}", span.start())?;
    }

    let lines: Vec<_> = source_file.content.lines().collect();

    // Print the lines around and including the one with the error
    let start = if span.start().row < 2 {
        0
    } else {
        span.start().row - 2
    } as usize;

    // Print each line and the line number
    for (n, line) in lines[start..(span.start().row + 1) as usize]
        .iter()
        .enumerate()
    {
        writeln!(f, "{:>3}: {}", n + start + 1, line)?;
    }

    let prepending_count = (span.start().col + 5) as usize;
    let token_width = if span.end().row == span.start().row {
        span.end().col - span.start().col
    } else {
        1
    } as usize;

    // Print the space before the highlight
    write!(f, "{}", String::from(" ").repeat(prepending_count))?;

    // Print the underline highlight
    writeln!(
        f,
        "{}",
        String::from("^").repeat(if token_width > 0 { token_width } else { 1 })
    )?;

    // Print the space before "here"
    write!(f, "{}", String::from(" ").repeat(prepending_count))?;

    writeln!(f, "here")?;

    Ok(())
}
