use std::fmt::{Debug, Display};

use crate::frontend::position::{Position, Span};

#[allow(dead_code)]
#[cfg_attr(not(test), derive(Debug))]
#[derive(Clone)]
pub struct Token {
    pub kind: TokenKind,
    pub text: String,
    pub span: Span,
}

#[derive(Debug, Eq, PartialEq, Clone, Copy)]
pub enum TokenKind {
    // Significant Whitespace
    Newline,

    // Words
    Keyword(KeywordKind), // leak
    Identifier,           // YourMom

    // Grouping
    OpenParen,         // (
    CloseParen,        // )
    OpenBracket,       // [
    CloseBracket,      // ]
    OpenCurlyBracket,  // {
    CloseCurlyBracket, // }

    // Literals
    StringLiteral,                      // "your mom"
    CharLiteral,                        // 'd'
    IntegerLiteral(IntegerLiteralKind), // 69
    FloatLiteral,                       // 420.69

    // Single Operators
    Equals,             // =
    DoubleEquals,       // ==
    LessThan,           // <
    LessThanOrEqual,    // <=
    GreaterThan,        // >
    GreaterThanOrEqual, // >=
    Plus,               // +
    PlusEquals,         // +=
    Minus,              // -
    MinusEquals,        // -=
    Asterisk,           // *
    MultiplyEquals,     // *=
    Divide,             // /
    DivideEquals,       // /=
    Modulo,             // %
    ModuloEquals,       // %=
    BitwiseNot,         // ~
    BitwiseNotEquals,   // ~=
    BitwiseXor,         // ^
    BitwiseXorEquals,   // ^=
    BitwiseOr,          // |
    BitwiseOrEquals,    // |=
    BitwiseAnd,         // &
    BitwiseAndEquals,   // &=
    LogicalNot,         // !
    LogicalNotEquals,   // !=

    // Double Operators
    Exponentiation,       // **
    ExponentiationEquals, // **=
    LeftShift,            // <<
    LeftShiftEquals,      // <<=
    RightShift,           // >>
    RightShiftEquals,     // >>=
    LogicalOr,            // ||
    LogicalOrEquals,      // ||=
    LogicalAnd,           // &&
    LogicalAndEquals,     // &&=

    // Non-Operator symbols
    Arrow,          // ->
    QuestionMark,   // ?
    Comma,          // ,
    Semicolon,      // ;
    Colon,          // :
    DoubleColon,    // ::
    Period,         // .
    BangCoalescing, // !.
    BackSlash,      // \
    Underscore,     // _
    Asperand,       // @
    Hash,           // #
    DollarSign,     // $
}

#[derive(Debug, Eq, PartialEq, Clone, Copy)]
pub enum IntegerLiteralKind {
    Decimal,
    Hexadecimal,
    Binary,
    Octal,
}

#[derive(Debug, Eq, PartialEq, Clone, Copy)]
pub enum KeywordKind {
    Fn,
    Struct,
    Leak,
    Hold,
    Perm,
    If,
    Else,
    While,
    For,
    Yeet,
}

impl<T> From<(TokenKind, T)> for Token
where
    T: Into<String> + Sized,
{
    fn from((kind, text): (TokenKind, T)) -> Self {
        Self {
            kind,
            text: text.into(),
            span: Span::from(Position::new()),
        }
    }
}

#[cfg(test)]
impl Debug for Token {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Token")
            .field("kind", &self.kind)
            .field("text", &self.text)
            .finish()
    }
}

impl Display for Token {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?} => {:?}", self.kind, self.text)
    }
}

impl PartialEq for Token {
    fn eq(&self, other: &Self) -> bool {
        self.kind == other.kind && self.text == other.text
    }
}

impl TokenKind {
    pub fn is_assignment_operator(&self) -> bool {
        matches!(
            self,
            Self::Equals
                | Self::PlusEquals
                | Self::MinusEquals
                | Self::MultiplyEquals
                | Self::DivideEquals
                | Self::ModuloEquals
                | Self::BitwiseNotEquals
                | Self::BitwiseXorEquals
                | Self::BitwiseOrEquals
                | Self::BitwiseAndEquals
                | Self::LogicalNotEquals
                | Self::ExponentiationEquals
                | Self::LeftShiftEquals
                | Self::RightShiftEquals
                | Self::LogicalOrEquals
                | Self::LogicalAndEquals
        )
    }

    pub fn is_unary_operator(&self) -> bool {
        matches!(self, Self::BitwiseNot | Self::LogicalNot | Self::Asterisk)
    }

    pub fn is_binary_operator(&self) -> bool {
        matches!(
            self,
            Self::DoubleEquals
                | Self::LessThan
                | Self::LessThanOrEqual
                | Self::GreaterThan
                | Self::GreaterThanOrEqual
                | Self::Plus
                | Self::Minus
                | Self::Asterisk
                | Self::Divide
                | Self::Modulo
                | Self::BitwiseXor
                | Self::BitwiseOr
                | Self::BitwiseAnd
                | Self::Exponentiation
                | Self::LeftShift
                | Self::RightShift
                | Self::LogicalOr
                | Self::LogicalAnd
        )
    }

    pub fn is_literal(&self) -> bool {
        matches!(
            self,
            Self::CharLiteral | Self::StringLiteral | Self::FloatLiteral | Self::IntegerLiteral(_)
        )
    }

    pub fn grouping_symbol_from(c: char) -> TokenKind {
        match c {
            '(' => Self::OpenParen,
            ')' => Self::CloseParen,
            '[' => Self::OpenBracket,
            ']' => Self::CloseBracket,
            '{' => Self::OpenCurlyBracket,
            '}' => Self::CloseCurlyBracket,
            x => unreachable!("Illegal non-grouping symbol `{}`", x),
        }
    }

    pub fn single_operator_from(c: char) -> TokenKind {
        match c {
            '=' => Self::Equals,
            '<' => Self::LessThan,
            '>' => Self::GreaterThan,
            '!' => Self::LogicalNot,
            '+' => Self::Plus,
            '-' => Self::Minus,
            '*' => Self::Asterisk,
            '/' => Self::Divide,
            '%' => Self::Modulo,
            '~' => Self::BitwiseNot,
            '^' => Self::BitwiseXor,
            '|' => Self::BitwiseOr,
            '&' => Self::BitwiseAnd,
            x => unreachable!("Illegal single non-operator `{}`", x),
        }
    }

    pub fn double_operator_from(c: char) -> TokenKind {
        match c {
            '*' => Self::Exponentiation,
            '<' => Self::LeftShift,
            '>' => Self::RightShift,
            '&' => Self::LogicalAnd,
            '|' => Self::LogicalOr,
            x => unreachable!("Illegal double non-operator `{}`", x),
        }
    }

    pub fn single_equals_operator_from(c: char) -> TokenKind {
        match c {
            '=' => Self::DoubleEquals,
            '<' => Self::LessThanOrEqual,
            '>' => Self::GreaterThanOrEqual,
            '!' => Self::LogicalNotEquals,
            '+' => Self::PlusEquals,
            '-' => Self::MinusEquals,
            '*' => Self::MultiplyEquals,
            '/' => Self::DivideEquals,
            '%' => Self::ModuloEquals,
            '~' => Self::BitwiseNotEquals,
            '^' => Self::BitwiseXorEquals,
            '|' => Self::BitwiseOrEquals,
            '&' => Self::BitwiseAndEquals,
            x => unreachable!("Illegal single non-equals-operator `{}`", x),
        }
    }

    pub fn double_equals_operator_from(c: char) -> TokenKind {
        match c {
            '*' => Self::ExponentiationEquals,
            '<' => Self::LeftShiftEquals,
            '>' => Self::RightShiftEquals,
            '&' => Self::LogicalAndEquals,
            '|' => Self::LogicalOrEquals,
            x => unreachable!("Illegal double non-equals-operator `{}`", x),
        }
    }

    pub fn other_symbol_from(c: impl Into<String>) -> TokenKind {
        match c.into().as_str() {
            "->" => Self::Arrow,
            "?" => Self::QuestionMark,
            "!." => Self::BangCoalescing,
            "," => Self::Comma,
            ";" => Self::Semicolon,
            ":" => Self::Colon,
            "::" => Self::DoubleColon,
            "." => Self::Period,
            "\\" => Self::BackSlash,
            "_" => Self::Underscore,
            "@" => Self::Asperand,
            "#" => Self::Hash,
            "$" => Self::DollarSign,
            x => unreachable!("Illegal non-other-symbol `{}`", x),
        }
    }
}

impl TryFrom<&String> for KeywordKind {
    type Error = ();

    fn try_from(value: &String) -> Result<Self, Self::Error> {
        Ok(match value.as_str() {
            "fn" => Self::Fn,
            "struct" => Self::Struct,
            "leak" => Self::Leak,
            "hold" => Self::Hold,
            "perm" => Self::Perm,
            "if" => Self::If,
            "else" => Self::Else,
            "while" => Self::While,
            "for" => Self::For,
            "yeet" => Self::Yeet,
            _ => return Err(()),
        })
    }
}