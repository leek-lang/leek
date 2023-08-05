use core::panic;
use std::fmt::Display;

use crate::{
    common::error::LeekCompilerError,
    frontend::lexer::{IntegerLiteralKind, KeywordKind, LeekToken, LeekTokenKind, Lexer},
    frontend::position::{SourceFile, Span},
};

use super::position::highlight_span;

#[derive(Debug)]
pub struct ParseTree {
    pub root: ParseTreeNode,
    pub source_file: SourceFile,
}

impl PartialEq for ParseTree {
    fn eq(&self, other: &Self) -> bool {
        self.root == other.root
    }
}

#[derive(Debug, PartialEq, Clone)]
pub enum ParseTreeNode {
    Terminal(LeekToken),
    NonTerminal(ParseTreeNodeNonTerminal),
}

#[derive(Debug, PartialEq, Clone)]
pub struct ParseTreeNodeNonTerminal {
    pub kind: ParseTreeNonTerminalKind,
    pub children: Vec<ParseTreeNode>,
}

impl ParseTreeNode {
    fn fmt_recursive(&self, f: &mut std::fmt::Formatter<'_>, indent: usize) -> std::fmt::Result {
        match self {
            ParseTreeNode::Terminal(token) => {
                writeln!(f, "{}{token}", String::from(" ").repeat(indent))
            }
            ParseTreeNode::NonTerminal(ParseTreeNodeNonTerminal { kind, children }) => {
                writeln!(f, "{}{kind:?}:", String::from(" ").repeat(indent))?;

                for child in children {
                    child.fmt_recursive(f, indent + 4)?;
                }

                Ok(())
            }
        }
    }

    pub fn terminal_token(&self) -> &LeekToken {
        if let ParseTreeNode::Terminal(token) = self {
            token
        } else {
            panic!("Expected node to be terminal token")
        }
    }

    pub fn non_terminal(&self) -> &ParseTreeNodeNonTerminal {
        if let ParseTreeNode::NonTerminal(non_terminal) = self {
            non_terminal
        } else {
            panic!("Expected node to be non-terminal")
        }
    }
}

macro_rules! terminal {
    ($token:expr) => {
        ParseTreeNode::Terminal($token)
    };
}

#[allow(unused_macros)]
macro_rules! non_terminal {
    ($kind:expr, $children:expr) => {
        ParseTreeNode::NonTerminal(ParseTreeNodeNonTerminal {
            kind: $kind,
            children: $children,
        })
    };
}

impl Display for ParseTreeNode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.fmt_recursive(f, 0)
    }
}

/// Represents non-terminal parse tree nodes
#[derive(Debug, PartialEq, Clone)]
pub enum ParseTreeNonTerminalKind {
    Program,
    FunctionDefinition,
    FunctionReturnType,
    FunctionParameters,
    Block,
    Statement,
    Expression,
    FunctionCallExpression,
    FunctionArguments,
    StructFieldAccess,
    StructMethodCall,
    BinaryExpression,
    UnaryExpression,
    Atom,
    StructDefinition,
    StructDefinitionBody,
    StructInitialization,
    TypeAssociation,
    Type,
    QualifiedIdentifier,
    ConstantVariableDeclaration,
    StaticVariableDeclaration,
    LocalVariableDeclaration,
    Yeet,
    VariableAssignment,
}

// TODO: Add better parser error output

#[derive(Debug)]
pub struct ParserError {
    pub kind: ParserErrorKind,
    pub source_file: SourceFile,
    pub span: Span,
}

impl Display for ParserError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self.kind {
            ParserErrorKind::UnexpectedToken { expected, found } => writeln!(
                f,
                "Unexpected token {:?}. Expected one of: {:?}",
                found, expected
            )?,
            ParserErrorKind::UnexpectedKeyword { expected, found } => writeln!(
                f,
                "Unexpected keyword {:?}. Expected one of: {:?}",
                found, expected
            )?,
            ParserErrorKind::UnexpectedEndOfInput => writeln!(f, "Unexpected end of input.")?,
            ParserErrorKind::IndexIntoNonIdentifier => {
                writeln!(f, "Cannot access field of non-struct object.")?
            }
        }

        highlight_span(f, &self.source_file, self.span.clone())?;

        Ok(())
    }
}

#[derive(Debug)]
pub enum ParserErrorKind {
    UnexpectedToken {
        expected: Vec<LeekTokenKind>,
        found: LeekTokenKind,
    },
    UnexpectedKeyword {
        expected: Vec<KeywordKind>,
        found: KeywordKind,
    },
    UnexpectedEndOfInput,
    IndexIntoNonIdentifier,
}

pub trait Parser {
    /// Takes in a lexer and returns the root of a parse tree
    fn parse(lexer: impl Lexer + 'static) -> Result<ParseTree, LeekCompilerError>;
}

pub struct LeekParser {
    lexer: Box<dyn Lexer>,
}

impl Parser for LeekParser {
    fn parse(lexer: impl Lexer + 'static) -> Result<ParseTree, LeekCompilerError> {
        let mut parser = LeekParser::new(lexer);

        parser.parse_from_lexer()
    }
}

impl LeekParser {
    fn new(lexer: impl Lexer + 'static) -> Self {
        Self {
            lexer: Box::new(lexer),
        }
    }

    /// Peeks the next token or returns an error if there are none left
    fn peek_expect(&self) -> Result<&LeekToken, LeekCompilerError> {
        self.lexer.peek()?.ok_or_else(|| {
            ParserError {
                kind: ParserErrorKind::UnexpectedEndOfInput,
                source_file: self.lexer.get_source_file().clone(),
                span: Span::from(self.lexer.get_position()),
            }
            .into()
        })
    }

    /// Grabs the next token and asserts that it is the provided type
    fn peek_expect_is(&self, kind: LeekTokenKind) -> Result<bool, LeekCompilerError> {
        let token = self.peek_expect()?;

        Ok(token.kind == kind)
    }

    /// Peeks the nth token or returns an error if there are none left
    #[allow(unused)]
    fn peek_nth_expect(&self, n: usize) -> Result<&LeekToken, LeekCompilerError> {
        self.lexer.peek_nth(n)?.ok_or_else(|| {
            ParserError {
                kind: ParserErrorKind::UnexpectedEndOfInput,
                source_file: self.lexer.get_source_file().clone(),
                span: Span::from(self.lexer.get_position()),
            }
            .into()
        })
    }

    /// Peeks the next token and asserts that it is one of the provided types
    fn peek_expect_is_of(
        &self,
        kinds: Vec<LeekTokenKind>,
    ) -> Result<&LeekToken, LeekCompilerError> {
        let token = self.peek_expect()?;

        if !kinds.contains(&token.kind) {
            return Err(ParserError {
                kind: ParserErrorKind::UnexpectedToken {
                    expected: kinds,
                    found: token.kind,
                },
                source_file: self.lexer.get_source_file().clone(),
                span: token.span.clone(),
            }
            .into());
        }

        Ok(token)
    }

    /// Searches the next token ignoring new lines
    fn peek_nth_ignore_whitespace(
        &self,
        n: usize,
    ) -> Result<Option<&LeekToken>, LeekCompilerError> {
        let mut peek_index = 0;
        let mut non_nl_tokens = 0;

        while self.lexer.has_next()? {
            let Some(peeked) = self.lexer.peek_nth(peek_index)? else {
                return Ok(None);
            };

            match peeked.kind {
                LeekTokenKind::Newline => {
                    peek_index += 1;
                    continue;
                }
                _ => {
                    if non_nl_tokens == n {
                        return Ok(Some(peeked));
                    } else {
                        non_nl_tokens += 1;
                        peek_index += 1;
                    }
                }
            }
        }

        Ok(None)
    }

    /// Peeks the nth token or returns an error if there are none left
    fn peek_nth_ignore_whitespace_expect(&self, n: usize) -> Result<&LeekToken, LeekCompilerError> {
        self.peek_nth_ignore_whitespace(n)?
            .ok_or_else(|| self.create_error(ParserErrorKind::UnexpectedEndOfInput))
    }

    /// Ignores tokens while they are new lines
    fn bleed_whitespace(&mut self) -> Result<(), LeekCompilerError> {
        while self
            .lexer
            .peek()?
            .is_some_and(|t| t.kind == LeekTokenKind::Newline)
        {
            self.lexer.next()?;
        }

        Ok(())
    }

    /// Grabs the next token or throws an error if none were found
    fn next_expect(&mut self) -> Result<LeekToken, LeekCompilerError> {
        self.lexer
            .next()?
            .ok_or_else(|| self.create_error(ParserErrorKind::UnexpectedEndOfInput))
    }

    /// Grabs the next token and asserts that it is the provided type
    fn next_expect_is(&mut self, kind: LeekTokenKind) -> Result<LeekToken, LeekCompilerError> {
        let token = self.next_expect()?;

        if token.kind != kind {
            return Err(self.create_error_with_span(
                ParserErrorKind::UnexpectedToken {
                    expected: vec![kind],
                    found: token.kind,
                },
                token.span,
            ));
        }

        Ok(token)
    }

    /// Gets the next token and asserts that it is one of the provided types
    fn next_expect_is_of(
        &mut self,
        kinds: Vec<LeekTokenKind>,
    ) -> Result<LeekToken, LeekCompilerError> {
        let token = self.next_expect()?;

        if !kinds.contains(&token.kind) {
            return Err(self.create_error_with_span(
                ParserErrorKind::UnexpectedToken {
                    expected: kinds,
                    found: token.kind,
                },
                token.span,
            ));
        }

        Ok(token)
    }

    /// Creates the associated error variant from the lexer's current position
    fn create_error(&self, kind: ParserErrorKind) -> LeekCompilerError {
        ParserError {
            kind,
            source_file: self.lexer.get_source_file().clone(),
            span: Span::from(self.lexer.get_position()),
        }
        .into()
    }

    /// Creates the associated error variant from a span
    fn create_error_with_span(&self, kind: ParserErrorKind, span: Span) -> LeekCompilerError {
        ParserError {
            kind,
            source_file: self.lexer.get_source_file().clone(),
            span,
        }
        .into()
    }

    /// Program ::
    ///     (
    ///         FunctionDefinition
    ///         | FunctionDeclaration
    ///         | StructDefinition
    ///         | ConstantVariableDeclaration
    ///         | StaticVariableDeclaration
    ///     )+
    ///      
    fn parse_program_part(&mut self) -> Result<ParseTreeNode, LeekCompilerError> {
        let peeked_token = self.peek_expect()?;

        match peeked_token.kind {
            // FunctionDefinition or FunctionDeclaration
            LeekTokenKind::Keyword(KeywordKind::Fn) => {
                self.parse_function_declaration_or_definition()
            }
            // StructDefinition
            LeekTokenKind::Keyword(KeywordKind::Struct) => self.parse_struct_definition(),
            // ConstantVariableDeclaration
            LeekTokenKind::Keyword(KeywordKind::Perm) => self.parse_constant_variable_declaration(),
            // StaticVariableDeclaration
            LeekTokenKind::Keyword(KeywordKind::Hold) => self.parse_static_variable_declaration(),
            // Unexpected keyword
            LeekTokenKind::Keyword(kw) => Err(self.create_error_with_span(
                ParserErrorKind::UnexpectedKeyword {
                    expected: vec![
                        KeywordKind::Fn,
                        KeywordKind::Struct,
                        KeywordKind::Perm,
                        KeywordKind::Hold,
                    ],
                    found: kw,
                },
                peeked_token.span.clone(),
            )),
            // Any other token
            _ => Err(self.create_error_with_span(
                ParserErrorKind::UnexpectedToken {
                    expected: vec![
                        LeekTokenKind::Keyword(KeywordKind::Fn),
                        LeekTokenKind::Keyword(KeywordKind::Struct),
                        LeekTokenKind::Keyword(KeywordKind::Perm),
                        LeekTokenKind::Keyword(KeywordKind::Hold),
                    ],
                    found: peeked_token.kind,
                },
                peeked_token.span.clone(),
            )),
        }
    }

    /// FunctionDefinition ::
    ///     `fn` QualifiedIdentifier FunctionParameters FunctionReturnType? Block
    ///
    /// FunctionDeclaration ::
    ///     `fn` QualifiedIdentifier FunctionParameters FunctionReturnType? Newline
    ///   
    fn parse_function_declaration_or_definition(
        &mut self,
    ) -> Result<ParseTreeNode, LeekCompilerError> {
        let mut children = Vec::new();

        children.push(terminal!(
            self.next_expect_is(LeekTokenKind::Keyword(KeywordKind::Fn))?
        ));
        self.bleed_whitespace()?;

        children.push(self.parse_qualified_identifier()?);
        self.bleed_whitespace()?;

        children.push(self.parse_function_parameters()?);

        if self
            .peek_nth_ignore_whitespace(0)?
            .is_some_and(|token| token.kind == LeekTokenKind::Arrow)
        {
            self.bleed_whitespace()?;
            children.push(self.parse_return_type()?);
        }

        self.bleed_whitespace()?;
        children.push(self.parse_block()?);

        Ok(ParseTreeNode::NonTerminal(ParseTreeNodeNonTerminal {
            kind: ParseTreeNonTerminalKind::FunctionDefinition,
            children,
        }))
    }

    /// FunctionReturnType ::
    ///     `->` Type
    fn parse_return_type(&mut self) -> Result<ParseTreeNode, LeekCompilerError> {
        let children = vec![
            terminal!(self.next_expect_is(LeekTokenKind::Arrow)?),
            self.parse_type()?,
        ];

        Ok(ParseTreeNode::NonTerminal(ParseTreeNodeNonTerminal {
            kind: ParseTreeNonTerminalKind::FunctionReturnType,
            children,
        }))
    }

    /// FunctionParameters ::
    ///     `(`
    ///          (TypeAssociation `,`)* TypeAssociation
    ///      `)`
    fn parse_function_parameters(&mut self) -> Result<ParseTreeNode, LeekCompilerError> {
        let mut children = Vec::new();

        children.push(terminal!(self.next_expect_is(LeekTokenKind::OpenParen)?));
        self.bleed_whitespace()?;

        match self.peek_expect()?.kind {
            LeekTokenKind::CloseParen => {}
            _ => {
                children.push(self.parse_type_association()?);
                self.bleed_whitespace()?;

                while self.peek_expect_is(LeekTokenKind::Comma)? {
                    children.push(terminal!(self.next_expect_is(LeekTokenKind::Comma)?));
                    self.bleed_whitespace()?;
                    children.push(self.parse_type_association()?);
                    self.bleed_whitespace()?;
                }
            }
        }
        self.bleed_whitespace()?;

        children.push(terminal!(self.next_expect_is(LeekTokenKind::CloseParen)?));

        Ok(ParseTreeNode::NonTerminal(ParseTreeNodeNonTerminal {
            kind: ParseTreeNonTerminalKind::FunctionParameters,
            children,
        }))
    }

    /// Block ::
    ///     `{`
    ///         (Block | Statement)*
    ///     `}`
    fn parse_block(&mut self) -> Result<ParseTreeNode, LeekCompilerError> {
        let mut children = Vec::new();

        children.push(terminal!(
            self.next_expect_is(LeekTokenKind::OpenCurlyBracket)?
        ));
        self.bleed_whitespace()?;

        while self.lexer.has_next()? {
            let token = self.lexer.peek()?.unwrap();

            match token.kind {
                // Ignore preceding newlines
                LeekTokenKind::Newline => {
                    self.lexer.next()?;
                }
                // Allow recursive blocks
                LeekTokenKind::OpenCurlyBracket => children.push(self.parse_block()?),
                // Break the loop if a closing bracket is found
                LeekTokenKind::CloseCurlyBracket => break,

                _ => children.push(self.parse_statement()?),
            }
        }

        children.push(terminal!(
            self.next_expect_is(LeekTokenKind::CloseCurlyBracket)?
        ));
        self.bleed_whitespace()?;

        Ok(ParseTreeNode::NonTerminal(ParseTreeNodeNonTerminal {
            kind: ParseTreeNonTerminalKind::Block,
            children,
        }))
    }

    /// Statement ::
    ///     (
    ///         (yeet Expression)
    ///         | (leak identifier (`:` Type)? = Expression)
    ///         | (QualifiedIdentifier assignment Expression)
    ///         | (FunctionCallExpression)
    ///     )
    fn parse_statement(&mut self) -> Result<ParseTreeNode, LeekCompilerError> {
        let mut children = Vec::new();

        match self.peek_expect()?.kind {
            LeekTokenKind::Keyword(KeywordKind::Yeet) => {
                children.push(self.parse_yeet_statement()?);
            }
            LeekTokenKind::Keyword(KeywordKind::Leak) => {
                children.push(self.parse_local_variable_declaration()?);
            }
            k @ LeekTokenKind::Identifier => {
                let identifier = self.parse_qualified_identifier()?;

                // Could be assignment or function call
                match self.peek_nth_ignore_whitespace_expect(0)?.kind {
                    LeekTokenKind::OpenParen => {
                        children.push(self.parse_function_call_expression(identifier)?)
                    }
                    k if k.is_assignment_operator() => {
                        children.push(self.parse_variable_assignment(identifier, k)?);
                    }
                    _ => {
                        return Err(self.create_error(ParserErrorKind::UnexpectedToken {
                            expected: vec![
                                LeekTokenKind::OpenParen,
                                LeekTokenKind::Equals,
                                LeekTokenKind::PlusEquals,
                                LeekTokenKind::MinusEquals,
                                LeekTokenKind::MultiplyEquals,
                                LeekTokenKind::DivideEquals,
                                LeekTokenKind::ModuloEquals,
                                LeekTokenKind::BitwiseNotEquals,
                                LeekTokenKind::BitwiseXorEquals,
                                LeekTokenKind::BitwiseOrEquals,
                                LeekTokenKind::BitwiseAndEquals,
                                LeekTokenKind::LogicalNotEquals,
                                LeekTokenKind::ExponentiationEquals,
                                LeekTokenKind::LeftShiftEquals,
                                LeekTokenKind::RightShiftEquals,
                                LeekTokenKind::LogicalOrEquals,
                                LeekTokenKind::LogicalAndEquals,
                            ],
                            found: k,
                        }));
                    }
                }
            }
            k => {
                return Err(self.create_error(ParserErrorKind::UnexpectedToken {
                    expected: vec![
                        LeekTokenKind::Keyword(KeywordKind::Yeet),
                        LeekTokenKind::Keyword(KeywordKind::Leak),
                        LeekTokenKind::Identifier,
                    ],
                    found: k,
                }));
            }
        }

        match self
            .peek_expect_is_of(vec![
                LeekTokenKind::Newline,
                LeekTokenKind::CloseCurlyBracket,
            ])?
            .kind
        {
            LeekTokenKind::Newline => children.push(terminal!(self.next_expect()?)),
            LeekTokenKind::CloseCurlyBracket => {}
            _ => unreachable!(),
        }

        Ok(ParseTreeNode::NonTerminal(ParseTreeNodeNonTerminal {
            kind: ParseTreeNonTerminalKind::Statement,
            children,
        }))
    }

    fn parse_yeet_statement(&mut self) -> Result<ParseTreeNode, LeekCompilerError> {
        let mut children = Vec::with_capacity(2);

        children.push(terminal!(
            self.next_expect_is(LeekTokenKind::Keyword(KeywordKind::Yeet))?
        ));
        self.bleed_whitespace()?;

        children.push(self.parse_expression()?);

        Ok(ParseTreeNode::NonTerminal(ParseTreeNodeNonTerminal {
            kind: ParseTreeNonTerminalKind::Yeet,
            children,
        }))
    }

    fn parse_local_variable_declaration(&mut self) -> Result<ParseTreeNode, LeekCompilerError> {
        let mut children = Vec::new();

        children.push(terminal!(
            self.next_expect_is(LeekTokenKind::Keyword(KeywordKind::Leak))?
        ));
        self.bleed_whitespace()?;

        children.push(terminal!(self.next_expect_is(LeekTokenKind::Identifier)?));
        self.bleed_whitespace()?;

        // Parse explicit type
        match self.peek_expect()?.kind {
            // No type def found
            LeekTokenKind::Equals => {}
            // Found type def
            LeekTokenKind::Colon => {
                children.push(terminal!(self.next_expect_is(LeekTokenKind::Colon)?));
                self.bleed_whitespace()?;

                todo!("parse explicit type in leak statement")
            }
            k => {
                return Err(self.create_error_with_span(
                    ParserErrorKind::UnexpectedToken {
                        expected: vec![LeekTokenKind::Colon, LeekTokenKind::Equals],
                        found: k,
                    },
                    self.peek_expect()?.span.clone(),
                ));
            }
        }

        children.push(terminal!(self.next_expect_is(LeekTokenKind::Equals)?));
        self.bleed_whitespace()?;

        children.push(self.parse_expression()?);

        Ok(ParseTreeNode::NonTerminal(ParseTreeNodeNonTerminal {
            kind: ParseTreeNonTerminalKind::LocalVariableDeclaration,
            children,
        }))
    }

    fn parse_variable_assignment(
        &mut self,
        identifier: ParseTreeNode,
        operator: LeekTokenKind,
    ) -> Result<ParseTreeNode, LeekCompilerError> {
        let mut children = Vec::new();

        children.push(identifier);
        self.bleed_whitespace()?;

        children.push(terminal!(self.next_expect_is(operator)?));
        self.bleed_whitespace()?;

        children.push(self.parse_expression()?);

        Ok(ParseTreeNode::NonTerminal(ParseTreeNodeNonTerminal {
            kind: ParseTreeNonTerminalKind::VariableAssignment,
            children,
        }))
    }

    /// Expression ::
    ///     Atom
    ///     | UnaryExpression
    ///     | FunctionCallExpression
    ///     | BinaryExpression
    ///     | StructInitialization
    ///     | StructFieldAccess
    ///     | StructMethodCall
    fn parse_expression(&mut self) -> Result<ParseTreeNode, LeekCompilerError> {
        let mut node = match self.peek_expect()?.kind {
            LeekTokenKind::OpenParen => self.parse_atom()?,
            LeekTokenKind::CharLiteral
            | LeekTokenKind::StringLiteral
            | LeekTokenKind::IntegerLiteral(_)
            | LeekTokenKind::FloatLiteral => self.parse_atom()?,
            k if k.is_unary_operator() => self.parse_unary_expression()?,
            LeekTokenKind::Identifier => {
                let identifier = self.parse_qualified_identifier()?;

                match self.peek_nth_ignore_whitespace_expect(0)?.kind {
                    LeekTokenKind::OpenParen => self.parse_function_call_expression(identifier)?,
                    LeekTokenKind::OpenCurlyBracket => {
                        self.parse_struct_initialization(identifier)?
                    }
                    _ => self.parse_atom_from_identifier(identifier)?,
                }
            }
            k => {
                return Err(self.create_error_with_span(
                    ParserErrorKind::UnexpectedToken {
                        expected: vec![
                            LeekTokenKind::OpenParen,
                            LeekTokenKind::CharLiteral,
                            LeekTokenKind::StringLiteral,
                            LeekTokenKind::IntegerLiteral(IntegerLiteralKind::Binary),
                            LeekTokenKind::IntegerLiteral(IntegerLiteralKind::Octal),
                            LeekTokenKind::IntegerLiteral(IntegerLiteralKind::Hexadecimal),
                            LeekTokenKind::IntegerLiteral(IntegerLiteralKind::Decimal),
                            LeekTokenKind::FloatLiteral,
                            LeekTokenKind::Identifier,
                        ],
                        found: k,
                    },
                    self.peek_expect()?.span.clone(),
                ));
            }
        };

        while self.peek_nth_ignore_whitespace_expect(0)?.kind == LeekTokenKind::Period {
            // Check to see if it is an indexable object
            match node.non_terminal().kind {
                ParseTreeNonTerminalKind::QualifiedIdentifier
                | ParseTreeNonTerminalKind::StructFieldAccess
                | ParseTreeNonTerminalKind::StructMethodCall
                | ParseTreeNonTerminalKind::Atom => {}

                _ => return Err(self.create_error(ParserErrorKind::IndexIntoNonIdentifier)),
            };

            // If the indexed object is an atom, make sure it is an identifier
            if let ParseTreeNonTerminalKind::Atom = node.non_terminal().kind {
                let atom_node = node.non_terminal();
                let first_child = atom_node
                    .children
                    .get(0)
                    .expect("Atom did not have any children");

                let ParseTreeNode::NonTerminal(child) = first_child else {
                    return Err(self.create_error(ParserErrorKind::IndexIntoNonIdentifier));
                };

                let ParseTreeNonTerminalKind::QualifiedIdentifier = child.kind else {
                    return Err(self.create_error(ParserErrorKind::IndexIntoNonIdentifier));

                };
            };

            node = match self.peek_nth_ignore_whitespace_expect(2)?.kind {
                LeekTokenKind::OpenParen => self.parse_struct_method_call(
                    ParseTreeNode::NonTerminal(ParseTreeNodeNonTerminal {
                        kind: ParseTreeNonTerminalKind::Expression,
                        children: vec![node],
                    }),
                )?,
                _ => self.parse_struct_field_access(ParseTreeNode::NonTerminal(
                    ParseTreeNodeNonTerminal {
                        kind: ParseTreeNonTerminalKind::Expression,
                        children: vec![node],
                    },
                ))?,
            }
        }

        if self
            .peek_nth_ignore_whitespace_expect(0)?
            .kind
            .is_binary_operator()
        {
            node = self.parse_binary_expression(ParseTreeNode::NonTerminal(
                ParseTreeNodeNonTerminal {
                    kind: ParseTreeNonTerminalKind::Expression,
                    children: vec![node],
                },
            ))?;
        }

        Ok(ParseTreeNode::NonTerminal(ParseTreeNodeNonTerminal {
            kind: ParseTreeNonTerminalKind::Expression,
            children: vec![node],
        }))
    }

    /// FunctionCallExpression ::
    ///     QualifiedIdentifier `(`
    ///         FunctionArguments?
    ///      `)`
    fn parse_function_call_expression(
        &mut self,
        identifier: ParseTreeNode,
    ) -> Result<ParseTreeNode, LeekCompilerError> {
        let mut children = Vec::new();

        children.push(identifier);
        self.bleed_whitespace()?;

        children.push(terminal!(self.next_expect_is(LeekTokenKind::OpenParen)?));
        self.bleed_whitespace()?;

        match self.peek_expect()?.kind {
            LeekTokenKind::CloseParen => {}
            _ => children.push(self.parse_function_arguments()?),
        }
        self.bleed_whitespace()?;

        children.push(terminal!(self.next_expect_is(LeekTokenKind::CloseParen)?));

        Ok(ParseTreeNode::NonTerminal(ParseTreeNodeNonTerminal {
            kind: ParseTreeNonTerminalKind::FunctionCallExpression,
            children,
        }))
    }

    /// FunctionArguments ::
    ///     (
    ///          (Expression `,`)* Expression
    ///     )
    fn parse_function_arguments(&mut self) -> Result<ParseTreeNode, LeekCompilerError> {
        let mut children = Vec::new();

        children.push(self.parse_expression()?);
        self.bleed_whitespace()?;

        while self.peek_expect_is(LeekTokenKind::Comma)? {
            children.push(terminal!(self.next_expect_is(LeekTokenKind::Comma)?));
            self.bleed_whitespace()?;
            children.push(self.parse_expression()?);
            self.bleed_whitespace()?;
        }

        Ok(ParseTreeNode::NonTerminal(ParseTreeNodeNonTerminal {
            kind: ParseTreeNonTerminalKind::FunctionArguments,
            children,
        }))
    }

    /// StructInitialization ::
    ///     QualifiedIdentifier `{`
    ///         (
    ///             identifier `:` Expression `\n`        
    ///         )*    
    ///     `}`
    fn parse_struct_initialization(
        &mut self,
        identifier: ParseTreeNode,
    ) -> Result<ParseTreeNode, LeekCompilerError> {
        let mut children = Vec::new();

        children.push(identifier);
        self.bleed_whitespace()?;

        children.push(terminal!(
            self.next_expect_is(LeekTokenKind::OpenCurlyBracket)?
        ));
        self.bleed_whitespace()?;

        while !self.peek_expect_is(LeekTokenKind::CloseCurlyBracket)? {
            children.push(terminal!(self.next_expect_is(LeekTokenKind::Identifier)?));
            self.bleed_whitespace()?;

            children.push(terminal!(self.next_expect_is(LeekTokenKind::Colon)?));
            self.bleed_whitespace()?;

            children.push(self.parse_expression()?);

            self.peek_expect_is_of(vec![
                LeekTokenKind::Newline,
                LeekTokenKind::CloseCurlyBracket,
            ])?;

            self.bleed_whitespace()?;
        }

        children.push(terminal!(
            self.next_expect_is(LeekTokenKind::CloseCurlyBracket)?
        ));

        Ok(ParseTreeNode::NonTerminal(ParseTreeNodeNonTerminal {
            kind: ParseTreeNonTerminalKind::StructInitialization,
            children,
        }))
    }

    /// BinaryExpression ::
    ///     Expression binary_operator Expression
    fn parse_binary_expression(
        &mut self,
        lhs: ParseTreeNode,
    ) -> Result<ParseTreeNode, LeekCompilerError> {
        let mut children = Vec::new();

        // TODO: Parse operator precedence (use a stack)

        // Left hand expression
        children.push(lhs);
        self.bleed_whitespace()?;

        // Binary operator
        children.push(terminal!(self.next_expect_is_of(vec![
            LeekTokenKind::DoubleEquals,
            LeekTokenKind::LessThan,
            LeekTokenKind::LessThanOrEqual,
            LeekTokenKind::GreaterThan,
            LeekTokenKind::GreaterThanOrEqual,
            LeekTokenKind::Plus,
            LeekTokenKind::Minus,
            LeekTokenKind::Asterisk,
            LeekTokenKind::Divide,
            LeekTokenKind::Modulo,
            LeekTokenKind::BitwiseXor,
            LeekTokenKind::BitwiseOr,
            LeekTokenKind::BitwiseAnd,
            LeekTokenKind::Exponentiation,
            LeekTokenKind::LeftShift,
            LeekTokenKind::RightShift,
            LeekTokenKind::LogicalOr,
            LeekTokenKind::LogicalAnd,
        ])?));
        self.bleed_whitespace()?;

        // Right hand expression
        children.push(self.parse_expression()?);

        Ok(ParseTreeNode::NonTerminal(ParseTreeNodeNonTerminal {
            kind: ParseTreeNonTerminalKind::BinaryExpression,
            children,
        }))
    }

    /// StructFieldAccess ::
    ///     Expression `.` identifier
    fn parse_struct_field_access(
        &mut self,
        lhs: ParseTreeNode,
    ) -> Result<ParseTreeNode, LeekCompilerError> {
        let mut children = Vec::new();

        // Left hand expression
        children.push(lhs);
        self.bleed_whitespace()?;

        // Dot operator
        children.push(terminal!(self.next_expect_is(LeekTokenKind::Period)?));
        self.bleed_whitespace()?;

        // Field
        children.push(terminal!(self.next_expect_is(LeekTokenKind::Identifier)?));

        Ok(ParseTreeNode::NonTerminal(ParseTreeNodeNonTerminal {
            kind: ParseTreeNonTerminalKind::StructFieldAccess,
            children,
        }))
    }

    /// StructMethodCall ::
    ///     Expression `.` FunctionCallExpression
    fn parse_struct_method_call(
        &mut self,
        lhs: ParseTreeNode,
    ) -> Result<ParseTreeNode, LeekCompilerError> {
        let mut children = Vec::new();

        // Left hand expression
        children.push(lhs);
        self.bleed_whitespace()?;

        // Dot operator
        children.push(terminal!(self.next_expect_is(LeekTokenKind::Period)?));
        self.bleed_whitespace()?;

        // Method
        let identifier = terminal!(self.next_expect_is(LeekTokenKind::Identifier)?);
        children.push(self.parse_function_call_expression(identifier)?);

        Ok(ParseTreeNode::NonTerminal(ParseTreeNodeNonTerminal {
            kind: ParseTreeNonTerminalKind::StructMethodCall,
            children,
        }))
    }

    /// UnaryExpression ::
    ///     unary_operator Expression  
    fn parse_unary_expression(&mut self) -> Result<ParseTreeNode, LeekCompilerError> {
        let mut children = Vec::new();

        // Unary operator
        children.push(terminal!(self.next_expect_is_of(vec![
            LeekTokenKind::BitwiseNot,
            LeekTokenKind::LogicalNot,
            LeekTokenKind::Asterisk
        ])?));
        self.bleed_whitespace()?;

        // Right hand expression
        children.push(self.parse_expression()?);

        Ok(ParseTreeNode::NonTerminal(ParseTreeNodeNonTerminal {
            kind: ParseTreeNonTerminalKind::UnaryExpression,
            children,
        }))
    }

    /// Atom ::
    ///     QualifiedIdentifier
    ///     | literal
    ///     | (
    ///         `(` Expression `)`
    ///       )
    fn parse_atom(&mut self) -> Result<ParseTreeNode, LeekCompilerError> {
        let mut children = Vec::new();

        match self.peek_expect()?.kind {
            LeekTokenKind::Identifier => {
                children.push(self.parse_qualified_identifier()?);
            }
            k if k.is_literal() => {
                children.push(terminal!(self.next_expect()?));
            }
            LeekTokenKind::OpenParen => {
                children.push(terminal!(self.next_expect_is(LeekTokenKind::OpenParen)?));
                self.bleed_whitespace()?;

                children.push(self.parse_expression()?);
                self.bleed_whitespace()?;

                children.push(terminal!(self.next_expect_is(LeekTokenKind::CloseParen)?));
            }
            k => {
                return Err(self.create_error_with_span(
                    ParserErrorKind::UnexpectedToken {
                        expected: vec![
                            LeekTokenKind::Identifier,
                            LeekTokenKind::OpenParen,
                            LeekTokenKind::CharLiteral,
                            LeekTokenKind::StringLiteral,
                            LeekTokenKind::IntegerLiteral(IntegerLiteralKind::Binary),
                            LeekTokenKind::IntegerLiteral(IntegerLiteralKind::Octal),
                            LeekTokenKind::IntegerLiteral(IntegerLiteralKind::Hexadecimal),
                            LeekTokenKind::IntegerLiteral(IntegerLiteralKind::Decimal),
                            LeekTokenKind::FloatLiteral,
                        ],
                        found: k,
                    },
                    self.peek_expect()?.span.clone(),
                ))
            }
        }

        Ok(ParseTreeNode::NonTerminal(ParseTreeNodeNonTerminal {
            kind: ParseTreeNonTerminalKind::Atom,
            children,
        }))
    }

    fn parse_atom_from_identifier(
        &mut self,
        node: ParseTreeNode,
    ) -> Result<ParseTreeNode, LeekCompilerError> {
        Ok(ParseTreeNode::NonTerminal(ParseTreeNodeNonTerminal {
            kind: ParseTreeNonTerminalKind::Atom,
            children: vec![node],
        }))
    }

    /// StructDefinition ::
    ///     `struct` identifier StructDefinitionBody?
    fn parse_struct_definition(&mut self) -> Result<ParseTreeNode, LeekCompilerError> {
        let mut children = Vec::new();

        children.push(terminal!(
            self.next_expect_is(LeekTokenKind::Keyword(KeywordKind::Struct))?
        ));
        self.bleed_whitespace()?;

        children.push(terminal!(self.next_expect_is(LeekTokenKind::Identifier)?));

        if self
            .peek_nth_ignore_whitespace(0)?
            .is_some_and(|token| token.kind == LeekTokenKind::OpenCurlyBracket)
        {
            self.bleed_whitespace()?;
            children.push(self.parse_struct_definition_body()?)
        } else if self.lexer.has_next()? {
            // If open bracket does not follow, must be None or newline
            children.push(terminal!(self.next_expect_is(LeekTokenKind::Newline)?));
        }

        Ok(ParseTreeNode::NonTerminal(ParseTreeNodeNonTerminal {
            kind: ParseTreeNonTerminalKind::StructDefinition,
            children,
        }))
    }

    /// StructDefinitionBody ::
    ///     `{`
    ///         (TypeAssociation `\n`)* TypeAssociation
    ///     `}`
    fn parse_struct_definition_body(&mut self) -> Result<ParseTreeNode, LeekCompilerError> {
        let mut children = Vec::new();

        children.push(terminal!(
            self.next_expect_is(LeekTokenKind::OpenCurlyBracket)?
        ));
        self.bleed_whitespace()?;

        if self.peek_nth_ignore_whitespace_expect(0)?.kind != LeekTokenKind::CloseCurlyBracket {
            // Non `}`, so parse at last one type association
            children.push(self.parse_type_association()?);

            while self.peek_expect_is(LeekTokenKind::Newline)? {
                self.bleed_whitespace()?;

                if self.peek_expect_is(LeekTokenKind::CloseCurlyBracket)? {
                    break;
                }

                children.push(self.parse_type_association()?);
            }
        }

        children.push(terminal!(
            self.next_expect_is(LeekTokenKind::CloseCurlyBracket)?
        ));

        Ok(ParseTreeNode::NonTerminal(ParseTreeNodeNonTerminal {
            kind: ParseTreeNonTerminalKind::StructDefinitionBody,
            children,
        }))
    }

    /// TypeAssociation ::
    ///     (identifier `:` Type)
    fn parse_type_association(&mut self) -> Result<ParseTreeNode, LeekCompilerError> {
        let mut children = Vec::new();

        children.push(terminal!(self.next_expect_is(LeekTokenKind::Identifier)?));
        self.bleed_whitespace()?;

        children.push(terminal!(self.next_expect_is(LeekTokenKind::Colon)?));
        self.bleed_whitespace()?;

        children.push(self.parse_type()?);

        Ok(ParseTreeNode::NonTerminal(ParseTreeNodeNonTerminal {
            kind: ParseTreeNonTerminalKind::TypeAssociation,
            children,
        }))
    }

    /// Type ::
    ///     QualifiedIdentifier
    fn parse_type(&mut self) -> Result<ParseTreeNode, LeekCompilerError> {
        let children = vec![self.parse_qualified_identifier()?];

        Ok(ParseTreeNode::NonTerminal(ParseTreeNodeNonTerminal {
            kind: ParseTreeNonTerminalKind::Type,
            children,
        }))
    }

    /// QualifiedIdentifier ::
    ///     identifier (`::` identifier)*
    fn parse_qualified_identifier(&mut self) -> Result<ParseTreeNode, LeekCompilerError> {
        let mut children = Vec::new();

        children.push(terminal!(self.next_expect_is(LeekTokenKind::Identifier)?));

        while self
            .peek_nth_ignore_whitespace(0)?
            .is_some_and(|token| token.kind == LeekTokenKind::DoubleColon)
        {
            self.bleed_whitespace()?;
            children.push(terminal!(self.next_expect_is(LeekTokenKind::DoubleColon)?));

            self.bleed_whitespace()?;
            children.push(terminal!(self.next_expect_is(LeekTokenKind::Identifier)?));
        }

        Ok(ParseTreeNode::NonTerminal(ParseTreeNodeNonTerminal {
            kind: ParseTreeNonTerminalKind::QualifiedIdentifier,
            children,
        }))
    }

    /// ConstantVariableDeclaration ::
    ///     `perm` identifier `:` Type `=` Expression
    fn parse_constant_variable_declaration(&mut self) -> Result<ParseTreeNode, LeekCompilerError> {
        let mut children = Vec::new();

        children.push(terminal!(
            self.next_expect_is(LeekTokenKind::Keyword(KeywordKind::Perm))?
        ));
        self.bleed_whitespace()?;

        children.push(terminal!(self.next_expect_is(LeekTokenKind::Identifier)?));
        self.bleed_whitespace()?;

        children.push(terminal!(self.next_expect_is(LeekTokenKind::Colon)?));
        self.bleed_whitespace()?;

        children.push(self.parse_type()?);
        self.bleed_whitespace()?;

        children.push(terminal!(self.next_expect_is(LeekTokenKind::Equals)?));
        self.bleed_whitespace()?;

        children.push(self.parse_expression()?);

        if self.lexer.has_next()? {
            children.push(terminal!(self.next_expect_is(LeekTokenKind::Newline)?));
        }

        Ok(ParseTreeNode::NonTerminal(ParseTreeNodeNonTerminal {
            kind: ParseTreeNonTerminalKind::ConstantVariableDeclaration,
            children,
        }))
    }

    /// StaticVariableDeclaration ::
    ///     `hold` identifier `:` Type `=` Expression
    fn parse_static_variable_declaration(&mut self) -> Result<ParseTreeNode, LeekCompilerError> {
        let mut children = Vec::new();

        children.push(terminal!(
            self.next_expect_is(LeekTokenKind::Keyword(KeywordKind::Hold))?
        ));
        self.bleed_whitespace()?;

        children.push(terminal!(self.next_expect_is(LeekTokenKind::Identifier)?));
        self.bleed_whitespace()?;

        children.push(terminal!(self.next_expect_is(LeekTokenKind::Colon)?));
        self.bleed_whitespace()?;

        children.push(self.parse_type()?);
        self.bleed_whitespace()?;

        children.push(terminal!(self.next_expect_is(LeekTokenKind::Equals)?));
        self.bleed_whitespace()?;

        children.push(self.parse_expression()?);

        if self.lexer.has_next()? {
            children.push(terminal!(self.next_expect_is(LeekTokenKind::Newline)?));
        }

        Ok(ParseTreeNode::NonTerminal(ParseTreeNodeNonTerminal {
            kind: ParseTreeNonTerminalKind::StaticVariableDeclaration,
            children,
        }))
    }

    /// Internal method to parse all the tokens from the internal lexer
    fn parse_from_lexer(&mut self) -> Result<ParseTree, LeekCompilerError> {
        let mut children = Vec::new();

        self.bleed_whitespace()?;

        while self.lexer.has_next()? {
            children.push(self.parse_program_part()?);

            self.bleed_whitespace()?;
        }

        let root = ParseTreeNode::NonTerminal(ParseTreeNodeNonTerminal {
            kind: ParseTreeNonTerminalKind::Program,
            children,
        });

        Ok(ParseTree {
            root,
            source_file: self.lexer.get_source_file().clone(),
        })
    }
}

#[cfg(test)]
mod test {
    use ansi_term::Color;

    use crate::{
        frontend::lexer::{IntegerLiteralKind, KeywordKind, LeekLexer, LeekToken, LeekTokenKind},
        frontend::reader::FileReader,
    };

    use super::{
        LeekParser, ParseTreeNode, ParseTreeNodeNonTerminal, ParseTreeNonTerminalKind, Parser,
    };

    fn compare_input_to_expected(input: &str, expected_tree: ParseTreeNode) {
        // Collect tokens from lexer
        let reader = FileReader::from(input.to_owned());
        let lexer = LeekLexer::new(reader);
        let parse_tree =
            LeekParser::parse(lexer).unwrap_or_else(|e| panic!("Could not parse input: \n{e}"));

        if parse_tree.root == expected_tree {
            return;
        }

        let mut output = String::new();

        for diff in diff::lines(&format!("{expected_tree}"), &format!("{}", parse_tree.root)) {
            match diff {
                diff::Result::Left(l) => {
                    output.push_str(&format!("{}", Color::Red.paint(format!("-{}\n", l))))
                }
                diff::Result::Both(l, _) => output.push_str(&format!(" {}\n", l)),
                diff::Result::Right(r) => {
                    output.push_str(&format!("{}", Color::Green.paint(format!("+{}\n", r))))
                }
            }
        }

        panic!("Parse tree did not match expected: \n{output}");
    }

    macro_rules! terminal_from {
        ($kind:expr, $text:literal) => {
            ParseTreeNode::Terminal(LeekToken::from(($kind, $text)))
        };
    }

    #[test]
    fn basic_program() {
        compare_input_to_expected(
            r#"
            perm PI: f32 = 3.1415926535
            perm E: f32 = 2.178
            perm THREE: u8 = 0x03
            
            hold state: u8 = 0b0001

            fn main() {
                leak a = 1
                leak b = 2 
                leak node = Node("text")
            
                println(a)  
            }
            "#,
            non_terminal!(
                ParseTreeNonTerminalKind::Program,
                vec![
                    non_terminal!(
                        ParseTreeNonTerminalKind::ConstantVariableDeclaration,
                        vec![
                            terminal_from!(LeekTokenKind::Keyword(KeywordKind::Perm), "perm"),
                            terminal_from!(LeekTokenKind::Identifier, "PI"),
                            terminal_from!(LeekTokenKind::Colon, ":"),
                            non_terminal!(
                                ParseTreeNonTerminalKind::Type,
                                vec![non_terminal!(
                                    ParseTreeNonTerminalKind::QualifiedIdentifier,
                                    vec![
                                        terminal_from!(LeekTokenKind::Identifier, "f32"),
                                    ]
                                )]
                            ),
                            terminal_from!(LeekTokenKind::Equals, "="),
                            non_terminal!(
                                ParseTreeNonTerminalKind::Expression,
                                vec![non_terminal!(
                                    ParseTreeNonTerminalKind::Atom,
                                    vec![terminal_from!(
                                        LeekTokenKind::FloatLiteral,
                                        "3.1415926535"
                                    ),]
                                ),]
                            ),
                            terminal_from!(LeekTokenKind::Newline, "\n"),
                        ]
                    ),
                    non_terminal!(
                        ParseTreeNonTerminalKind::ConstantVariableDeclaration,
                        vec![
                            terminal_from!(LeekTokenKind::Keyword(KeywordKind::Perm), "perm"),
                            terminal_from!(LeekTokenKind::Identifier, "E"),
                            terminal_from!(LeekTokenKind::Colon, ":"),
                            non_terminal!(
                                ParseTreeNonTerminalKind::Type,
                                vec![non_terminal!(
                                    ParseTreeNonTerminalKind::QualifiedIdentifier,
                                    vec![
                                        terminal_from!(LeekTokenKind::Identifier, "f32"),
                                    ]
                                )]
                            ),
                            terminal_from!(LeekTokenKind::Equals, "="),
                            non_terminal!(
                                ParseTreeNonTerminalKind::Expression,
                                vec![non_terminal!(
                                    ParseTreeNonTerminalKind::Atom,
                                    vec![terminal_from!(LeekTokenKind::FloatLiteral, "2.178"),]
                                ),]
                            ),
                            terminal_from!(LeekTokenKind::Newline, "\n"),
                        ]
                    ),
                    non_terminal!(
                        ParseTreeNonTerminalKind::ConstantVariableDeclaration,
                        vec![
                            terminal_from!(LeekTokenKind::Keyword(KeywordKind::Perm), "perm"),
                            terminal_from!(LeekTokenKind::Identifier, "THREE"),
                            terminal_from!(LeekTokenKind::Colon, ":"),
                            non_terminal!(
                                ParseTreeNonTerminalKind::Type,
                                vec![non_terminal!(
                                    ParseTreeNonTerminalKind::QualifiedIdentifier,
                                    vec![
                                        terminal_from!(LeekTokenKind::Identifier, "u8"),
                                    ]
                                )]
                            ),
                            terminal_from!(LeekTokenKind::Equals, "="),
                            non_terminal!(
                                ParseTreeNonTerminalKind::Expression,
                                vec![non_terminal!(
                                    ParseTreeNonTerminalKind::Atom,
                                    vec![terminal_from!(
                                        LeekTokenKind::IntegerLiteral(
                                            IntegerLiteralKind::Hexadecimal
                                        ),
                                        "0x03"
                                    ),]
                                ),]
                            ),
                            terminal_from!(LeekTokenKind::Newline, "\n"),
                        ]
                    ),
                    non_terminal!(
                        ParseTreeNonTerminalKind::StaticVariableDeclaration,
                        vec![
                            terminal_from!(LeekTokenKind::Keyword(KeywordKind::Hold), "hold"),
                            terminal_from!(LeekTokenKind::Identifier, "state"),
                            terminal_from!(LeekTokenKind::Colon, ":"),
                            non_terminal!(
                                ParseTreeNonTerminalKind::Type,
                                vec![non_terminal!(
                                    ParseTreeNonTerminalKind::QualifiedIdentifier,
                                    vec![
                                        terminal_from!(LeekTokenKind::Identifier, "u8"),
                                    ]
                                )]
                            ),
                            terminal_from!(LeekTokenKind::Equals, "="),
                            non_terminal!(
                                ParseTreeNonTerminalKind::Expression,
                                vec![non_terminal!(
                                    ParseTreeNonTerminalKind::Atom,
                                    vec![terminal_from!(
                                        LeekTokenKind::IntegerLiteral(IntegerLiteralKind::Binary),
                                        "0b0001"
                                    ),]
                                ),]
                            ),
                            terminal_from!(LeekTokenKind::Newline, "\n"),
                        ]
                    ),
                    non_terminal!(
                        ParseTreeNonTerminalKind::FunctionDefinition,
                        vec![
                            terminal_from!(LeekTokenKind::Keyword(KeywordKind::Fn), "fn"),
                            non_terminal!(
                                ParseTreeNonTerminalKind::QualifiedIdentifier,
                                vec![
                                    terminal_from!(LeekTokenKind::Identifier, "main"),
                                ]
                            ),
                            non_terminal!(
                                ParseTreeNonTerminalKind::FunctionParameters,
                                vec![
                                    terminal_from!(LeekTokenKind::OpenParen, "("),
                                    terminal_from!(LeekTokenKind::CloseParen, ")"),
                                ]
                            ),
                            non_terminal!(
                                ParseTreeNonTerminalKind::Block,
                                vec![
                                    terminal_from!(LeekTokenKind::OpenCurlyBracket, "{"),
                                    non_terminal!(
                                        ParseTreeNonTerminalKind::Statement,
                                        vec![
                                            non_terminal!(
                                                ParseTreeNonTerminalKind::LocalVariableDeclaration,
                                                vec![
                                                    terminal_from!(
                                                        LeekTokenKind::Keyword(KeywordKind::Leak),
                                                        "leak"
                                                    ),
                                                    terminal_from!(LeekTokenKind::Identifier, "a"),
                                                    terminal_from!(LeekTokenKind::Equals, "="),
                                                    non_terminal!(
                                                        ParseTreeNonTerminalKind::Expression,
                                                        vec![non_terminal!(
                                                            ParseTreeNonTerminalKind::Atom,
                                                            vec![terminal_from!(
                                                                LeekTokenKind::IntegerLiteral(
                                                                    IntegerLiteralKind::Decimal
                                                                ),
                                                                "1"
                                                            ),]
                                                        ),]
                                                    ),
                                                ]
                                            ),
                                            terminal_from!(LeekTokenKind::Newline, "\n"),
                                        ]
                                    ),
                                    non_terminal!(
                                        ParseTreeNonTerminalKind::Statement,
                                        vec![
                                            non_terminal!(
                                                ParseTreeNonTerminalKind::LocalVariableDeclaration,
                                                vec![
                                                    terminal_from!(
                                                        LeekTokenKind::Keyword(KeywordKind::Leak),
                                                        "leak"
                                                    ),
                                                    terminal_from!(LeekTokenKind::Identifier, "b"),
                                                    terminal_from!(LeekTokenKind::Equals, "="),
                                                    non_terminal!(
                                                        ParseTreeNonTerminalKind::Expression,
                                                        vec![non_terminal!(
                                                            ParseTreeNonTerminalKind::Atom,
                                                            vec![terminal_from!(
                                                                LeekTokenKind::IntegerLiteral(
                                                                    IntegerLiteralKind::Decimal
                                                                ),
                                                                "2"
                                                            ),]
                                                        ),]
                                                    ),
                                                ]
                                            ),
                                            terminal_from!(LeekTokenKind::Newline, "\n"),
                                        ]
                                    ),
                                    non_terminal!(
                                        ParseTreeNonTerminalKind::Statement,
                                        vec![
                                            non_terminal!(
                                                ParseTreeNonTerminalKind::LocalVariableDeclaration,
                                                vec![
                                                    terminal_from!(
                                                        LeekTokenKind::Keyword(KeywordKind::Leak),
                                                        "leak"
                                                    ),
                                                    terminal_from!(LeekTokenKind::Identifier, "node"),
                                                    terminal_from!(LeekTokenKind::Equals, "="),
                                                    non_terminal!(
                                                        ParseTreeNonTerminalKind::Expression,
                                                        vec![non_terminal!(
                                                        ParseTreeNonTerminalKind::FunctionCallExpression,
                                                        vec![
                                                            non_terminal!(
                                                                ParseTreeNonTerminalKind::QualifiedIdentifier,
                                                                vec![
                                                                    terminal_from!(LeekTokenKind::Identifier, "Node"),
                                                                ]
                                                            ),
                                                            terminal_from!(LeekTokenKind::OpenParen, "("),
                                                            non_terminal!(
                                                                ParseTreeNonTerminalKind::FunctionArguments,
                                                                vec![non_terminal!(
                                                                    ParseTreeNonTerminalKind::Expression,
                                                                    vec![non_terminal!(
                                                                        ParseTreeNonTerminalKind::Atom,
                                                                        vec![terminal_from!(
                                                                            LeekTokenKind::StringLiteral,
                                                                            "\"text\""
                                                                        ),]
                                                                    ),]
                                                                ),]
                                                            ),
                                                            terminal_from!(LeekTokenKind::CloseParen, ")"),
                                                        ]
                                                    ),]
                                                    ),
                                                ]
                                            ),
                                            terminal_from!(LeekTokenKind::Newline, "\n"),
                                        ]
                                    ),
                                    non_terminal!(
                                        ParseTreeNonTerminalKind::Statement,
                                        vec![
                                            non_terminal!(
                                                ParseTreeNonTerminalKind::FunctionCallExpression,
                                                vec![
                                                    non_terminal!(
                                                        ParseTreeNonTerminalKind::QualifiedIdentifier,
                                                        vec![
                                                            terminal_from!(LeekTokenKind::Identifier, "println"),
                                                        ]
                                                    ),
                                                    terminal_from!(LeekTokenKind::OpenParen, "("),
                                                    non_terminal!(
                                                        ParseTreeNonTerminalKind::FunctionArguments,
                                                        vec![non_terminal!(
                                                            ParseTreeNonTerminalKind::Expression,
                                                            vec![non_terminal!(
                                                                ParseTreeNonTerminalKind::Atom,
                                                                vec![
                                                                    non_terminal!(
                                                                        ParseTreeNonTerminalKind::QualifiedIdentifier,
                                                                        vec![
                                                                            terminal_from!(LeekTokenKind::Identifier, "a"),
                                                                        ]
                                                                    )
                                                                ]
                                                            ),]
                                                        ),]
                                                    ),
                                                    terminal_from!(LeekTokenKind::CloseParen, ")"),
                                                ]
                                            ),
                                            terminal_from!(LeekTokenKind::Newline, "\n"),
                                        ]
                                    ),
                                    terminal_from!(LeekTokenKind::CloseCurlyBracket, "}"),
                                ]
                            ),
                        ]
                    ),
                ]
            ),
        )
    }

    #[test]
    fn parse_structs() {
        compare_input_to_expected(
            r#"
            struct EmptyStruct 

            struct SomeStruct {
            
            }
            
            struct BinaryTreeNode {
                left: BinaryTreeNode
                right: BinaryTreeNode
                data: i32
            }
            "#,
            non_terminal!(
                ParseTreeNonTerminalKind::Program,
                vec![
                    non_terminal!(
                        ParseTreeNonTerminalKind::StructDefinition,
                        vec![
                            terminal_from!(LeekTokenKind::Keyword(KeywordKind::Struct), "struct"),
                            terminal_from!(LeekTokenKind::Identifier, "EmptyStruct"),
                            terminal_from!(LeekTokenKind::Newline, "\n"),
                        ]
                    ),
                    non_terminal!(
                        ParseTreeNonTerminalKind::StructDefinition,
                        vec![
                            terminal_from!(LeekTokenKind::Keyword(KeywordKind::Struct), "struct"),
                            terminal_from!(LeekTokenKind::Identifier, "SomeStruct"),
                            non_terminal!(
                                ParseTreeNonTerminalKind::StructDefinitionBody,
                                vec![
                                    terminal_from!(LeekTokenKind::OpenCurlyBracket, "{"),
                                    terminal_from!(LeekTokenKind::CloseCurlyBracket, "}"),
                                ]
                            )
                        ]
                    ),
                    non_terminal!(
                        ParseTreeNonTerminalKind::StructDefinition,
                        vec![
                            terminal_from!(LeekTokenKind::Keyword(KeywordKind::Struct), "struct"),
                            terminal_from!(LeekTokenKind::Identifier, "BinaryTreeNode"),
                            non_terminal!(
                                ParseTreeNonTerminalKind::StructDefinitionBody,
                                vec![
                                    terminal_from!(LeekTokenKind::OpenCurlyBracket, "{"),
                                    non_terminal!(
                                        ParseTreeNonTerminalKind::TypeAssociation,
                                        vec![
                                            terminal_from!(LeekTokenKind::Identifier, "left"),
                                            terminal_from!(LeekTokenKind::Colon, ":"),
                                            non_terminal!(
                                                ParseTreeNonTerminalKind::Type,
                                                vec![non_terminal!(
                                                    ParseTreeNonTerminalKind::QualifiedIdentifier,
                                                    vec![terminal_from!(
                                                        LeekTokenKind::Identifier,
                                                        "BinaryTreeNode"
                                                    ),]
                                                )]
                                            ),
                                        ]
                                    ),
                                    non_terminal!(
                                        ParseTreeNonTerminalKind::TypeAssociation,
                                        vec![
                                            terminal_from!(LeekTokenKind::Identifier, "right"),
                                            terminal_from!(LeekTokenKind::Colon, ":"),
                                            non_terminal!(
                                                ParseTreeNonTerminalKind::Type,
                                                vec![non_terminal!(
                                                    ParseTreeNonTerminalKind::QualifiedIdentifier,
                                                    vec![terminal_from!(
                                                        LeekTokenKind::Identifier,
                                                        "BinaryTreeNode"
                                                    ),]
                                                )]
                                            ),
                                        ]
                                    ),
                                    non_terminal!(
                                        ParseTreeNonTerminalKind::TypeAssociation,
                                        vec![
                                            terminal_from!(LeekTokenKind::Identifier, "data"),
                                            terminal_from!(LeekTokenKind::Colon, ":"),
                                            non_terminal!(
                                                ParseTreeNonTerminalKind::Type,
                                                vec![non_terminal!(
                                                    ParseTreeNonTerminalKind::QualifiedIdentifier,
                                                    vec![terminal_from!(
                                                        LeekTokenKind::Identifier,
                                                        "i32"
                                                    ),]
                                                )]
                                            ),
                                        ]
                                    ),
                                    terminal_from!(LeekTokenKind::CloseCurlyBracket, "}"),
                                ]
                            )
                        ]
                    ),
                ]
            ),
        )
    }
}
