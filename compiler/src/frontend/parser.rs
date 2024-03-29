use core::panic;
use std::fmt::Display;

use crate::{
    common::error::CompilerError,
    frontend::lexer::{
        token::{IntegerLiteralKind, KeywordKind, Token, TokenKind},
        Lexer,
    },
    frontend::position::{highlight_span, SourceFile, Span},
};

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
    Terminal(Token),
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

    pub fn terminal_token(&self) -> &Token {
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
            ),
            ParserErrorKind::UnexpectedKeyword { expected, found } => writeln!(
                f,
                "Unexpected keyword {:?}. Expected one of: {:?}",
                found, expected
            ),
            ParserErrorKind::UnexpectedEndOfInput => writeln!(f, "Unexpected end of input."),
            ParserErrorKind::IndexIntoNonIdentifier => {
                writeln!(f, "Cannot access field of non-struct object.")
            }
        }?;

        highlight_span(f, &self.source_file, self.span.clone())?;

        Ok(())
    }
}

#[derive(Debug)]
pub enum ParserErrorKind {
    UnexpectedToken {
        expected: Vec<TokenKind>,
        found: TokenKind,
    },
    UnexpectedKeyword {
        expected: Vec<KeywordKind>,
        found: KeywordKind,
    },
    UnexpectedEndOfInput,
    IndexIntoNonIdentifier,
}

pub struct Parser {
    lexer: Lexer,
}

impl Parser {
    pub fn parse(lexer: Lexer) -> Result<ParseTree, CompilerError> {
        let mut parser = Parser { lexer };

        parser.parse_from_lexer()
    }

    /// Peeks the next token or returns an error if there are none left
    fn peek_expect(&self) -> Result<&Token, CompilerError> {
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
    fn peek_expect_is(&self, kind: TokenKind) -> Result<bool, CompilerError> {
        let token = self.peek_expect()?;

        Ok(token.kind == kind)
    }

    /// Peeks the nth token or returns an error if there are none left
    #[allow(unused)]
    fn peek_nth_expect(&self, n: usize) -> Result<&Token, CompilerError> {
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
    fn peek_expect_is_of(&self, kinds: Vec<TokenKind>) -> Result<&Token, CompilerError> {
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
    fn peek_nth_ignore_whitespace(&self, n: usize) -> Result<Option<&Token>, CompilerError> {
        let mut peek_index = 0;
        let mut non_nl_tokens = 0;

        while self.lexer.has_next()? {
            let Some(peeked) = self.lexer.peek_nth(peek_index)? else {
                return Ok(None);
            };

            match peeked.kind {
                TokenKind::Newline => {
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
    fn peek_nth_ignore_whitespace_expect(&self, n: usize) -> Result<&Token, CompilerError> {
        self.peek_nth_ignore_whitespace(n)?
            .ok_or_else(|| self.create_error(ParserErrorKind::UnexpectedEndOfInput))
    }

    /// Ignores tokens while they are new lines
    fn bleed_whitespace(&mut self) -> Result<(), CompilerError> {
        while self
            .lexer
            .peek()?
            .is_some_and(|t| t.kind == TokenKind::Newline)
        {
            self.lexer.next()?;
        }

        Ok(())
    }

    /// Grabs the next token or throws an error if none were found
    fn next_expect(&mut self) -> Result<Token, CompilerError> {
        self.lexer
            .next()?
            .ok_or_else(|| self.create_error(ParserErrorKind::UnexpectedEndOfInput))
    }

    /// Grabs the next token and asserts that it is the provided type
    fn next_expect_is(&mut self, kind: TokenKind) -> Result<Token, CompilerError> {
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
    fn next_expect_is_of(&mut self, kinds: Vec<TokenKind>) -> Result<Token, CompilerError> {
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
    fn create_error(&self, kind: ParserErrorKind) -> CompilerError {
        ParserError {
            kind,
            source_file: self.lexer.get_source_file().clone(),
            span: Span::from(self.lexer.get_position()),
        }
        .into()
    }

    /// Creates the associated error variant from a span
    fn create_error_with_span(&self, kind: ParserErrorKind, span: Span) -> CompilerError {
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
    fn parse_program_part(&mut self) -> Result<ParseTreeNode, CompilerError> {
        let peeked_token = self.peek_expect()?;

        match peeked_token.kind {
            // FunctionDefinition or FunctionDeclaration
            TokenKind::Keyword(KeywordKind::Fn) => self.parse_function_declaration_or_definition(),
            // StructDefinition
            TokenKind::Keyword(KeywordKind::Struct) => self.parse_struct_definition(),
            // ConstantVariableDeclaration
            TokenKind::Keyword(KeywordKind::Perm) => self.parse_constant_variable_declaration(),
            // StaticVariableDeclaration
            TokenKind::Keyword(KeywordKind::Hold) => self.parse_static_variable_declaration(),
            // Unexpected keyword
            TokenKind::Keyword(kw) => Err(self.create_error_with_span(
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
                        TokenKind::Keyword(KeywordKind::Fn),
                        TokenKind::Keyword(KeywordKind::Struct),
                        TokenKind::Keyword(KeywordKind::Perm),
                        TokenKind::Keyword(KeywordKind::Hold),
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
    fn parse_function_declaration_or_definition(&mut self) -> Result<ParseTreeNode, CompilerError> {
        let mut children = Vec::new();

        children.push(terminal!(
            self.next_expect_is(TokenKind::Keyword(KeywordKind::Fn))?
        ));
        self.bleed_whitespace()?;

        children.push(self.parse_qualified_identifier()?);
        self.bleed_whitespace()?;

        children.push(self.parse_function_parameters()?);

        if self
            .peek_nth_ignore_whitespace(0)?
            .is_some_and(|token| token.kind == TokenKind::Arrow)
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
    fn parse_return_type(&mut self) -> Result<ParseTreeNode, CompilerError> {
        let children = vec![
            terminal!(self.next_expect_is(TokenKind::Arrow)?),
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
    fn parse_function_parameters(&mut self) -> Result<ParseTreeNode, CompilerError> {
        let mut children = Vec::new();

        children.push(terminal!(self.next_expect_is(TokenKind::OpenParen)?));
        self.bleed_whitespace()?;

        match self.peek_expect()?.kind {
            TokenKind::CloseParen => {}
            _ => {
                children.push(self.parse_type_association()?);
                self.bleed_whitespace()?;

                while self.peek_expect_is(TokenKind::Comma)? {
                    children.push(terminal!(self.next_expect_is(TokenKind::Comma)?));
                    self.bleed_whitespace()?;
                    children.push(self.parse_type_association()?);
                    self.bleed_whitespace()?;
                }
            }
        }
        self.bleed_whitespace()?;

        children.push(terminal!(self.next_expect_is(TokenKind::CloseParen)?));

        Ok(ParseTreeNode::NonTerminal(ParseTreeNodeNonTerminal {
            kind: ParseTreeNonTerminalKind::FunctionParameters,
            children,
        }))
    }

    /// Block ::
    ///     `{`
    ///         (Block | Statement)*
    ///     `}`
    fn parse_block(&mut self) -> Result<ParseTreeNode, CompilerError> {
        let mut children = Vec::new();

        children.push(terminal!(self.next_expect_is(TokenKind::OpenCurlyBracket)?));
        self.bleed_whitespace()?;

        while self.lexer.has_next()? {
            let token = self.lexer.peek()?.unwrap();

            match token.kind {
                // Ignore preceding newlines
                TokenKind::Newline => {
                    self.lexer.next()?;
                }
                // Allow recursive blocks
                TokenKind::OpenCurlyBracket => children.push(self.parse_block()?),
                // Break the loop if a closing bracket is found
                TokenKind::CloseCurlyBracket => break,

                _ => children.push(self.parse_statement()?),
            }
        }

        children.push(terminal!(self.next_expect_is(TokenKind::CloseCurlyBracket)?));
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
    fn parse_statement(&mut self) -> Result<ParseTreeNode, CompilerError> {
        let mut children = Vec::new();

        match self.peek_expect()?.kind {
            TokenKind::Keyword(KeywordKind::Yeet) => {
                children.push(self.parse_yeet_statement()?);
            }
            TokenKind::Keyword(KeywordKind::Leak) => {
                children.push(self.parse_local_variable_declaration()?);
            }
            k @ TokenKind::Identifier => {
                let identifier = self.parse_qualified_identifier()?;

                // Could be assignment or function call
                match self.peek_nth_ignore_whitespace_expect(0)?.kind {
                    TokenKind::OpenParen => {
                        children.push(self.parse_function_call_expression(identifier)?)
                    }
                    k if k.is_assignment_operator() => {
                        children.push(self.parse_variable_assignment(identifier, k)?);
                    }
                    _ => {
                        return Err(self.create_error(ParserErrorKind::UnexpectedToken {
                            expected: vec![
                                TokenKind::OpenParen,
                                TokenKind::Equals,
                                TokenKind::PlusEquals,
                                TokenKind::MinusEquals,
                                TokenKind::MultiplyEquals,
                                TokenKind::DivideEquals,
                                TokenKind::ModuloEquals,
                                TokenKind::BitwiseNotEquals,
                                TokenKind::BitwiseXorEquals,
                                TokenKind::BitwiseOrEquals,
                                TokenKind::BitwiseAndEquals,
                                TokenKind::LogicalNotEquals,
                                TokenKind::ExponentiationEquals,
                                TokenKind::LeftShiftEquals,
                                TokenKind::RightShiftEquals,
                                TokenKind::LogicalOrEquals,
                                TokenKind::LogicalAndEquals,
                            ],
                            found: k,
                        }));
                    }
                }
            }
            k => {
                return Err(self.create_error(ParserErrorKind::UnexpectedToken {
                    expected: vec![
                        TokenKind::Keyword(KeywordKind::Yeet),
                        TokenKind::Keyword(KeywordKind::Leak),
                        TokenKind::Identifier,
                    ],
                    found: k,
                }));
            }
        }

        match self
            .peek_expect_is_of(vec![TokenKind::Newline, TokenKind::CloseCurlyBracket])?
            .kind
        {
            TokenKind::Newline => children.push(terminal!(self.next_expect()?)),
            TokenKind::CloseCurlyBracket => {}
            _ => unreachable!(),
        }

        Ok(ParseTreeNode::NonTerminal(ParseTreeNodeNonTerminal {
            kind: ParseTreeNonTerminalKind::Statement,
            children,
        }))
    }

    fn parse_yeet_statement(&mut self) -> Result<ParseTreeNode, CompilerError> {
        let mut children = Vec::with_capacity(2);

        children.push(terminal!(
            self.next_expect_is(TokenKind::Keyword(KeywordKind::Yeet))?
        ));
        self.bleed_whitespace()?;

        children.push(self.parse_expression()?);

        Ok(ParseTreeNode::NonTerminal(ParseTreeNodeNonTerminal {
            kind: ParseTreeNonTerminalKind::Yeet,
            children,
        }))
    }

    fn parse_local_variable_declaration(&mut self) -> Result<ParseTreeNode, CompilerError> {
        let mut children = Vec::new();

        children.push(terminal!(
            self.next_expect_is(TokenKind::Keyword(KeywordKind::Leak))?
        ));
        self.bleed_whitespace()?;

        children.push(terminal!(self.next_expect_is(TokenKind::Identifier)?));
        self.bleed_whitespace()?;

        // Parse explicit type
        match self.peek_expect()?.kind {
            // No type def found
            TokenKind::Equals => {}
            // Found type def
            TokenKind::Colon => {
                children.push(terminal!(self.next_expect_is(TokenKind::Colon)?));
                self.bleed_whitespace()?;

                todo!("parse explicit type in leak statement")
            }
            k => {
                return Err(self.create_error_with_span(
                    ParserErrorKind::UnexpectedToken {
                        expected: vec![TokenKind::Colon, TokenKind::Equals],
                        found: k,
                    },
                    self.peek_expect()?.span.clone(),
                ));
            }
        }

        children.push(terminal!(self.next_expect_is(TokenKind::Equals)?));
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
        operator: TokenKind,
    ) -> Result<ParseTreeNode, CompilerError> {
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
    fn parse_expression(&mut self) -> Result<ParseTreeNode, CompilerError> {
        let mut node = match self.peek_expect()?.kind {
            TokenKind::OpenParen => self.parse_atom()?,
            TokenKind::CharLiteral
            | TokenKind::StringLiteral
            | TokenKind::IntegerLiteral(_)
            | TokenKind::FloatLiteral => self.parse_atom()?,
            k if k.is_unary_operator() => self.parse_unary_expression()?,
            TokenKind::Identifier => {
                let identifier = self.parse_qualified_identifier()?;

                match self.peek_nth_ignore_whitespace_expect(0)?.kind {
                    TokenKind::OpenParen => self.parse_function_call_expression(identifier)?,
                    TokenKind::OpenCurlyBracket => self.parse_struct_initialization(identifier)?,
                    _ => self.parse_atom_from_identifier(identifier)?,
                }
            }
            k => {
                return Err(self.create_error_with_span(
                    ParserErrorKind::UnexpectedToken {
                        expected: vec![
                            TokenKind::OpenParen,
                            TokenKind::CharLiteral,
                            TokenKind::StringLiteral,
                            TokenKind::IntegerLiteral(IntegerLiteralKind::Binary),
                            TokenKind::IntegerLiteral(IntegerLiteralKind::Octal),
                            TokenKind::IntegerLiteral(IntegerLiteralKind::Hexadecimal),
                            TokenKind::IntegerLiteral(IntegerLiteralKind::Decimal),
                            TokenKind::FloatLiteral,
                            TokenKind::Identifier,
                        ],
                        found: k,
                    },
                    self.peek_expect()?.span.clone(),
                ));
            }
        };

        while self.peek_nth_ignore_whitespace_expect(0)?.kind == TokenKind::Period {
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
                TokenKind::OpenParen => self.parse_struct_method_call(
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
    ) -> Result<ParseTreeNode, CompilerError> {
        let mut children = Vec::new();

        children.push(identifier);
        self.bleed_whitespace()?;

        children.push(terminal!(self.next_expect_is(TokenKind::OpenParen)?));
        self.bleed_whitespace()?;

        match self.peek_expect()?.kind {
            TokenKind::CloseParen => {}
            _ => children.push(self.parse_function_arguments()?),
        }
        self.bleed_whitespace()?;

        children.push(terminal!(self.next_expect_is(TokenKind::CloseParen)?));

        Ok(ParseTreeNode::NonTerminal(ParseTreeNodeNonTerminal {
            kind: ParseTreeNonTerminalKind::FunctionCallExpression,
            children,
        }))
    }

    /// FunctionArguments ::
    ///     (
    ///          (Expression `,`)* Expression
    ///     )
    fn parse_function_arguments(&mut self) -> Result<ParseTreeNode, CompilerError> {
        let mut children = Vec::new();

        children.push(self.parse_expression()?);
        self.bleed_whitespace()?;

        while self.peek_expect_is(TokenKind::Comma)? {
            children.push(terminal!(self.next_expect_is(TokenKind::Comma)?));
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
    ) -> Result<ParseTreeNode, CompilerError> {
        let mut children = Vec::new();

        children.push(identifier);
        self.bleed_whitespace()?;

        children.push(terminal!(self.next_expect_is(TokenKind::OpenCurlyBracket)?));
        self.bleed_whitespace()?;

        while !self.peek_expect_is(TokenKind::CloseCurlyBracket)? {
            children.push(terminal!(self.next_expect_is(TokenKind::Identifier)?));
            self.bleed_whitespace()?;

            children.push(terminal!(self.next_expect_is(TokenKind::Colon)?));
            self.bleed_whitespace()?;

            children.push(self.parse_expression()?);

            self.peek_expect_is_of(vec![TokenKind::Newline, TokenKind::CloseCurlyBracket])?;

            self.bleed_whitespace()?;
        }

        children.push(terminal!(self.next_expect_is(TokenKind::CloseCurlyBracket)?));

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
    ) -> Result<ParseTreeNode, CompilerError> {
        let mut children = Vec::new();

        // TODO: Parse operator precedence (use a stack)

        // Left hand expression
        children.push(lhs);
        self.bleed_whitespace()?;

        // Binary operator
        children.push(terminal!(self.next_expect_is_of(vec![
            TokenKind::DoubleEquals,
            TokenKind::LessThan,
            TokenKind::LessThanOrEqual,
            TokenKind::GreaterThan,
            TokenKind::GreaterThanOrEqual,
            TokenKind::Plus,
            TokenKind::Minus,
            TokenKind::Asterisk,
            TokenKind::Divide,
            TokenKind::Modulo,
            TokenKind::BitwiseXor,
            TokenKind::BitwiseOr,
            TokenKind::BitwiseAnd,
            TokenKind::Exponentiation,
            TokenKind::LeftShift,
            TokenKind::RightShift,
            TokenKind::LogicalOr,
            TokenKind::LogicalAnd,
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
    ) -> Result<ParseTreeNode, CompilerError> {
        let mut children = Vec::new();

        // Left hand expression
        children.push(lhs);
        self.bleed_whitespace()?;

        // Dot operator
        children.push(terminal!(self.next_expect_is(TokenKind::Period)?));
        self.bleed_whitespace()?;

        // Field
        children.push(terminal!(self.next_expect_is(TokenKind::Identifier)?));

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
    ) -> Result<ParseTreeNode, CompilerError> {
        let mut children = Vec::new();

        // Left hand expression
        children.push(lhs);
        self.bleed_whitespace()?;

        // Dot operator
        children.push(terminal!(self.next_expect_is(TokenKind::Period)?));
        self.bleed_whitespace()?;

        // Method
        let identifier = terminal!(self.next_expect_is(TokenKind::Identifier)?);
        children.push(self.parse_function_call_expression(identifier)?);

        Ok(ParseTreeNode::NonTerminal(ParseTreeNodeNonTerminal {
            kind: ParseTreeNonTerminalKind::StructMethodCall,
            children,
        }))
    }

    /// UnaryExpression ::
    ///     unary_operator Expression  
    fn parse_unary_expression(&mut self) -> Result<ParseTreeNode, CompilerError> {
        let mut children = Vec::new();

        // Unary operator
        children.push(terminal!(self.next_expect_is_of(vec![
            TokenKind::BitwiseNot,
            TokenKind::LogicalNot,
            TokenKind::Asterisk
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
    fn parse_atom(&mut self) -> Result<ParseTreeNode, CompilerError> {
        let mut children = Vec::new();

        match self.peek_expect()?.kind {
            TokenKind::Identifier => {
                children.push(self.parse_qualified_identifier()?);
            }
            k if k.is_literal() => {
                children.push(terminal!(self.next_expect()?));
            }
            TokenKind::OpenParen => {
                children.push(terminal!(self.next_expect_is(TokenKind::OpenParen)?));
                self.bleed_whitespace()?;

                children.push(self.parse_expression()?);
                self.bleed_whitespace()?;

                children.push(terminal!(self.next_expect_is(TokenKind::CloseParen)?));
            }
            k => {
                return Err(self.create_error_with_span(
                    ParserErrorKind::UnexpectedToken {
                        expected: vec![
                            TokenKind::Identifier,
                            TokenKind::OpenParen,
                            TokenKind::CharLiteral,
                            TokenKind::StringLiteral,
                            TokenKind::IntegerLiteral(IntegerLiteralKind::Binary),
                            TokenKind::IntegerLiteral(IntegerLiteralKind::Octal),
                            TokenKind::IntegerLiteral(IntegerLiteralKind::Hexadecimal),
                            TokenKind::IntegerLiteral(IntegerLiteralKind::Decimal),
                            TokenKind::FloatLiteral,
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
    ) -> Result<ParseTreeNode, CompilerError> {
        Ok(ParseTreeNode::NonTerminal(ParseTreeNodeNonTerminal {
            kind: ParseTreeNonTerminalKind::Atom,
            children: vec![node],
        }))
    }

    /// StructDefinition ::
    ///     `struct` identifier StructDefinitionBody?
    fn parse_struct_definition(&mut self) -> Result<ParseTreeNode, CompilerError> {
        let mut children = Vec::new();

        children.push(terminal!(
            self.next_expect_is(TokenKind::Keyword(KeywordKind::Struct))?
        ));
        self.bleed_whitespace()?;

        children.push(terminal!(self.next_expect_is(TokenKind::Identifier)?));

        if self
            .peek_nth_ignore_whitespace(0)?
            .is_some_and(|token| token.kind == TokenKind::OpenCurlyBracket)
        {
            self.bleed_whitespace()?;
            children.push(self.parse_struct_definition_body()?)
        } else if self.lexer.has_next()? {
            // If open bracket does not follow, must be None or newline
            children.push(terminal!(self.next_expect_is(TokenKind::Newline)?));
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
    fn parse_struct_definition_body(&mut self) -> Result<ParseTreeNode, CompilerError> {
        let mut children = Vec::new();

        children.push(terminal!(self.next_expect_is(TokenKind::OpenCurlyBracket)?));
        self.bleed_whitespace()?;

        if self.peek_nth_ignore_whitespace_expect(0)?.kind != TokenKind::CloseCurlyBracket {
            // Non `}`, so parse at last one type association
            children.push(self.parse_type_association()?);

            while self.peek_expect_is(TokenKind::Newline)? {
                self.bleed_whitespace()?;

                if self.peek_expect_is(TokenKind::CloseCurlyBracket)? {
                    break;
                }

                children.push(self.parse_type_association()?);
            }
        }

        children.push(terminal!(self.next_expect_is(TokenKind::CloseCurlyBracket)?));

        Ok(ParseTreeNode::NonTerminal(ParseTreeNodeNonTerminal {
            kind: ParseTreeNonTerminalKind::StructDefinitionBody,
            children,
        }))
    }

    /// TypeAssociation ::
    ///     (identifier `:` Type)
    fn parse_type_association(&mut self) -> Result<ParseTreeNode, CompilerError> {
        let mut children = Vec::new();

        children.push(terminal!(self.next_expect_is(TokenKind::Identifier)?));
        self.bleed_whitespace()?;

        children.push(terminal!(self.next_expect_is(TokenKind::Colon)?));
        self.bleed_whitespace()?;

        children.push(self.parse_type()?);

        Ok(ParseTreeNode::NonTerminal(ParseTreeNodeNonTerminal {
            kind: ParseTreeNonTerminalKind::TypeAssociation,
            children,
        }))
    }

    /// Type ::
    ///     QualifiedIdentifier
    fn parse_type(&mut self) -> Result<ParseTreeNode, CompilerError> {
        let children = vec![self.parse_qualified_identifier()?];

        Ok(ParseTreeNode::NonTerminal(ParseTreeNodeNonTerminal {
            kind: ParseTreeNonTerminalKind::Type,
            children,
        }))
    }

    /// QualifiedIdentifier ::
    ///     identifier (`::` identifier)*
    fn parse_qualified_identifier(&mut self) -> Result<ParseTreeNode, CompilerError> {
        let mut children = Vec::new();

        children.push(terminal!(self.next_expect_is(TokenKind::Identifier)?));

        while self
            .peek_nth_ignore_whitespace(0)?
            .is_some_and(|token| token.kind == TokenKind::DoubleColon)
        {
            self.bleed_whitespace()?;
            children.push(terminal!(self.next_expect_is(TokenKind::DoubleColon)?));

            self.bleed_whitespace()?;
            children.push(terminal!(self.next_expect_is(TokenKind::Identifier)?));
        }

        Ok(ParseTreeNode::NonTerminal(ParseTreeNodeNonTerminal {
            kind: ParseTreeNonTerminalKind::QualifiedIdentifier,
            children,
        }))
    }

    /// ConstantVariableDeclaration ::
    ///     `perm` identifier `:` Type `=` Expression
    fn parse_constant_variable_declaration(&mut self) -> Result<ParseTreeNode, CompilerError> {
        let mut children = Vec::new();

        children.push(terminal!(
            self.next_expect_is(TokenKind::Keyword(KeywordKind::Perm))?
        ));
        self.bleed_whitespace()?;

        children.push(terminal!(self.next_expect_is(TokenKind::Identifier)?));
        self.bleed_whitespace()?;

        children.push(terminal!(self.next_expect_is(TokenKind::Colon)?));
        self.bleed_whitespace()?;

        children.push(self.parse_type()?);
        self.bleed_whitespace()?;

        children.push(terminal!(self.next_expect_is(TokenKind::Equals)?));
        self.bleed_whitespace()?;

        children.push(self.parse_expression()?);

        if self.lexer.has_next()? {
            children.push(terminal!(self.next_expect_is(TokenKind::Newline)?));
        }

        Ok(ParseTreeNode::NonTerminal(ParseTreeNodeNonTerminal {
            kind: ParseTreeNonTerminalKind::ConstantVariableDeclaration,
            children,
        }))
    }

    /// StaticVariableDeclaration ::
    ///     `hold` identifier `:` Type `=` Expression
    fn parse_static_variable_declaration(&mut self) -> Result<ParseTreeNode, CompilerError> {
        let mut children = Vec::new();

        children.push(terminal!(
            self.next_expect_is(TokenKind::Keyword(KeywordKind::Hold))?
        ));
        self.bleed_whitespace()?;

        children.push(terminal!(self.next_expect_is(TokenKind::Identifier)?));
        self.bleed_whitespace()?;

        children.push(terminal!(self.next_expect_is(TokenKind::Colon)?));
        self.bleed_whitespace()?;

        children.push(self.parse_type()?);
        self.bleed_whitespace()?;

        children.push(terminal!(self.next_expect_is(TokenKind::Equals)?));
        self.bleed_whitespace()?;

        children.push(self.parse_expression()?);

        if self.lexer.has_next()? {
            children.push(terminal!(self.next_expect_is(TokenKind::Newline)?));
        }

        Ok(ParseTreeNode::NonTerminal(ParseTreeNodeNonTerminal {
            kind: ParseTreeNonTerminalKind::StaticVariableDeclaration,
            children,
        }))
    }

    /// Internal method to parse all the tokens from the internal lexer
    fn parse_from_lexer(&mut self) -> Result<ParseTree, CompilerError> {
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
        frontend::lexer::Lexer,
        frontend::{
            lexer::token::{IntegerLiteralKind, KeywordKind, Token, TokenKind},
            reader::FileReader,
        },
    };

    use super::{ParseTreeNode, ParseTreeNodeNonTerminal, ParseTreeNonTerminalKind, Parser};

    fn compare_input_to_expected(input: &str, expected_tree: ParseTreeNode) {
        // Collect tokens from lexer
        let reader = FileReader::from(input.to_owned());
        let lexer = Lexer::new(reader);
        let parse_tree =
            Parser::parse(lexer).unwrap_or_else(|e| panic!("Could not parse input: \n{e}"));

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
            ParseTreeNode::Terminal(Token::from(($kind, $text)))
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
                            terminal_from!(TokenKind::Keyword(KeywordKind::Perm), "perm"),
                            terminal_from!(TokenKind::Identifier, "PI"),
                            terminal_from!(TokenKind::Colon, ":"),
                            non_terminal!(
                                ParseTreeNonTerminalKind::Type,
                                vec![non_terminal!(
                                    ParseTreeNonTerminalKind::QualifiedIdentifier,
                                    vec![
                                        terminal_from!(TokenKind::Identifier, "f32"),
                                    ]
                                )]
                            ),
                            terminal_from!(TokenKind::Equals, "="),
                            non_terminal!(
                                ParseTreeNonTerminalKind::Expression,
                                vec![non_terminal!(
                                    ParseTreeNonTerminalKind::Atom,
                                    vec![terminal_from!(
                                        TokenKind::FloatLiteral,
                                        "3.1415926535"
                                    ),]
                                ),]
                            ),
                            terminal_from!(TokenKind::Newline, "\n"),
                        ]
                    ),
                    non_terminal!(
                        ParseTreeNonTerminalKind::ConstantVariableDeclaration,
                        vec![
                            terminal_from!(TokenKind::Keyword(KeywordKind::Perm), "perm"),
                            terminal_from!(TokenKind::Identifier, "E"),
                            terminal_from!(TokenKind::Colon, ":"),
                            non_terminal!(
                                ParseTreeNonTerminalKind::Type,
                                vec![non_terminal!(
                                    ParseTreeNonTerminalKind::QualifiedIdentifier,
                                    vec![
                                        terminal_from!(TokenKind::Identifier, "f32"),
                                    ]
                                )]
                            ),
                            terminal_from!(TokenKind::Equals, "="),
                            non_terminal!(
                                ParseTreeNonTerminalKind::Expression,
                                vec![non_terminal!(
                                    ParseTreeNonTerminalKind::Atom,
                                    vec![terminal_from!(TokenKind::FloatLiteral, "2.178"),]
                                ),]
                            ),
                            terminal_from!(TokenKind::Newline, "\n"),
                        ]
                    ),
                    non_terminal!(
                        ParseTreeNonTerminalKind::ConstantVariableDeclaration,
                        vec![
                            terminal_from!(TokenKind::Keyword(KeywordKind::Perm), "perm"),
                            terminal_from!(TokenKind::Identifier, "THREE"),
                            terminal_from!(TokenKind::Colon, ":"),
                            non_terminal!(
                                ParseTreeNonTerminalKind::Type,
                                vec![non_terminal!(
                                    ParseTreeNonTerminalKind::QualifiedIdentifier,
                                    vec![
                                        terminal_from!(TokenKind::Identifier, "u8"),
                                    ]
                                )]
                            ),
                            terminal_from!(TokenKind::Equals, "="),
                            non_terminal!(
                                ParseTreeNonTerminalKind::Expression,
                                vec![non_terminal!(
                                    ParseTreeNonTerminalKind::Atom,
                                    vec![terminal_from!(
                                        TokenKind::IntegerLiteral(
                                            IntegerLiteralKind::Hexadecimal
                                        ),
                                        "0x03"
                                    ),]
                                ),]
                            ),
                            terminal_from!(TokenKind::Newline, "\n"),
                        ]
                    ),
                    non_terminal!(
                        ParseTreeNonTerminalKind::StaticVariableDeclaration,
                        vec![
                            terminal_from!(TokenKind::Keyword(KeywordKind::Hold), "hold"),
                            terminal_from!(TokenKind::Identifier, "state"),
                            terminal_from!(TokenKind::Colon, ":"),
                            non_terminal!(
                                ParseTreeNonTerminalKind::Type,
                                vec![non_terminal!(
                                    ParseTreeNonTerminalKind::QualifiedIdentifier,
                                    vec![
                                        terminal_from!(TokenKind::Identifier, "u8"),
                                    ]
                                )]
                            ),
                            terminal_from!(TokenKind::Equals, "="),
                            non_terminal!(
                                ParseTreeNonTerminalKind::Expression,
                                vec![non_terminal!(
                                    ParseTreeNonTerminalKind::Atom,
                                    vec![terminal_from!(
                                        TokenKind::IntegerLiteral(IntegerLiteralKind::Binary),
                                        "0b0001"
                                    ),]
                                ),]
                            ),
                            terminal_from!(TokenKind::Newline, "\n"),
                        ]
                    ),
                    non_terminal!(
                        ParseTreeNonTerminalKind::FunctionDefinition,
                        vec![
                            terminal_from!(TokenKind::Keyword(KeywordKind::Fn), "fn"),
                            non_terminal!(
                                ParseTreeNonTerminalKind::QualifiedIdentifier,
                                vec![
                                    terminal_from!(TokenKind::Identifier, "main"),
                                ]
                            ),
                            non_terminal!(
                                ParseTreeNonTerminalKind::FunctionParameters,
                                vec![
                                    terminal_from!(TokenKind::OpenParen, "("),
                                    terminal_from!(TokenKind::CloseParen, ")"),
                                ]
                            ),
                            non_terminal!(
                                ParseTreeNonTerminalKind::Block,
                                vec![
                                    terminal_from!(TokenKind::OpenCurlyBracket, "{"),
                                    non_terminal!(
                                        ParseTreeNonTerminalKind::Statement,
                                        vec![
                                            non_terminal!(
                                                ParseTreeNonTerminalKind::LocalVariableDeclaration,
                                                vec![
                                                    terminal_from!(
                                                        TokenKind::Keyword(KeywordKind::Leak),
                                                        "leak"
                                                    ),
                                                    terminal_from!(TokenKind::Identifier, "a"),
                                                    terminal_from!(TokenKind::Equals, "="),
                                                    non_terminal!(
                                                        ParseTreeNonTerminalKind::Expression,
                                                        vec![non_terminal!(
                                                            ParseTreeNonTerminalKind::Atom,
                                                            vec![terminal_from!(
                                                                TokenKind::IntegerLiteral(
                                                                    IntegerLiteralKind::Decimal
                                                                ),
                                                                "1"
                                                            ),]
                                                        ),]
                                                    ),
                                                ]
                                            ),
                                            terminal_from!(TokenKind::Newline, "\n"),
                                        ]
                                    ),
                                    non_terminal!(
                                        ParseTreeNonTerminalKind::Statement,
                                        vec![
                                            non_terminal!(
                                                ParseTreeNonTerminalKind::LocalVariableDeclaration,
                                                vec![
                                                    terminal_from!(
                                                        TokenKind::Keyword(KeywordKind::Leak),
                                                        "leak"
                                                    ),
                                                    terminal_from!(TokenKind::Identifier, "b"),
                                                    terminal_from!(TokenKind::Equals, "="),
                                                    non_terminal!(
                                                        ParseTreeNonTerminalKind::Expression,
                                                        vec![non_terminal!(
                                                            ParseTreeNonTerminalKind::Atom,
                                                            vec![terminal_from!(
                                                                TokenKind::IntegerLiteral(
                                                                    IntegerLiteralKind::Decimal
                                                                ),
                                                                "2"
                                                            ),]
                                                        ),]
                                                    ),
                                                ]
                                            ),
                                            terminal_from!(TokenKind::Newline, "\n"),
                                        ]
                                    ),
                                    non_terminal!(
                                        ParseTreeNonTerminalKind::Statement,
                                        vec![
                                            non_terminal!(
                                                ParseTreeNonTerminalKind::LocalVariableDeclaration,
                                                vec![
                                                    terminal_from!(
                                                        TokenKind::Keyword(KeywordKind::Leak),
                                                        "leak"
                                                    ),
                                                    terminal_from!(TokenKind::Identifier, "node"),
                                                    terminal_from!(TokenKind::Equals, "="),
                                                    non_terminal!(
                                                        ParseTreeNonTerminalKind::Expression,
                                                        vec![non_terminal!(
                                                        ParseTreeNonTerminalKind::FunctionCallExpression,
                                                        vec![
                                                            non_terminal!(
                                                                ParseTreeNonTerminalKind::QualifiedIdentifier,
                                                                vec![
                                                                    terminal_from!(TokenKind::Identifier, "Node"),
                                                                ]
                                                            ),
                                                            terminal_from!(TokenKind::OpenParen, "("),
                                                            non_terminal!(
                                                                ParseTreeNonTerminalKind::FunctionArguments,
                                                                vec![non_terminal!(
                                                                    ParseTreeNonTerminalKind::Expression,
                                                                    vec![non_terminal!(
                                                                        ParseTreeNonTerminalKind::Atom,
                                                                        vec![terminal_from!(
                                                                            TokenKind::StringLiteral,
                                                                            "\"text\""
                                                                        ),]
                                                                    ),]
                                                                ),]
                                                            ),
                                                            terminal_from!(TokenKind::CloseParen, ")"),
                                                        ]
                                                    ),]
                                                    ),
                                                ]
                                            ),
                                            terminal_from!(TokenKind::Newline, "\n"),
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
                                                            terminal_from!(TokenKind::Identifier, "println"),
                                                        ]
                                                    ),
                                                    terminal_from!(TokenKind::OpenParen, "("),
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
                                                                            terminal_from!(TokenKind::Identifier, "a"),
                                                                        ]
                                                                    )
                                                                ]
                                                            ),]
                                                        ),]
                                                    ),
                                                    terminal_from!(TokenKind::CloseParen, ")"),
                                                ]
                                            ),
                                            terminal_from!(TokenKind::Newline, "\n"),
                                        ]
                                    ),
                                    terminal_from!(TokenKind::CloseCurlyBracket, "}"),
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
                            terminal_from!(TokenKind::Keyword(KeywordKind::Struct), "struct"),
                            terminal_from!(TokenKind::Identifier, "EmptyStruct"),
                            terminal_from!(TokenKind::Newline, "\n"),
                        ]
                    ),
                    non_terminal!(
                        ParseTreeNonTerminalKind::StructDefinition,
                        vec![
                            terminal_from!(TokenKind::Keyword(KeywordKind::Struct), "struct"),
                            terminal_from!(TokenKind::Identifier, "SomeStruct"),
                            non_terminal!(
                                ParseTreeNonTerminalKind::StructDefinitionBody,
                                vec![
                                    terminal_from!(TokenKind::OpenCurlyBracket, "{"),
                                    terminal_from!(TokenKind::CloseCurlyBracket, "}"),
                                ]
                            )
                        ]
                    ),
                    non_terminal!(
                        ParseTreeNonTerminalKind::StructDefinition,
                        vec![
                            terminal_from!(TokenKind::Keyword(KeywordKind::Struct), "struct"),
                            terminal_from!(TokenKind::Identifier, "BinaryTreeNode"),
                            non_terminal!(
                                ParseTreeNonTerminalKind::StructDefinitionBody,
                                vec![
                                    terminal_from!(TokenKind::OpenCurlyBracket, "{"),
                                    non_terminal!(
                                        ParseTreeNonTerminalKind::TypeAssociation,
                                        vec![
                                            terminal_from!(TokenKind::Identifier, "left"),
                                            terminal_from!(TokenKind::Colon, ":"),
                                            non_terminal!(
                                                ParseTreeNonTerminalKind::Type,
                                                vec![non_terminal!(
                                                    ParseTreeNonTerminalKind::QualifiedIdentifier,
                                                    vec![terminal_from!(
                                                        TokenKind::Identifier,
                                                        "BinaryTreeNode"
                                                    ),]
                                                )]
                                            ),
                                        ]
                                    ),
                                    non_terminal!(
                                        ParseTreeNonTerminalKind::TypeAssociation,
                                        vec![
                                            terminal_from!(TokenKind::Identifier, "right"),
                                            terminal_from!(TokenKind::Colon, ":"),
                                            non_terminal!(
                                                ParseTreeNonTerminalKind::Type,
                                                vec![non_terminal!(
                                                    ParseTreeNonTerminalKind::QualifiedIdentifier,
                                                    vec![terminal_from!(
                                                        TokenKind::Identifier,
                                                        "BinaryTreeNode"
                                                    ),]
                                                )]
                                            ),
                                        ]
                                    ),
                                    non_terminal!(
                                        ParseTreeNonTerminalKind::TypeAssociation,
                                        vec![
                                            terminal_from!(TokenKind::Identifier, "data"),
                                            terminal_from!(TokenKind::Colon, ":"),
                                            non_terminal!(
                                                ParseTreeNonTerminalKind::Type,
                                                vec![non_terminal!(
                                                    ParseTreeNonTerminalKind::QualifiedIdentifier,
                                                    vec![terminal_from!(
                                                        TokenKind::Identifier,
                                                        "i32"
                                                    ),]
                                                )]
                                            ),
                                        ]
                                    ),
                                    terminal_from!(TokenKind::CloseCurlyBracket, "}"),
                                ]
                            )
                        ]
                    ),
                ]
            ),
        )
    }
}
