use core::panic;

use crate::{
    common::lang::BinaryOperator,
    frontend::{
        ast::{
            AssignmentOperator, Atom, BinaryExpression, Block, FunctionCallExpression,
            FunctionDefinition, FunctionParameter, Statement, StructDefinition, StructFieldAccess,
            StructInitialization, StructMethodCall, UnaryExpression, VariableDeclaration,
            VariableDeclarationKind,
        },
        lexer::{IntegerLiteralKind, KeywordKind, LeekToken, LeekTokenKind},
        parser::{ParseTree, ParseTreeNode, ParseTreeNodeNonTerminal, ParseTreeNonTerminalKind},
    },
};

use super::{
    Expression, IntegerKind, LeekAst, Literal, LiteralKind, PrimitiveKind, Program,
    QualifiedIdentifier, Type, VariableAssignment,
};

// TODO: Add spans for ast nodes

impl LeekAst {
    /// This function is infallible. If there is an error, it is due to a bug in the parser or the builder.
    /// As such, this function will panic if there is an error.
    pub fn build_from(parse_tree: ParseTree) -> Self {
        let root = Program {
            constant_variables: vec![],
            static_variables: vec![],
            function_definitions: vec![],
            struct_definitions: vec![],
            enum_definitions: vec![],
        };

        let mut ast = Self {
            source_file: parse_tree.source_file.clone(),
            root,
        };

        ast.populate(parse_tree);

        ast
    }

    fn populate(&mut self, parse_tree: ParseTree) {
        let program = parse_tree.root.non_terminal();
        assert!(program.kind == ParseTreeNonTerminalKind::Program);

        for node in &program.children {
            let ParseTreeNode::NonTerminal(top_level_node) = node else {
                panic!("Expected top level node to be non-terminal, found {:?}", node);
            };

            match top_level_node.kind {
                ParseTreeNonTerminalKind::ConstantVariableDeclaration => self
                    .root
                    .constant_variables
                    .push(VariableDeclaration::from_node(top_level_node)),
                ParseTreeNonTerminalKind::StaticVariableDeclaration => self
                    .root
                    .static_variables
                    .push(VariableDeclaration::from_node(top_level_node)),
                ParseTreeNonTerminalKind::FunctionDefinition => self
                    .root
                    .function_definitions
                    .push(FunctionDefinition::from_node(top_level_node)),
                ParseTreeNonTerminalKind::StructDefinition => self
                    .root
                    .struct_definitions
                    .push(StructDefinition::from_node(top_level_node)),
                _ => panic!("Unexpected top level node: {:?}", top_level_node),
            }
        }
    }
}

#[inline]
fn assert_nt_kind(node: &ParseTreeNodeNonTerminal, kind: ParseTreeNonTerminalKind) {
    assert_eq!(
        node.kind, kind,
        "Expected non-terminal node {:?}, found {:?}",
        kind, node.kind
    );
}

#[inline]
fn assert_nt_kind_of(node: &ParseTreeNodeNonTerminal, kinds: &[ParseTreeNonTerminalKind]) {
    assert!(
        kinds.contains(&node.kind),
        "Expected non-terminal node {:?}, found {:?}",
        kinds,
        node.kind
    );
}

trait FromNode
where
    Self: Sized,
{
    fn from_node(node: &ParseTreeNodeNonTerminal) -> Self;
}

trait FromTerminal
where
    Self: Sized,
{
    fn from_terminal(node: &LeekToken) -> Self;
}

impl FromNode for Type {
    fn from_node(type_node: &ParseTreeNodeNonTerminal) -> Self {
        assert_nt_kind(type_node, ParseTreeNonTerminalKind::Type);

        let qualified_identifier_node = &type_node.children[0].non_terminal();

        assert_nt_kind(
            qualified_identifier_node,
            ParseTreeNonTerminalKind::QualifiedIdentifier,
        );

        let identifier = QualifiedIdentifier::from_node(qualified_identifier_node);

        // Check if is primitive
        if !identifier.has_namespace() {
            let primitive_kind = match identifier.name().as_str() {
                "void" => PrimitiveKind::Void,
                "i8" => PrimitiveKind::I8,
                "i16" => PrimitiveKind::I16,
                "i32" => PrimitiveKind::I32,
                "i64" => PrimitiveKind::I64,
                "u8" => PrimitiveKind::U8,
                "u16" => PrimitiveKind::U16,
                "u32" => PrimitiveKind::U32,
                "u64" => PrimitiveKind::U64,
                "f32" => PrimitiveKind::F32,
                "f64" => PrimitiveKind::F64,
                _ => return Type::Identifier(identifier),
            };

            return Type::Primitive(primitive_kind);
        }

        Type::Identifier(identifier)
    }
}

impl FromNode for QualifiedIdentifier {
    fn from_node(node: &ParseTreeNodeNonTerminal) -> Self {
        assert!(
            !node.children.is_empty(),
            "Qualified identifier node has no children"
        );

        let name = node.children.last().unwrap().terminal_token().text.clone();

        let mut namespace = None;

        if node.children.len() > 1 {
            assert!(
                node.children.len() % 2 == 1,
                "Qualified identifier node has invalid children"
            );

            let mut parts = vec![];

            for i in 0..(node.children.len() - 1) / 2 {
                let id = node.children.get(i * 2).unwrap().terminal_token();

                parts.push(id.text.clone())
            }

            namespace = Some(parts)
        }

        QualifiedIdentifier { namespace, name }
    }
}

impl FromNode for VariableDeclaration {
    fn from_node(_node: &ParseTreeNodeNonTerminal) -> Self {
        todo!()
    }
}

impl FromNode for Expression {
    fn from_node(node: &ParseTreeNodeNonTerminal) -> Self {
        assert_nt_kind(node, ParseTreeNonTerminalKind::Expression);

        assert_eq!(node.children.len(), 1);

        let expression_node = &node.children[0].non_terminal();

        match expression_node.kind {
            ParseTreeNonTerminalKind::Atom => {
                let atom = Atom::from_node(expression_node);

                Expression::Atom(atom)
            }
            ParseTreeNonTerminalKind::UnaryExpression => {
                let unary_expression = UnaryExpression::from_node(expression_node);

                Expression::UnaryExpression(unary_expression)
            }
            ParseTreeNonTerminalKind::FunctionCallExpression => {
                let function_call_expression = FunctionCallExpression::from_node(expression_node);

                Expression::FunctionCallExpression(function_call_expression)
            }
            ParseTreeNonTerminalKind::BinaryExpression => {
                let binary_expression = BinaryExpression::from_node(expression_node);

                Expression::BinaryExpression(binary_expression)
            }
            ParseTreeNonTerminalKind::StructInitialization => {
                let struct_initialization = StructInitialization::from_node(expression_node);

                Expression::StructInitialization(struct_initialization)
            }
            ParseTreeNonTerminalKind::StructFieldAccess => {
                let struct_field_access = StructFieldAccess::from_node(expression_node);

                Expression::StructFieldAccess(struct_field_access)
            }
            ParseTreeNonTerminalKind::StructMethodCall => {
                let struct_method_call = StructMethodCall::from_node(expression_node);

                Expression::StructMethodCall(struct_method_call)
            }
            _ => unreachable!("Found invalid node in expression"),
        }
    }
}

impl From<LeekToken> for IntegerKind {
    fn from(value: LeekToken) -> Self {
        let LeekTokenKind::IntegerLiteral(integer) = value.kind else {
           panic!("Expected integer literal, found {:?}", value.kind)
       };

        // TODO: add support for type specifiers like `u32` and `i32`

        match integer {
            IntegerLiteralKind::Decimal => {
                let Ok(value) = value.text.parse::<i32>() else {
                    panic!("Could not parse integer literal from token text")
                };

                IntegerKind::I32(value)
            }
            IntegerLiteralKind::Hexadecimal => todo!(),
            IntegerLiteralKind::Binary => todo!(),
            IntegerLiteralKind::Octal => todo!(),
        }
    }
}

impl FromNode for Atom {
    fn from_node(node: &ParseTreeNodeNonTerminal) -> Self {
        assert_nt_kind(node, ParseTreeNonTerminalKind::Atom);

        let atom = match &node.children[0] {
            ParseTreeNode::Terminal(terminal) => match terminal.kind {
                LeekTokenKind::StringLiteral => Atom::Literal(Literal {
                    kind: LiteralKind::String(terminal.text.clone()),
                    span: terminal.span.clone(),
                }),
                LeekTokenKind::CharLiteral => todo!(),
                LeekTokenKind::IntegerLiteral(_) => Atom::Literal(Literal {
                    kind: LiteralKind::Integer(IntegerKind::from(terminal.clone())),
                    span: terminal.span.clone(),
                }),
                LeekTokenKind::FloatLiteral => todo!(),
                LeekTokenKind::OpenParen => {
                    let expression = Expression::from_node(node.children[1].non_terminal());

                    assert_eq!(
                        node.children[2].terminal_token().kind,
                        LeekTokenKind::CloseParen
                    );

                    Atom::ParenthesizedExpression(Box::new(expression))
                }
                _ => unreachable!("Found invalid atom node"),
            },
            ParseTreeNode::NonTerminal(non_terminal) => match non_terminal.kind {
                ParseTreeNonTerminalKind::QualifiedIdentifier => {
                    let identifier = QualifiedIdentifier::from_node(non_terminal);

                    Atom::QualifiedIdentifier(identifier)
                }
                _ => unreachable!("Found invalid atom node"),
            },
        };

        atom
    }
}

impl FromNode for UnaryExpression {
    fn from_node(_node: &ParseTreeNodeNonTerminal) -> Self {
        todo!("build from unary expression")
    }
}

impl FromNode for FunctionCallExpression {
    fn from_node(node: &ParseTreeNodeNonTerminal) -> Self {
        assert_nt_kind(node, ParseTreeNonTerminalKind::FunctionCallExpression);

        assert!(node.children.len() >= 3);
        assert!(node.children.len() <= 4);

        let identifier = QualifiedIdentifier::from_node(node.children[0].non_terminal());

        assert_eq!(
            node.children[1].terminal_token().kind,
            LeekTokenKind::OpenParen
        );

        let arguments = match &node.children[2] {
            ParseTreeNode::Terminal(terminal) => {
                assert_eq!(terminal.kind, LeekTokenKind::CloseParen);
                Vec::new()
            }
            ParseTreeNode::NonTerminal(non_terminal) => {
                assert_eq!(
                    node.children[3].terminal_token().kind,
                    LeekTokenKind::CloseParen
                );

                assert_nt_kind(non_terminal, ParseTreeNonTerminalKind::FunctionArguments);

                let mut arguments = vec![];

                for (index, argument) in non_terminal.children.iter().enumerate() {
                    if index % 2 == 1 {
                        assert_eq!(argument.terminal_token().kind, LeekTokenKind::Comma);
                        continue;
                    }

                    let argument = Expression::from_node(argument.non_terminal());

                    arguments.push(argument)
                }

                arguments
            }
        };

        FunctionCallExpression {
            identifier,
            arguments,
        }
    }
}

impl FromTerminal for BinaryOperator {
    fn from_terminal(node: &LeekToken) -> Self {
        match node.kind {
            LeekTokenKind::DoubleEquals => Self::DoubleEquals,
            LeekTokenKind::LessThan => Self::LessThan,
            LeekTokenKind::LessThanOrEqual => Self::LessThanOrEqual,
            LeekTokenKind::GreaterThan => Self::GreaterThan,
            LeekTokenKind::GreaterThanOrEqual => Self::GreaterThanOrEqual,
            LeekTokenKind::Plus => Self::Plus,
            LeekTokenKind::Minus => Self::Minus,
            LeekTokenKind::Asterisk => Self::Asterisk,
            LeekTokenKind::Divide => Self::Divide,
            LeekTokenKind::Modulo => Self::Modulo,
            LeekTokenKind::BitwiseXor => Self::BitwiseXor,
            LeekTokenKind::BitwiseOr => Self::BitwiseOr,
            LeekTokenKind::BitwiseAnd => Self::BitwiseAnd,
            LeekTokenKind::Exponentiation => Self::Exponentiation,
            LeekTokenKind::LeftShift => Self::LeftShift,
            LeekTokenKind::RightShift => Self::RightShift,
            LeekTokenKind::LogicalOr => Self::LogicalOr,
            LeekTokenKind::LogicalAnd => Self::LogicalAnd,
            _ => {
                panic!("Invalid binary operator {:?}", node.kind);
            }
        }
    }
}

impl FromNode for BinaryExpression {
    fn from_node(node: &ParseTreeNodeNonTerminal) -> Self {
        assert_nt_kind(node, ParseTreeNonTerminalKind::BinaryExpression);

        assert_eq!(node.children.len(), 3, "Binary expression must have 3 children");

        let left = Expression::from_node(node.children[0].non_terminal());
        let operator = BinaryOperator::from_terminal(node.children[1].terminal_token());
        let right = Expression::from_node(node.children[2].non_terminal());

        BinaryExpression {
            binary_operator: operator,
            lhs: Box::new(left),
            rhs: Box::new(right),
        }
    }
}

impl FromNode for StructInitialization {
    fn from_node(_node: &ParseTreeNodeNonTerminal) -> Self {
        todo!("build from struct initialization")
    }
}

impl FromNode for StructFieldAccess {
    fn from_node(_node: &ParseTreeNodeNonTerminal) -> Self {
        todo!("build from struct field access")
    }
}

impl FromNode for StructMethodCall {
    fn from_node(_node: &ParseTreeNodeNonTerminal) -> Self {
        todo!("build from struct method call")
    }
}

impl FromNode for FunctionDefinition {
    fn from_node(node: &ParseTreeNodeNonTerminal) -> Self {
        assert_nt_kind(node, ParseTreeNonTerminalKind::FunctionDefinition);

        /* Get Function Def Components */

        assert!(node.children.len() >= 4 && node.children.len() <= 5);

        let (_fn, identifier, parameters, return_type, block) = match node.children.len() {
            4 => (
                &node.children[0],
                &node.children[1],
                &node.children[2],
                None,
                &node.children[3],
            ),
            5 => (
                &node.children[0],
                &node.children[1],
                &node.children[2],
                Some(&node.children[3]),
                &node.children[4],
            ),
            _ => unreachable!("Invalid number of children in function definition"),
        };

        /* Build the function identifier and struct identifier (if any) */

        let QualifiedIdentifier { name, namespace } =
            QualifiedIdentifier::from_node(identifier.non_terminal());

        let struct_identifier = match namespace {
            Some(n) => {
                if n.len() == 1 {
                    n.first().map(|s| s.to_owned())
                } else {
                    panic!("Function name qualified identifier had more than one namespace value");
                }
            }
            None => None,
        };

        /* Build the function parameters */

        // Make sure that the param node is correct
        assert_nt_kind(
            parameters.non_terminal(),
            ParseTreeNonTerminalKind::FunctionParameters,
        );

        let parameter_nodes = &parameters.non_terminal().children;

        // Make sure we have enough nodes
        assert!(
            parameter_nodes.len() >= 2,
            "Less than 2 nodes in function parameters. Expected parens."
        );

        // Make sure nodes are correct
        assert_eq!(
            parameter_nodes.first().unwrap().terminal_token().kind,
            LeekTokenKind::OpenParen,
            "Expected first token of params to be open paren"
        );

        assert_eq!(
            parameter_nodes.last().unwrap().terminal_token().kind,
            LeekTokenKind::CloseParen,
            "Expected last token of params to be close paren"
        );

        let mut parameters = Vec::new();

        for i in 1..parameter_nodes.len() - 1 {
            if i % 2 == 0 {
                assert_eq!(
                    parameter_nodes.get(i).unwrap().terminal_token().kind,
                    LeekTokenKind::Comma,
                    "Expected token to be comma"
                );
                continue;
            }

            parameters.push(FunctionParameter::from_node(
                parameter_nodes.get(i).unwrap().non_terminal(),
            ))
        }

        let return_type = match return_type {
            Some(function_return_type_node) => {
                let function_return_type = function_return_type_node.non_terminal();

                assert_nt_kind(
                    function_return_type,
                    ParseTreeNonTerminalKind::FunctionReturnType,
                );

                assert_eq!(
                    function_return_type.children[0].terminal_token().kind,
                    LeekTokenKind::Arrow,
                    "Expected first token of return type to be arrow"
                );

                let type_node = &function_return_type.children[1].non_terminal();

                Type::from_node(type_node)
            }
            None => Type::Primitive(PrimitiveKind::Void),
        };

        let block = block.non_terminal();
        let block = Block::from_node(block);

        FunctionDefinition {
            name,
            struct_identifier,
            parameters,
            return_type,
            body: block,
        }
    }
}

impl FromNode for FunctionParameter {
    fn from_node(node: &ParseTreeNodeNonTerminal) -> Self {
        assert_nt_kind(node, ParseTreeNonTerminalKind::TypeAssociation);

        assert!(node.children.len() == 3);

        let identifier = node.children[0].terminal_token().text.clone();

        assert!(node.children[1].terminal_token().kind == LeekTokenKind::Colon);

        let ty = Type::from_node(node.children[2].non_terminal());

        FunctionParameter { identifier, ty }
    }
}

impl FromNode for Block {
    fn from_node(node: &ParseTreeNodeNonTerminal) -> Self {
        assert_nt_kind(node, ParseTreeNonTerminalKind::Block);

        assert!(node.children.len() >= 2);

        assert_eq!(
            node.children.first().unwrap().terminal_token().kind,
            LeekTokenKind::OpenCurlyBracket
        );

        assert_eq!(
            node.children.last().unwrap().terminal_token().kind,
            LeekTokenKind::CloseCurlyBracket
        );

        let mut statements = Vec::new();

        for i in 1..node.children.len() - 1 {
            let statement = Statement::from_node(node.children[i].non_terminal());
            statements.push(statement);
        }

        Block { statements }
    }
}

impl FromTerminal for AssignmentOperator {
    fn from_terminal(node: &LeekToken) -> Self {
        match node.kind {
            LeekTokenKind::Equals => Self::Equals,
            LeekTokenKind::PlusEquals => Self::PlusEquals,
            LeekTokenKind::MinusEquals => Self::MinusEquals,
            LeekTokenKind::MultiplyEquals => Self::MultiplyEquals,
            LeekTokenKind::DivideEquals => Self::DivideEquals,
            LeekTokenKind::ModuloEquals => Self::ModuloEquals,
            LeekTokenKind::BitwiseNotEquals => Self::BitwiseNotEquals,
            LeekTokenKind::BitwiseXorEquals => Self::BitwiseXorEquals,
            LeekTokenKind::BitwiseOrEquals => Self::BitwiseOrEquals,
            LeekTokenKind::BitwiseAndEquals => Self::BitwiseAndEquals,
            LeekTokenKind::LogicalNotEquals => Self::LogicalNotEquals,
            LeekTokenKind::ExponentiationEquals => Self::ExponentiationEquals,
            LeekTokenKind::LeftShiftEquals => Self::LeftShiftEquals,
            LeekTokenKind::RightShiftEquals => Self::RightShiftEquals,
            LeekTokenKind::LogicalOrEquals => Self::LogicalOrEquals,
            LeekTokenKind::LogicalAndEquals => Self::LogicalAndEquals,
            _ => {
                panic!("Invalid assignment operator {:?}", node.kind);
            }
        }
    }
}

impl FromNode for Statement {
    fn from_node(node: &ParseTreeNodeNonTerminal) -> Self {
        assert_nt_kind_of(
            node,
            &[
                ParseTreeNonTerminalKind::Statement,
                ParseTreeNonTerminalKind::Block,
            ],
        );

        // Recursive block
        if let ParseTreeNonTerminalKind::Block = node.kind {
            return Statement::Block(Block::from_node(node));
        }

        // TODO: Refactor this to match more non-terminal kinds

        // Other kind of statement
        match &node.children[0] {
            ParseTreeNode::Terminal(terminal) => {
                let LeekTokenKind::Keyword(keyword) = terminal.kind else {
                   panic!("Expected keyword token in statement, got {:?}", terminal.kind)
                };

                match keyword {
                    KeywordKind::Yeet => {
                        let expression = Expression::from_node(node.children[1].non_terminal());
                        Statement::Yeet(expression)
                    }
                    KeywordKind::Leak => {
                        let identifier = &node.children[1].terminal_token();
                        assert_eq!(identifier.kind, LeekTokenKind::Identifier);
                        let identifier = identifier.text.clone();

                        assert_eq!(
                            node.children[2].terminal_token().kind,
                            LeekTokenKind::Equals
                        );

                        if let ParseTreeNode::Terminal(terminal) = &node.children[3] {
                            if terminal.kind == LeekTokenKind::Colon {
                                todo!("Parse leak with explicit type")
                            } else {
                                unreachable!("Terminal token in leak statement was not a colon")
                            }
                        }

                        let value = Expression::from_node(node.children[3].non_terminal());

                        Statement::VariableDeclaration(VariableDeclaration {
                            kind: VariableDeclarationKind::Local,
                            identifier,
                            ty: None,
                            value,
                        })
                    }

                    _ => unreachable!("Statement node began with non-statement keyword"),
                }
            }
            ParseTreeNode::NonTerminal(non_terminal) => match non_terminal.kind {
                ParseTreeNonTerminalKind::QualifiedIdentifier => {
                    let identifier =
                        QualifiedIdentifier::from_node(node.children[0].non_terminal());
                    let operator =
                        AssignmentOperator::from_terminal(node.children[1].terminal_token());
                    let value = Expression::from_node(node.children[2].non_terminal());

                    Statement::VariableAssignment(VariableAssignment {
                        identifier,
                        operator,
                        value,
                    })
                }
                ParseTreeNonTerminalKind::FunctionCallExpression => {
                    Statement::FunctionCall(FunctionCallExpression::from_node(non_terminal))
                }
                _ => unreachable!("Statement node began with non-statement non-terminal"),
            },
        }
    }
}

impl FromNode for StructDefinition {
    fn from_node(node: &ParseTreeNodeNonTerminal) -> Self {
        assert_nt_kind(node, ParseTreeNonTerminalKind::StructDefinition);

        todo!()
    }
}

#[cfg(test)]
mod tests {
    use crate::frontend::ast::*;
    use crate::frontend::parse_string;
    use crate::frontend::position::*;

    use indoc::indoc;

    macro_rules! assert_ast_eq {
        ($ast:expr, $expected:expr) => {
            if $ast != $expected {
                use ansi_term::Color;

                let mut output = String::new();

                for diff in diff::lines(&format!("{:#?}", $ast), &format!("{:#?}", $expected)) {
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

                panic!("AST did not match expected: \n{output}");
            }
        };
    }

    #[test]
    fn should_parse_hello_world() {
        const INPUT: &str = indoc! {r#"
        fn main() {
            println("Hello, world!")
        }
        "#};

        let ast = parse_string(INPUT.to_owned()).unwrap_or_else(|e| panic!("{e}"));

        let expected = LeekAst {
            source_file: SourceFile {
                path: None,
                content: INPUT.to_owned(),
            },
            root: Program {
                constant_variables: vec![],
                static_variables: vec![],
                function_definitions: vec![FunctionDefinition {
                    name: "main".to_owned(),
                    struct_identifier: None,
                    parameters: vec![],
                    return_type: Type::Primitive(PrimitiveKind::Void),
                    body: Block {
                        statements: vec![Statement::FunctionCall(FunctionCallExpression {
                            identifier: QualifiedIdentifier::new(None, "println".to_owned()),
                            arguments: vec![Expression::Atom(Atom::Literal(Literal {
                                kind: LiteralKind::String("\"Hello, world!\"".to_owned()),
                                span: Span::new(
                                    Position { row: 1, col: 12 },
                                    Position { row: 1, col: 27 },
                                ),
                            }))],
                        })],
                    },
                }],
                struct_definitions: vec![],
                enum_definitions: vec![],
            },
        };

        assert_ast_eq!(ast, expected);
    }

    #[test]
    fn should_parse_recursive_blocks() {
        const INPUT: &str = indoc! {r#"
        fn main() {
            {
                println("Hello, world!")
            }
        }
        "#};

        let ast = parse_string(INPUT.to_owned()).unwrap_or_else(|e| panic!("{e}"));

        let expected = LeekAst {
            source_file: SourceFile {
                path: None,
                content: INPUT.to_owned(),
            },
            root: Program {
                constant_variables: vec![],
                static_variables: vec![],
                function_definitions: vec![FunctionDefinition {
                    name: "main".to_owned(),
                    struct_identifier: None,
                    parameters: vec![],
                    return_type: Type::Primitive(PrimitiveKind::Void),
                    body: Block {
                        statements: vec![Statement::Block(Block {
                            statements: vec![Statement::FunctionCall(FunctionCallExpression {
                                identifier: QualifiedIdentifier::new(None, "println".to_owned()),
                                arguments: vec![Expression::Atom(Atom::Literal(Literal {
                                    kind: LiteralKind::String("\"Hello, world!\"".to_owned()),
                                    span: Span::new(
                                        Position { row: 2, col: 16 },
                                        Position { row: 2, col: 31 },
                                    ),
                                }))],
                            })],
                        })],
                    },
                }],
                struct_definitions: vec![],
                enum_definitions: vec![],
            },
        };

        assert_ast_eq!(ast, expected);
    }

    #[test]
    fn should_parse_leak_statement() {
        const INPUT: &str = indoc! {r#"
        fn main() {
            leak a = 100
        }
        "#};

        let ast = parse_string(INPUT.to_owned()).unwrap_or_else(|e| panic!("{e}"));

        let expected = LeekAst {
            source_file: SourceFile {
                path: None,
                content: INPUT.to_owned(),
            },
            root: Program {
                constant_variables: vec![],
                static_variables: vec![],
                function_definitions: vec![FunctionDefinition {
                    name: "main".to_owned(),
                    struct_identifier: None,
                    parameters: vec![],
                    return_type: Type::Primitive(PrimitiveKind::Void),
                    body: Block {
                        statements: vec![Statement::VariableDeclaration(VariableDeclaration {
                            kind: VariableDeclarationKind::Local,
                            identifier: "a".to_owned(),
                            ty: None,
                            value: Expression::Atom(Atom::Literal(Literal {
                                kind: LiteralKind::Integer(IntegerKind::I32(100)),
                                span: Span::new(
                                    Position { row: 1, col: 13 },
                                    Position { row: 1, col: 16 },
                                ),
                            })),
                        })],
                    },
                }],
                struct_definitions: vec![],
                enum_definitions: vec![],
            },
        };

        assert_ast_eq!(ast, expected);
    }

    #[test]
    fn should_parse_assignment_statement() {
        const INPUT: &str = indoc! {r#"
        fn main() {
            a += 420
        }
        "#};

        let ast = parse_string(INPUT.to_owned()).unwrap_or_else(|e| panic!("{e}"));

        let expected = LeekAst {
            source_file: SourceFile {
                path: None,
                content: INPUT.to_owned(),
            },
            root: Program {
                constant_variables: vec![],
                static_variables: vec![],
                function_definitions: vec![FunctionDefinition {
                    name: "main".to_owned(),
                    struct_identifier: None,
                    parameters: vec![],
                    return_type: Type::Primitive(PrimitiveKind::Void),
                    body: Block {
                        statements: vec![Statement::VariableAssignment(VariableAssignment {
                            identifier: QualifiedIdentifier::new(None, "a".to_owned()),
                            operator: AssignmentOperator::PlusEquals,
                            value: Expression::Atom(Atom::Literal(Literal {
                                kind: LiteralKind::Integer(IntegerKind::I32(420)),
                                span: Span::new(
                                    Position { row: 1, col: 9 },
                                    Position { row: 1, col: 12 },
                                ),
                            })),
                        })],
                    },
                }],
                struct_definitions: vec![],
                enum_definitions: vec![],
            },
        };

        assert_ast_eq!(ast, expected);
    }

    #[test]
    fn should_parse_function_definition() {
        const INPUT: &str = indoc! {r#"
        fn add(a: i32, b: i32) -> i32 {
            yeet a + b
        }
        "#};

        let ast = parse_string(INPUT.to_owned()).unwrap_or_else(|e| panic!("{e}"));

        let expected = LeekAst {
            source_file: SourceFile {
                path: None,
                content: INPUT.to_owned(),
            },
            root: Program {
                constant_variables: vec![],
                static_variables: vec![],
                function_definitions: vec![FunctionDefinition {
                    name: "add".to_owned(),
                    struct_identifier: None,
                    parameters: vec![
                        FunctionParameter {
                            identifier: "a".to_owned(),
                            ty: Type::Primitive(PrimitiveKind::I32),
                        },
                        FunctionParameter {
                            identifier: "b".to_owned(),
                            ty: Type::Primitive(PrimitiveKind::I32),
                        },
                    ],
                    return_type: Type::Primitive(PrimitiveKind::I32),
                    body: Block {
                        statements: vec![Statement::Yeet(Expression::BinaryExpression(
                            BinaryExpression {
                                binary_operator: BinaryOperator::Plus,
                                lhs: Box::new(Expression::Atom(Atom::QualifiedIdentifier(
                                    QualifiedIdentifier::new(None, "a".to_owned()),
                                ))),
                                rhs: Box::new(Expression::Atom(Atom::QualifiedIdentifier(
                                    QualifiedIdentifier::new(None, "b".to_owned()),
                                ))),
                            },
                        ))],
                    },
                }],
                struct_definitions: vec![],
                enum_definitions: vec![],
            },
        };

        assert_ast_eq!(ast, expected);
    }
}
