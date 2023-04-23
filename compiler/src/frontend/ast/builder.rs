use std::fmt::Display;

use crate::frontend::{
    ast::{
        AssignmentOperator, Atom, BinaryExpression, Block, FunctionCallExpression,
        FunctionDefinition, FunctionParameter, Statement, StructDefinition, StructFieldAccess,
        StructInitialization, StructMethodCall, UnaryExpression, VariableDeclaration,
        VariableDeclarationKind,
    },
    lexer::{KeywordKind, LeekToken, LeekTokenKind},
    parser::{ParseTree, ParseTreeNode, ParseTreeNodeNonTerminal, ParseTreeNonTerminalKind},
};

use super::{
    Expression, LeekAst, LiteralKind, PrimitiveKind, Program, QualifiedIdentifier, Type,
    VariableAssignment,
};

#[derive(Debug)]
pub struct AstBuildError {
    pub kind: AstBuildErrorKind,
}

impl Display for AstBuildError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self.kind {
            AstBuildErrorKind::InvalidNode(node) => {
                writeln!(f, "Invalid ParseTreeNode: {:?}", node)
            }
        }
    }
}

#[derive(Debug)]
pub enum AstBuildErrorKind {
    InvalidNode(ParseTreeNode),
}

impl LeekAst {
    pub fn build_from(parse_tree: ParseTree) -> Result<Self, AstBuildError> {
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

        ast.populate(parse_tree)?;

        Ok(ast)
    }

    fn populate(&mut self, parse_tree: ParseTree) -> Result<(), AstBuildError> {
        let program = parse_tree.root.non_terminal();
        assert!(program.kind == ParseTreeNonTerminalKind::Program);

        for node in &program.children {
            let ParseTreeNode::NonTerminal(top_level_node) = node else {
                return Err(node.into())
            };

            match top_level_node.kind {
                ParseTreeNonTerminalKind::ConstantVariableDeclaration => self
                    .root
                    .constant_variables
                    .push(VariableDeclaration::from_node(top_level_node)?),
                ParseTreeNonTerminalKind::StaticVariableDeclaration => self
                    .root
                    .static_variables
                    .push(VariableDeclaration::from_node(top_level_node)?),
                ParseTreeNonTerminalKind::FunctionDefinition => self
                    .root
                    .function_definitions
                    .push(FunctionDefinition::from_node(top_level_node)?),
                ParseTreeNonTerminalKind::StructDefinition => self
                    .root
                    .struct_definitions
                    .push(StructDefinition::from_node(top_level_node)?),
                _ => return Err(node.into()),
            }
        }

        Ok(())
    }
}

fn assert_nt_kind(
    node: &ParseTreeNodeNonTerminal,
    kind: ParseTreeNonTerminalKind,
) -> Result<(), AstBuildError> {
    if node.kind != kind {
        return Err(node.to_owned().into());
    }

    Ok(())
}

impl From<ParseTreeNode> for AstBuildError {
    fn from(node: ParseTreeNode) -> Self {
        AstBuildError {
            kind: AstBuildErrorKind::InvalidNode(node),
        }
    }
}

impl From<ParseTreeNodeNonTerminal> for AstBuildError {
    fn from(node: ParseTreeNodeNonTerminal) -> Self {
        AstBuildError {
            kind: AstBuildErrorKind::InvalidNode(ParseTreeNode::NonTerminal(node)),
        }
    }
}

impl From<&ParseTreeNode> for AstBuildError {
    fn from(node: &ParseTreeNode) -> Self {
        node.to_owned().into()
    }
}

impl From<&ParseTreeNodeNonTerminal> for AstBuildError {
    fn from(node: &ParseTreeNodeNonTerminal) -> Self {
        node.to_owned().into()
    }
}

trait FromNode
where
    Self: Sized,
{
    fn from_node(node: &ParseTreeNodeNonTerminal) -> Result<Self, AstBuildError>;
}

trait FromTerminal
where
    Self: Sized,
{
    fn from_terminal(node: &LeekToken) -> Result<Self, AstBuildError>;
}

impl FromNode for Type {
    fn from_node(type_node: &ParseTreeNodeNonTerminal) -> Result<Self, AstBuildError> {
        assert_nt_kind(type_node, ParseTreeNonTerminalKind::Type)?;

        let qualified_identifier_node = &type_node.children[0].non_terminal();

        assert_nt_kind(
            qualified_identifier_node,
            ParseTreeNonTerminalKind::QualifiedIdentifier,
        )?;

        let identifier = QualifiedIdentifier::from_node(qualified_identifier_node)?;

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
                _ => return Ok(Type::Identifier(identifier)),
            };

            return Ok(Type::Primitive(primitive_kind));
        }

        Ok(Type::Identifier(identifier))
    }
}

impl FromNode for QualifiedIdentifier {
    fn from_node(node: &ParseTreeNodeNonTerminal) -> Result<Self, AstBuildError> {
        assert!(node.children.len() >= 1);

        let name = node.children.last().unwrap().terminal_token().text.clone();

        let mut namespace = None;

        if node.children.len() > 1 {
            assert!(node.children.len() % 2 == 1);

            let mut parts = vec![];

            for i in 0..(node.children.len() - 1) / 2 {
                let id = node.children.get(i * 2).unwrap().terminal_token();

                parts.push(id.text.clone())
            }

            namespace = Some(parts)
        }

        Ok(QualifiedIdentifier { namespace, name })
    }
}

impl FromNode for VariableDeclaration {
    fn from_node(_node: &ParseTreeNodeNonTerminal) -> Result<Self, AstBuildError> {
        todo!()
    }
}

impl FromNode for Expression {
    fn from_node(node: &ParseTreeNodeNonTerminal) -> Result<Self, AstBuildError> {
        assert_nt_kind(node, ParseTreeNonTerminalKind::Expression)?;

        assert_eq!(node.children.len(), 1);

        let expression_node = &node.children[0].non_terminal();

        match expression_node.kind {
            ParseTreeNonTerminalKind::Atom => {
                let atom = Atom::from_node(expression_node)?;

                Ok(Expression::Atom(atom))
            }
            ParseTreeNonTerminalKind::UnaryExpression => {
                let unary_expression = UnaryExpression::from_node(expression_node)?;

                Ok(Expression::UnaryExpression(unary_expression))
            }
            ParseTreeNonTerminalKind::FunctionCallExpression => {
                let function_call_expression = FunctionCallExpression::from_node(expression_node)?;

                Ok(Expression::FunctionCallExpression(function_call_expression))
            }
            ParseTreeNonTerminalKind::BinaryExpression => {
                let binary_expression = BinaryExpression::from_node(expression_node)?;

                Ok(Expression::BinaryExpression(binary_expression))
            }
            ParseTreeNonTerminalKind::StructInitialization => {
                let struct_initialization = StructInitialization::from_node(expression_node)?;

                Ok(Expression::StructInitialization(struct_initialization))
            }
            ParseTreeNonTerminalKind::StructFieldAccess => {
                let struct_field_access = StructFieldAccess::from_node(expression_node)?;

                Ok(Expression::StructFieldAccess(struct_field_access))
            }
            ParseTreeNonTerminalKind::StructMethodCall => {
                let struct_method_call = StructMethodCall::from_node(expression_node)?;

                Ok(Expression::StructMethodCall(struct_method_call))
            }
            _ => unreachable!("Found invalid expression node"),
        }
    }
}

impl FromNode for Atom {
    fn from_node(node: &ParseTreeNodeNonTerminal) -> Result<Self, AstBuildError> {
        assert_nt_kind(node, ParseTreeNonTerminalKind::Atom)?;

        let atom = match &node.children[0] {
            ParseTreeNode::Terminal(terminal) => match terminal.kind {
                LeekTokenKind::StringLiteral => Atom::Literal(super::Literal {
                    kind: LiteralKind::String(terminal.text.clone()),
                    span: terminal.span.clone(),
                }),
                LeekTokenKind::CharLiteral => todo!(),
                LeekTokenKind::IntegerLiteral(_) => todo!(),
                LeekTokenKind::FloatLiteral => todo!(),
                LeekTokenKind::OpenParen => {
                    let expression = Expression::from_node(node.children[1].non_terminal())?;

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
                    let identifier = QualifiedIdentifier::from_node(non_terminal)?;

                    Atom::QualifiedIdentifier(identifier)
                }
                _ => unreachable!("Found invalid atom node"),
            },
        };

        Ok(atom)
    }
}

impl FromNode for UnaryExpression {
    fn from_node(_node: &ParseTreeNodeNonTerminal) -> Result<Self, AstBuildError> {
        todo!("build from unary expression")
    }
}

impl FromNode for FunctionCallExpression {
    fn from_node(node: &ParseTreeNodeNonTerminal) -> Result<Self, AstBuildError> {
        assert_nt_kind(node, ParseTreeNonTerminalKind::FunctionCallExpression)?;

        assert!(node.children.len() >= 3);
        assert!(node.children.len() <= 4);

        let identifier = QualifiedIdentifier::from_node(&node.children[0].non_terminal())?;

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

                assert_nt_kind(&non_terminal, ParseTreeNonTerminalKind::FunctionArguments)?;

                let mut arguments = vec![];

                for (index, argument) in non_terminal.children.iter().enumerate() {
                    if index % 2 == 1 {
                        assert_eq!(argument.terminal_token().kind, LeekTokenKind::Comma);
                        continue;
                    }

                    let argument = Expression::from_node(&argument.non_terminal())?;

                    arguments.push(argument)
                }

                arguments
            }
        };

        Ok(FunctionCallExpression {
            identifier,
            arguments,
        })
    }
}

impl FromNode for BinaryExpression {
    fn from_node(_node: &ParseTreeNodeNonTerminal) -> Result<Self, AstBuildError> {
        todo!("build from binary expression")
    }
}

impl FromNode for StructInitialization {
    fn from_node(_node: &ParseTreeNodeNonTerminal) -> Result<Self, AstBuildError> {
        todo!("build from struct initialization")
    }
}

impl FromNode for StructFieldAccess {
    fn from_node(_node: &ParseTreeNodeNonTerminal) -> Result<Self, AstBuildError> {
        todo!("build from struct field access")
    }
}

impl FromNode for StructMethodCall {
    fn from_node(_node: &ParseTreeNodeNonTerminal) -> Result<Self, AstBuildError> {
        todo!("build from struct method call")
    }
}

impl FromNode for FunctionDefinition {
    fn from_node(node: &ParseTreeNodeNonTerminal) -> Result<Self, AstBuildError> {
        assert_nt_kind(node, ParseTreeNonTerminalKind::FunctionDefinition)?;

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
            _ => unreachable!(),
        };

        /* Build the function identifier and struct identifier (if any) */

        let QualifiedIdentifier { name, namespace } =
            QualifiedIdentifier::from_node(identifier.non_terminal())?;

        let struct_identifier = match namespace {
            Some(n) => {
                if n.len() == 1 {
                    n.first().map(|s| s.to_owned())
                } else {
                    panic!("Function name qualified identifier had more than one namespace value");
                    return Err(node.into());
                }
            }
            None => None,
        };

        /* Build the function parameters */

        // Make sure that the param node is correct
        assert_nt_kind(
            &parameters.non_terminal(),
            ParseTreeNonTerminalKind::FunctionParameters,
        )?;

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
            )?)
        }

        let return_type = match return_type {
            Some(function_return_type_node) => {
                let function_return_type = function_return_type_node.non_terminal();

                assert_nt_kind(
                    &function_return_type,
                    ParseTreeNonTerminalKind::FunctionReturnType,
                )?;

                assert_eq!(
                    function_return_type.children[0].terminal_token().kind,
                    LeekTokenKind::Arrow
                );

                let type_node = &function_return_type.children[1].non_terminal();

                Type::from_node(type_node)?
            }
            None => Type::Primitive(PrimitiveKind::Void),
        };

        let block = block.non_terminal();
        let block = Block::from_node(block)?;

        Ok(FunctionDefinition {
            name,
            struct_identifier,
            parameters,
            return_type,
            body: block,
        })
    }
}

impl FromNode for FunctionParameter {
    fn from_node(node: &ParseTreeNodeNonTerminal) -> Result<Self, AstBuildError> {
        assert_nt_kind(node, ParseTreeNonTerminalKind::TypeAssociation)?;

        assert!(node.children.len() == 3);

        let identifier = node.children[0].terminal_token().text.clone();

        assert!(node.children[1].terminal_token().kind == LeekTokenKind::Colon);

        let ty = Type::from_node(node.children[2].non_terminal())?;

        Ok(FunctionParameter { identifier, ty })
    }
}

impl FromNode for Block {
    fn from_node(node: &ParseTreeNodeNonTerminal) -> Result<Self, AstBuildError> {
        assert_nt_kind(node, ParseTreeNonTerminalKind::Block)?;

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
            let statement = Statement::from_node(node.children[i].non_terminal())?;
            statements.push(statement);
        }

        Ok(Block { statements })
    }
}

impl FromTerminal for AssignmentOperator {
    fn from_terminal(node: &LeekToken) -> Result<Self, AstBuildError> {
        Ok(match node.kind {
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
                return Err(AstBuildError {
                    kind: AstBuildErrorKind::InvalidNode(ParseTreeNode::Terminal(node.clone())),
                })
            }
        })
    }
}

impl FromNode for Statement {
    fn from_node(node: &ParseTreeNodeNonTerminal) -> Result<Self, AstBuildError> {
        assert_nt_kind(node, ParseTreeNonTerminalKind::Statement)?;

        match &node.children[0] {
            ParseTreeNode::Terminal(terminal) => {
                let LeekTokenKind::Keyword(keyword) = terminal.kind else {
                   return Err(node.children[0].clone().into());
                };

                match keyword {
                    KeywordKind::Yeet => {
                        let expression = Expression::from_node(node.children[1].non_terminal())?;
                        Ok(Statement::Yeet(expression))
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

                        let value = Expression::from_node(node.children[3].non_terminal())?;

                        Ok(Statement::VariableDeclaration(VariableDeclaration {
                            kind: VariableDeclarationKind::Local,
                            identifier,
                            ty: None,
                            value,
                        }))
                    }

                    _ => unreachable!("Statement node began with non-statement keyword"),
                }
            }
            ParseTreeNode::NonTerminal(non_terminal) => match non_terminal.kind {
                ParseTreeNonTerminalKind::QualifiedIdentifier => {
                    let identifier =
                        QualifiedIdentifier::from_node(&node.children[0].non_terminal())?;
                    let operator =
                        AssignmentOperator::from_terminal(&node.children[1].terminal_token())?;
                    let value = Expression::from_node(&node.children[2].non_terminal())?;

                    Ok(Statement::VariableAssignment(VariableAssignment {
                        identifier,
                        operator,
                        value,
                    }))
                }
                ParseTreeNonTerminalKind::FunctionCallExpression => Ok(Statement::FunctionCall(
                    FunctionCallExpression::from_node(non_terminal)?,
                )),
                _ => unreachable!("Statement node began with non-statement non-terminal"),
            },
        }
    }
}

impl FromNode for StructDefinition {
    fn from_node(node: &ParseTreeNodeNonTerminal) -> Result<Self, AstBuildError> {
        assert_nt_kind(node, ParseTreeNonTerminalKind::StructDefinition)?;

        todo!()
    }
}
