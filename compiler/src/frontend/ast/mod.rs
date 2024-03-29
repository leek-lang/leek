use crate::common::lang::{AssignmentOperator, BinaryOperator, PrimitiveKind, UnaryOperator};

use super::position::{SourceFile, Span};

pub mod builder;

#[derive(Debug)]
pub struct Ast {
    pub source_file: SourceFile,
    pub items: Vec<ProgramPart>,
}

impl PartialEq for Ast {
    fn eq(&self, other: &Self) -> bool {
        self.items == other.items
    }
}

#[derive(Debug, PartialEq)]
pub enum ProgramPart {
    ConstantVariable(VariableDeclaration),
    StaticVariable(VariableDeclaration),
    FunctionDefinition(FunctionDefinition),
    StructDefinition(StructDefinition),
    EnumDefinition(EnumDefinition),
}

#[derive(Debug, PartialEq)]
pub enum Type {
    Primitive(PrimitiveKind),
    Identifier(QualifiedIdentifier),
}

#[derive(Debug, PartialEq, Eq)]
pub struct QualifiedIdentifier {
    pub namespace: Option<Vec<String>>,
    pub name: String,
}

impl QualifiedIdentifier {
    pub fn new(namespace: Option<Vec<String>>, name: String) -> Self {
        Self { namespace, name }
    }

    pub fn namespace(&self) -> Option<&Vec<String>> {
        self.namespace.as_ref()
    }

    pub fn has_namespace(&self) -> bool {
        self.namespace.is_some()
    }

    pub fn name(&self) -> &String {
        &self.name
    }
}

#[derive(Debug, PartialEq)]
pub struct VariableDeclaration {
    pub kind: VariableDeclarationKind,
    pub identifier: String,
    pub ty: Option<Type>,
    pub value: Expression,
}

#[derive(Debug, PartialEq)]
pub enum VariableDeclarationKind {
    Constant,
    Static,
    Local,
}

#[derive(Debug, PartialEq)]
pub struct VariableAssignment {
    pub identifier: QualifiedIdentifier,
    pub operator: AssignmentOperator,
    pub value: Expression,
}

#[derive(Debug, PartialEq)]
pub enum Expression {
    Atom(Atom),
    UnaryExpression(UnaryExpression),
    FunctionCallExpression(FunctionCallExpression),
    BinaryExpression(BinaryExpression),
    StructInitialization(StructInitialization),
    StructFieldAccess(StructFieldAccess),
    StructMethodCall(StructMethodCall),
}

#[derive(Debug, PartialEq)]
pub enum Atom {
    QualifiedIdentifier(QualifiedIdentifier),
    Literal(Literal),
    ParenthesizedExpression(Box<Expression>),
}

#[derive(Debug, PartialEq)]
pub struct Literal {
    pub kind: LiteralKind,
    pub span: Span,
}

#[derive(Debug, PartialEq)]
pub enum LiteralKind {
    Integer(IntegerKind),
    Float(FloatKind),
    Char(char),
    String(String),
}

#[derive(Debug, PartialEq)]
pub enum IntegerKind {
    I8(i8),
    U8(u8),
    I16(i16),
    U16(u16),
    I32(i32),
    U32(u32),
    I64(i64),
    U64(u64),
}

#[derive(Debug, PartialEq)]
pub enum FloatKind {
    F32(f32),
    F64(f64),
}

#[derive(Debug, PartialEq)]
pub struct UnaryExpression {
    pub unary_operator: UnaryOperator,
    pub expression: Box<Expression>,
}

#[derive(Debug, PartialEq)]
pub struct BinaryExpression {
    pub binary_operator: BinaryOperator,
    pub lhs: Box<Expression>,
    pub rhs: Box<Expression>,
}

#[derive(Debug, PartialEq)]
pub struct FunctionDefinition {
    pub name: String,
    pub struct_identifier: Option<String>,
    pub parameters: Vec<FunctionParameter>,
    pub return_type: Type,
    pub body: Block,
}

#[derive(Debug, PartialEq)]
pub struct FunctionParameter {
    pub identifier: String,
    pub ty: Type,
}

#[derive(Debug, PartialEq)]
pub struct Block {
    pub statements: Vec<Statement>,
}

#[derive(Debug, PartialEq)]
pub enum Statement {
    Block(Block),
    Yeet(Expression),
    VariableDeclaration(VariableDeclaration),
    VariableAssignment(VariableAssignment),
    FunctionCall(FunctionCallExpression),
}

#[derive(Debug, PartialEq)]
pub struct FunctionCallExpression {
    pub identifier: QualifiedIdentifier,
    pub arguments: Vec<Expression>,
}

#[derive(Debug, PartialEq)]
pub struct StructDefinition {
    pub name: String,
    pub fields: Vec<StructField>,
}

#[derive(Debug, PartialEq)]
pub struct StructField {
    pub identifier: String,
    pub ty: Type,
}

#[derive(Debug, PartialEq)]
pub struct EnumDefinition {
    pub name: String,
    pub variants: Vec<String>,
}

#[derive(Debug, PartialEq)]
pub struct StructInitialization {
    pub identifier: QualifiedIdentifier,
    pub arguments: Vec<StructInitializationField>,
}

#[derive(Debug, PartialEq)]
pub struct StructInitializationField {
    pub identifier: String,
    pub value: Expression,
}

#[derive(Debug, PartialEq)]
pub struct StructFieldAccess {
    pub identifier: QualifiedIdentifier,
    pub field: String,
}

#[derive(Debug, PartialEq)]
pub struct StructMethodCall {
    pub callee: Box<Expression>,
    pub method: String,
    pub arguments: Vec<Expression>,
}
