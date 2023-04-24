#[derive(Debug, PartialEq)]
pub enum PrimitiveKind {
    Void,
    I8,
    I16,
    I32,
    I64,
    U8,
    U16,
    U32,
    U64,
    F32,
    F64,
}

#[derive(Debug, PartialEq)]
pub enum AssignmentOperator {
    Equals,
    PlusEquals,
    MinusEquals,
    MultiplyEquals,
    DivideEquals,
    ModuloEquals,
    BitwiseNotEquals,
    BitwiseXorEquals,
    BitwiseOrEquals,
    BitwiseAndEquals,
    LogicalNotEquals,
    ExponentiationEquals,
    LeftShiftEquals,
    RightShiftEquals,
    LogicalOrEquals,
    LogicalAndEquals,
}

#[derive(Debug, PartialEq)]
pub enum BinaryOperator {
    DoubleEquals,
    LessThan,
    LessThanOrEqual,
    GreaterThan,
    GreaterThanOrEqual,
    Plus,
    Minus,
    Asterisk,
    Divide,
    Modulo,
    BitwiseXor,
    BitwiseOr,
    BitwiseAnd,
    Exponentiation,
    LeftShift,
    RightShift,
    LogicalOr,
    LogicalAnd,
}

#[derive(Debug, PartialEq)]
pub enum UnaryOperator {
    BitwiseNot,
    LogicalNot,
    Asterisk,
}
