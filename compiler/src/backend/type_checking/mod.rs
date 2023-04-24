use std::fmt::Display;

use crate::frontend::position::{highlight_span, SourceFile, Span};

#[derive(Debug)]
pub enum TypeCheckingErrorKind {
    DuplicateFunctionIdentifier {
        identifier_name: String,
        first: Span,
        second: Span,
    }, // Function with same name defined twice
    DuplicateGlobalVariableIdentifier, // Constant and static variables in global scope defined twice or conflictingly
    DuplicateParameterIdentifier,      // Multiple function parameters with same name
    DuplicateLocalVariableIdentifier,  // Local function stack variables with same name
    DuplicateStructIdentifier,         // Same struct name defined twice
    DuplicateEnumIdentifier,           // Same enum name defined twice
    DuplicateStructFieldIdentifier,    // Same fields defined twice in the struct
    DuplicateStructMethodIdentifier,   // Same method defined twice on the struct
    DuplicateEnumVariantIdentifier,    // Same variant defined twice in the enum

    FunctionArgumentTypeMismatch, // Arguments should match type signatures (or coerce to them)
    MissingFunctionArguments,
    TooManyFunctionArguments,

    StructInitializationFieldTypeMismatch, // Struct fields should match type signatures (or coerce to them)
    UnknownStructInitializationFieldIdentifier, // Struct field does not exist on struct when trying to initialize
    MissingStructInitializationFieldIdentifier, // Missing a required field of the struct when trying to initialize
    DuplicateStructInitializationFieldIdentifier, // Same field passed twice when trying to initialize

    UnknownNamespaceIdentifier,    // Namespace not found
    UnknownFunctionIdentifier,     // Function name not found
    UnknownVariableIdentifier,     // Variable (local or global) or struct or enum not found
    UnknownStructFieldIdentifier,  // Field on struct not found
    UnknownStructMethodIdentifier, // Method on struct not found
    UnknownEnumVariantIdentifier,  // Enum variant does not exist on enum

    UndefinedOperation, // Binary or Unary or Assignment operator is not implemented for the types (i32 and str addition)
    IdentifierIsNotAFunction, // Trying to call a variable as if it were a function `leak a = 3; a();`
    ExpressionIsNotAFunction, // Trying to call an expression as if it were a function `(a + b)()`
    ModificationOfConstant,   // Trying to overwrite a constant variable
    VariableExplicitTypeMismatch, // Explicit type of variable does not match right side of assignment
    FunctionReturnTypeMismatch,   // Function return type was different than expected
}

#[derive(Debug)]
pub struct TypeCheckingError {
    pub kind: TypeCheckingErrorKind,
    pub source_file: SourceFile,
}

impl Display for TypeCheckingError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self.kind {
            TypeCheckingErrorKind::DuplicateFunctionIdentifier {
                identifier_name,
                first,
                second,
            } => {
                writeln!(
                    f,
                    "Function identifier `{identifier_name}` is defined twice!"
                )?;

                highlight_span(f, &self.source_file, *first)?;
                highlight_span(f, &self.source_file, *second)?;
            }
            _ => {
                todo!("display messages for other errors")
            }
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use ansi_term::Color;
    use indoc::indoc;

    use crate::frontend::position::{Position, SourceFile, Span};

    use super::{TypeCheckingError, TypeCheckingErrorKind};

    fn compare_expected_to_actual(expected: &str, actual: &str) {
        if expected == actual {
            return;
        }

        let mut output = String::new();

        for diff in diff::lines(actual, expected) {
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

        panic!(
            concat!(
                "Input (red) did not match Expected (green):\n",
                "==========================\n",
                "{}",
                "==========================\n"
            ),
            output
        );
    }

    #[test]
    fn format_duplicate_function_identifier() {
        let source_file = SourceFile {
            path: None,
            content: indoc! {r#"
                fn my_func() {
                    println("first impl")
                }

                fn my_func() {
                    println("second impl")
                }
            "#}
            .to_owned(),
        };

        let error = TypeCheckingError {
            kind: TypeCheckingErrorKind::DuplicateFunctionIdentifier {
                identifier_name: "my_func".to_owned(),
                first: Span::new(Position { row: 0, col: 3 }, Position { row: 0, col: 10 }),
                second: Span::new(Position { row: 4, col: 3 }, Position { row: 4, col: 10 }),
            },
            source_file,
        };

        let expected = indoc! {r#"
            Function identifier `my_func` is defined twice!
            1:4
              1: fn my_func() {
                    ^^^^^^^
                    here
            5:4
              3: }
              4: 
              5: fn my_func() {
                    ^^^^^^^
                    here
        "#};

        compare_expected_to_actual(expected, &format!("{error}"));
    }
}
