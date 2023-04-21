use std::{path::PathBuf, process::Command, str::FromStr};

use crate::frontend::ast::LeekAst;

use self::x86_linux_gnu::CodeGeneratorX86LinuxGNU;

use super::CompilerOptions;

pub mod x86_64_linux_gnu;
pub mod x86_linux_gnu;

pub trait CodeGenerator {
    fn generate_assembly(&self, ast: LeekAst, compiler_options: &CompilerOptions) -> String;
    fn create_assembler_command(&self, input_file: &PathBuf, output_file: &PathBuf) -> Command;
    fn create_linker_command(&self, input_file: &PathBuf, output_file: &PathBuf) -> Command;
}

#[allow(non_camel_case_types)]
pub enum CodeGenTarget {
    x86LinuxGNU,
    x86_64LinuxGNU,
}

impl CodeGenTarget {
    pub fn get_code_generator(&self) -> impl CodeGenerator {
        match self {
            CodeGenTarget::x86LinuxGNU => CodeGeneratorX86LinuxGNU,
            CodeGenTarget::x86_64LinuxGNU => todo!(),
        }
    }
}

impl FromStr for CodeGenTarget {
    type Err = ();

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(match s {
            "x86-linux-gnu" => Self::x86LinuxGNU,
            "x86_64-linux-gnu" => Self::x86LinuxGNU,
            _ => return Err(()),
        })
    }
}

impl ToString for CodeGenTarget {
    fn to_string(&self) -> String {
        match self {
            CodeGenTarget::x86LinuxGNU => "x86-linux-gnu",
            CodeGenTarget::x86_64LinuxGNU => "x86_64-linux-gnu",
        }
        .to_owned()
    }
}
