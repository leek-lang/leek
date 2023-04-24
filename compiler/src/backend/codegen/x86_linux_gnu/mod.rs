use indoc::indoc;
use std::{path::PathBuf, process::Command};

use crate::{backend::CompilerOptions, frontend::ast::LeekAst};

use super::CodeGenerator;

pub struct CodeGeneratorX86LinuxGNU;

impl CodeGenerator for CodeGeneratorX86LinuxGNU {
    fn generate_assembly(&self, _ast: LeekAst, _compiler_options: &CompilerOptions) -> String {
        String::from(indoc! {"
            global main
    
            section .data
                ; Line 2
                msg: db \"Hello, world!\", 0xa
                msg_len: equ $ - msg
    
            section .text
    
            main:
                ; Line 1
                push ebp
                mov ebp, esp
    
                ; Line 2
                mov eax, 4
                mov ebx, 1
                mov ecx, msg
                mov edx, msg_len
                int 0x80
    
                ; Line 3
                mov eax, 0
                mov esp, ebp
                pop ebp
                ret
            "
        })
    }

    fn create_assembler_command(&self, input_file: &PathBuf, output_file: &PathBuf) -> Command {
        let mut cmd = Command::new("nasm");

        cmd.args([
            "-f",
            "elf32",
            "-o",
            output_file
                .to_str()
                .expect("Could not convert output_file to string"),
            input_file
                .to_str()
                .expect("Could not convert input_file to string"),
        ]);

        cmd
    }

    fn create_linker_command(&self, input_file: &PathBuf, output_file: &PathBuf) -> Command {
        let mut cmd = Command::new("gcc");

        cmd.args([
            "-m32",
            "-o",
            output_file
                .to_str()
                .expect("Could not convert output_file to string"),
            input_file
                .to_str()
                .expect("Could not convert input_file to string"),
        ]);

        cmd
    }
}
