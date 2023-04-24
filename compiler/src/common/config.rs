use std::path::PathBuf;

use clap::ValueEnum;

#[derive(Debug, Default, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, ValueEnum)]
pub enum OptimizationLevel {
    #[default]
    #[value(name = "0", help = "None (default)")]
    None,
    #[value(name = "1", help = "AST optimization is done")]
    Minimal,
    #[value(name = "2", help = "AST and assembly stack optimization is done")]
    Normal,
    #[value(
        name = "3",
        help = "AST, assembly stack, and SIMD optimization is done"
    )]
    Maximum,
    #[value(
        name = "z",
        help = "Output is optimized to contain the smallest possible size"
    )]
    Size,
}

#[derive(Debug, Default)]
pub enum BuildMode {
    #[default]
    Debug,
    Release,
}

#[derive(Debug, Default, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, ValueEnum)]
pub enum EmitMode {
    #[default]
    #[value(name = "exe", help = "executable file")]
    ExecutableFile,
    #[value(name = "obj", help = "object file")]
    ObjectFile,
    #[value(name = "asm", help = "assembly file")]
    AssemblyFile,
}

pub struct LeekCompilerConfig {
    pub opt_level: OptimizationLevel,
    pub build_mode: BuildMode,
    pub emit_mode: EmitMode,
    pub input_files: Vec<PathBuf>,
    pub output_name: Option<PathBuf>,
    pub verbose: bool,
}
