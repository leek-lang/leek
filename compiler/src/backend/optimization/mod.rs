use std::str::FromStr;

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

impl FromStr for OptimizationLevel {
    type Err = ();

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(match s {
            "0" => Self::None,
            "1" => Self::Minimal,
            "2" => Self::Normal,
            "3" => Self::Maximum,
            "z" => Self::Size,
            _ => return Err(()),
        })
    }
}

impl ToString for OptimizationLevel {
    fn to_string(&self) -> String {
        match self {
            Self::None => "0",
            Self::Minimal => "1",
            Self::Normal => "2",
            Self::Maximum => "3",
            Self::Size => "z",
        }
        .to_owned()
    }
}
