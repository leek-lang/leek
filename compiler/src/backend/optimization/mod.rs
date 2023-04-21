use std::str::FromStr;

#[derive(Debug, Default)]
pub enum OptimizationLevel {
    #[default]
    None,
    Minimal,
    Normal,
    Maximum,
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
