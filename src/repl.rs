//! Evaluation of expressions in a set chosen at runtime, shared by the command line and web interfaces.

use std::str::FromStr;

use crate::{
    field::{Set, complex::C, integer::Z, matrix::M, natural::N, real::R},
    printer::{Print, PrintOptions},
    try_parse,
};

/// The sets expressions can be evaluated in.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SetChoice {
    /// Natural integers.
    N,
    /// Integers.
    Z,
    /// Rationals.
    R,
    /// Complex numbers.
    C,
    /// Matrices with rational coefficients.
    M,
}

impl SetChoice {
    /// Every available set.
    pub const ALL: [Self; 5] = [Self::N, Self::Z, Self::R, Self::C, Self::M];

    /// The name used to select the set.
    #[must_use]
    pub const fn name(self) -> &'static str {
        match self {
            Self::N => "N",
            Self::Z => "Z",
            Self::R => "R",
            Self::C => "C",
            Self::M => "M",
        }
    }

    /// A short description of the set.
    #[must_use]
    pub const fn description(self) -> &'static str {
        match self {
            Self::N => "natural integers",
            Self::Z => "integers",
            Self::R => "rationals",
            Self::C => "complex numbers, `i` is the imaginary unit",
            Self::M => "matrices with rational coefficients, like [[1, 2], [3, 4]]",
        }
    }

    /// Parse and evaluate `input` in this set, printed as Typst math source if `typst` is set.
    ///
    /// # Errors
    /// Returns the parsing error message if `input` is not a valid expression.
    ///
    /// # Panics
    /// Panics if an operation is not supported by the set.
    pub fn eval(self, input: &str, typst: bool) -> Result<String, String> {
        match self {
            Self::N => eval_in(input, N, typst),
            Self::Z => eval_in(input, Z, typst),
            Self::R => eval_in(input, R, typst),
            Self::C => eval_in(input, C, typst),
            Self::M => eval_in(input, M, typst),
        }
    }
}

impl FromStr for SetChoice {
    type Err = String;

    fn from_str(name: &str) -> Result<Self, Self::Err> {
        Self::ALL
            .into_iter()
            .find(|set| set.name().eq_ignore_ascii_case(name))
            .ok_or_else(|| format!("unknown set `{name}`\n{}", sets_help()))
    }
}

/// List the available sets with their description.
#[must_use]
pub fn sets_help() -> String {
    let mut help = String::from("available sets:");
    for set in SetChoice::ALL {
        help.push_str(&format!("\n  {}  {}", set.name(), set.description()));
    }
    help
}

fn eval_in<E: Set>(input: &str, set: E, typst: bool) -> Result<String, String> {
    try_parse!(input, set)
        .map(|term| {
            if typst {
                term.with_options(PrintOptions::typst()).to_string()
            } else {
                term.to_string()
            }
        })
        .map_err(|err| err.to_string())
}
