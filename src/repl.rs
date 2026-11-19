//! Evaluation of expressions in a set chosen at runtime, shared by the command line and web interfaces.

use std::{fmt, str::FromStr};

use crate::{
    context::{Context, Symbol},
    field::{
        Set, SetParseExpression, complex::C, integer::Z, matrix::M, modular::Zn, natural::N,
        real::R,
    },
    parser::environment::{Environment, Statement, head},
    printer::{Print, PrintOptions},
    term::TermSet,
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
    /// Matrices with integer coefficients.
    MZ,
    /// Matrices with coefficients modulo `n`.
    MZn(u64),
    /// Integers modulo `n`.
    Zn(u64),
    /// Polynomials in a variable, with coefficients in a set.
    Poly(Coefficients, Symbol),
}

/// The sets of coefficients of polynomials which can be evaluated in [`SetChoice::Poly`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Coefficients {
    /// Rationals.
    R,
    /// Complex numbers.
    C,
    /// Integers modulo `n`.
    Zn(u64),
}

impl SetChoice {
    /// Every set which isn't parameterized.
    pub const ALL: [Self; 6] = [Self::N, Self::Z, Self::R, Self::C, Self::M, Self::MZ];

    /// The name used to select the set, like `Z/7` or `R[x]`.
    #[must_use]
    pub fn name(self) -> String {
        self.to_string()
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
            Self::MZ => "matrices with integer coefficients, with hermite and smith normal forms",
            Self::MZn(_) => "matrices with coefficients modulo n, like M(Z/6)",
            Self::Zn(_) => "integers modulo n, a field when n is prime, like Z/7",
            Self::Poly(..) => {
                "polynomials in x with coefficients in K = R, C or Z/n, like R[x] or Z/2[t]"
            }
        }
    }

    /// Parse and evaluate `input` in this set, printed as Typst math source if `typst` is set.
    ///
    /// `input` can also be a definition, like `f(x) := x^2`, or assumptions, like `assume(a > 0)`, stored in
    /// `env`, or a system of equations, like `x + y = 3, x - y = 1`, which is solved.
    ///
    /// # Errors
    /// Returns the parsing error message if `input` is not a valid expression or definition.
    ///
    /// # Panics
    /// Panics if an operation is not supported by the set.
    pub fn eval(self, input: &str, typst: bool, env: &mut Environment) -> Result<String, String> {
        match self {
            Self::N => eval_in(input, N, typst, env),
            Self::Z => eval_in(input, Z, typst, env),
            Self::R => eval_in(input, R, typst, env),
            Self::C => eval_in(input, C, typst, env),
            Self::M => eval_in(input, M, typst, env),
            Self::MZ => eval_in(input, M::new(TermSet::new(Z)), typst, env),
            Self::MZn(n) => eval_in(input, M::new(TermSet::new(Zn::new(n))), typst, env),
            Self::Zn(n) => eval_in(input, Zn::new(n), typst, env),
            Self::Poly(Coefficients::R, x) => eval_in(input, R.get_polynomial_ring(x), typst, env),
            Self::Poly(Coefficients::C, x) => eval_in(input, C.get_polynomial_ring(x), typst, env),
            Self::Poly(Coefficients::Zn(n), x) => {
                eval_in(input, Zn::new(n).get_polynomial_ring(x), typst, env)
            }
        }
    }
}

impl fmt::Display for SetChoice {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::N => f.write_str("N"),
            Self::Z => f.write_str("Z"),
            Self::R => f.write_str("R"),
            Self::C => f.write_str("C"),
            Self::M => f.write_str("M"),
            Self::MZ => f.write_str("M(Z)"),
            Self::MZn(n) => write!(f, "M(Z/{n})"),
            Self::Zn(n) => write!(f, "Z/{n}"),
            Self::Poly(coefficients, x) => {
                let coefficients = match coefficients {
                    Coefficients::R => Self::R,
                    Coefficients::C => Self::C,
                    Coefficients::Zn(n) => Self::Zn(*n),
                };
                write!(f, "{coefficients}[{}]", x.name())
            }
        }
    }
}

/// Check if `name` is an identifier which can be used as a polynomial variable.
fn is_variable_name(name: &str) -> bool {
    name.starts_with(|c: char| c.is_ascii_alphabetic() || c == '_')
        && name.chars().all(|c| c.is_ascii_alphanumeric() || c == '_')
        && !["true", "false"].contains(&name)
}

impl FromStr for SetChoice {
    type Err = String;

    /// Parse a set name, like `R`, `Z/7` (or `Z/7Z`) or `Z/2[x]`, ignoring the case of set letters.
    fn from_str(name: &str) -> Result<Self, Self::Err> {
        let name = name.trim();
        if let Some(entries) = name
            .strip_prefix(['M', 'm'])
            .and_then(|n| n.trim_start().strip_prefix('('))
            .and_then(|n| n.strip_suffix(')'))
        {
            return match entries.parse()? {
                Self::R => Ok(Self::M),
                Self::Z => Ok(Self::MZ),
                Self::Zn(n) => Ok(Self::MZn(n)),
                entries => Err(format!(
                    "matrices with coefficients in {entries} are not supported, use R, Z or Z/n"
                )),
            };
        }
        if let Some((base, variable)) = name.strip_suffix(']').and_then(|n| n.split_once('[')) {
            let variable = variable.trim();
            let coefficients = match base.trim().parse()? {
                Self::R => Coefficients::R,
                Self::C if variable != "i" => Coefficients::C,
                Self::C => return Err("`i` is the imaginary unit of C".to_owned()),
                Self::Zn(n) => Coefficients::Zn(n),
                base => {
                    return Err(format!(
                        "polynomials with coefficients in {base} are not supported, use R, C or Z/n"
                    ));
                }
            };
            if !is_variable_name(variable) {
                return Err(format!("invalid variable `{variable}`"));
            }
            let variable = Symbol::new(variable);
            if Context::builtin_arity(variable).is_some() {
                let kind = if Context::is_builtin_constant(variable) {
                    "constant"
                } else {
                    "function"
                };
                return Err(format!("`{}` is a builtin {kind}", variable.name()));
            }
            return Ok(Self::Poly(coefficients, variable));
        }
        if let Some(modulus) = name
            .strip_prefix(['Z', 'z'])
            .and_then(|n| n.trim_start().strip_prefix('/'))
        {
            let modulus = modulus.trim();
            let modulus = modulus.strip_suffix(['Z', 'z']).unwrap_or(modulus).trim();
            return match modulus.parse::<u64>() {
                Ok(n) if (2..=1 << 63).contains(&n) => Ok(Self::Zn(n)),
                _ => Err(format!(
                    "invalid modulus `{modulus}`, expected an integer between 2 and 2^63"
                )),
            };
        }
        Self::ALL
            .into_iter()
            .find(|set| set.name().eq_ignore_ascii_case(name))
            .ok_or_else(|| format!("unknown set `{name}`\n{}", sets_help()))
    }
}

/// List the available sets with their description.
#[must_use]
pub fn sets_help() -> String {
    let x = Symbol::new("x");
    let mut help = String::from("available sets:");
    for (name, set) in SetChoice::ALL
        .into_iter()
        .map(|set| (set.name(), set))
        .chain([
            ("Z/n".to_owned(), SetChoice::Zn(2)),
            ("M(Z/n)".to_owned(), SetChoice::MZn(2)),
            ("K[x]".to_owned(), SetChoice::Poly(Coefficients::R, x)),
        ])
    {
        help.push_str(&format!("\n  {name:<6} {}", set.description()));
    }
    help
}

fn eval_in<E: SetParseExpression>(
    input: &str,
    set: E,
    typst: bool,
    env: &mut Environment,
) -> Result<String, String> {
    let print = |term: &crate::term::Term<E>| {
        if typst {
            term.with_options(PrintOptions::typst()).to_string()
        } else {
            term.to_string()
        }
    };
    match env.eval(input, set).map_err(|err| err.to_string())? {
        Statement::Expression(term) => Ok(print(&term)),
        Statement::Definition {
            name, params, body, ..
        } => Ok(format!("{} := {}", head(name, &params), print(&body))),
        Statement::System { solution, .. } => Ok(if typst {
            solution.with_options(PrintOptions::typst()).to_string()
        } else {
            solution.to_string()
        }),
        Statement::Ode { solution, .. } => Ok(if typst {
            solution.with_options(PrintOptions::typst()).to_string()
        } else {
            solution.to_string()
        }),
        Statement::Assume(assumptions) if assumptions.is_empty() => Ok(if typst {
            "\"no assumption\"".to_owned()
        } else {
            "no assumption".to_owned()
        }),
        Statement::Assume(assumptions) => Ok(assumptions.describe(typst)),
    }
}

/// The definitions of `env`, one per line, then its assumptions as an `assume` statement.
#[must_use]
pub fn definitions(env: &Environment) -> String {
    let mut lines: Vec<_> = env.definitions().map(ToString::to_string).collect();
    if !env.assumptions().is_empty() {
        lines.push(format!("assume({})", env.assumptions()));
    }
    lines.join("\n")
}

/// Remove the definition and assumptions of `name` from `env`, or every definition and assumption if `name` is
/// empty.
///
/// # Errors
/// Returns an error message if `name` is neither defined nor has assumptions.
pub fn clear_definitions(env: &mut Environment, name: &str) -> Result<(), String> {
    if name.is_empty() {
        env.clear();
        Ok(())
    } else if env.remove(name) | env.remove_assumptions(name) {
        Ok(())
    } else {
        Err(format!("`{name}` is not defined"))
    }
}
