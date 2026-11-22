//! Helpers shared by integration tests.
#![allow(dead_code)]

pub mod guard;
pub mod harness;
pub mod numeric;
pub mod random;
pub mod rng;

use formalith::{
    dynamic::SetChoice,
    parser::environment::Environment,
    printer::{PrettyPrint, PrintOptions},
};

/// Evaluate each statement in `set` with shared definitions, returning the result of the last one.
pub fn eval_statements(set: SetChoice, statements: &[&str], typst: bool) -> Result<String, String> {
    let mut env = Environment::new();
    let mut result = Ok(String::new());
    for statement in statements {
        result = set.eval(statement, typst, &mut env);
    }
    result
}

/// Split a series printed on a single line into its terms and the argument of its remainder `o(...)`, printed
/// last: `x+o(x^2)` gives `("x", Some("x^2"))`, and `o(x)` gives `("0", Some("x"))`.
pub fn split_remainder(line: &str) -> (String, Option<String>) {
    let argument = |rest: &str| {
        let inner = rest.strip_prefix("o(")?.strip_suffix(')')?;
        let mut depth = 0_i32;
        for c in inner.chars() {
            depth += match c {
                '(' => 1,
                ')' => -1,
                _ => 0,
            };
            if depth < 0 {
                return None;
            }
        }
        (depth == 0).then(|| inner.to_owned())
    };
    if let Some(arg) = argument(line) {
        return ("0".to_owned(), Some(arg));
    }
    line.rfind("+o(")
        .and_then(|i| Some((line[..i].to_owned(), Some(argument(&line[i + 1..])?))))
        .unwrap_or_else(|| (line.to_owned(), None))
}

/// Print on a single line, without colors.
pub fn line<T: PrettyPrint>(value: &T) -> String {
    format!("{}", value.with_options(PrintOptions::plain()))
}

/// Pretty print (2D layout), without colors.
pub fn pretty<T: PrettyPrint>(value: &T) -> String {
    format!(
        "{}",
        value.with_options(PrintOptions {
            pretty_print: true,
            ..PrintOptions::plain()
        })
    )
}

/// Print as typst math source.
pub fn typst<T: PrettyPrint>(value: &T) -> String {
    format!("{}", value.with_options(PrintOptions::typst()))
}
