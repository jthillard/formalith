//! Helpers shared by integration tests.
#![allow(dead_code)]

pub mod guard;
pub mod harness;
pub mod numeric;
pub mod random;
pub mod rng;

use formalith::{
    parser::environment::Environment,
    printer::{PrettyPrint, PrintOptions},
    repl::SetChoice,
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
