//! Bindings exposing the Formalith command line interface to the browser.

use std::cell::RefCell;

use formalith::{
    parser::{Parser, environment::Environment},
    repl::{self, SetChoice},
};
use wasm_bindgen::prelude::*;

thread_local! {
    /// Variables and functions defined by the user. Lost when the wasm instance aborts on a panic.
    static ENV: RefCell<Environment> = RefCell::new(Environment::new());
}

/// Log panic messages to the browser console.
#[wasm_bindgen(start)]
pub fn start() {
    console_error_panic_hook::set_once();
}

/// Parse and evaluate `input` in the set named `set`, printed as Typst math source if `typst` is set.
///
/// `input` can also be a definition, like `f(x) := x^2`, used by the next evaluations.
///
/// # Errors
/// Returns an error message if the set is unknown or `input` is not a valid expression or definition.
///
/// Operations unsupported by the set panic, which aborts the wasm instance: the caller has to reload it.
#[wasm_bindgen(js_name = evaluate)]
pub fn eval(input: &str, set: &str, typst: bool) -> Result<String, String> {
    let set = set.parse::<SetChoice>()?;
    ENV.with_borrow_mut(|env| set.eval(input, typst, env))
}

/// Check if `input` is a definition, like `f(x) := x^2`.
#[wasm_bindgen]
#[must_use]
pub fn is_definition(input: &str) -> bool {
    Parser::new(input).is_definition()
}

/// List the definitions, one per line.
#[wasm_bindgen]
#[must_use]
pub fn definitions() -> String {
    ENV.with_borrow(|env| {
        env.definitions()
            .map(ToString::to_string)
            .collect::<Vec<_>>()
            .join("\n")
    })
}

/// Remove the definition of `name`, or every definition if `name` is empty.
///
/// # Errors
/// Returns an error message if `name` is not defined.
#[wasm_bindgen]
pub fn clear_definitions(name: &str) -> Result<(), String> {
    ENV.with_borrow_mut(|env| {
        if name.is_empty() {
            env.clear();
            Ok(())
        } else if env.remove(name) {
            Ok(())
        } else {
            Err(format!("`{name}` is not defined"))
        }
    })
}

/// List the available sets with their description.
#[wasm_bindgen]
#[must_use]
pub fn sets_help() -> String {
    repl::sets_help()
}

/// Canonical name of the set named `name`, like `Z/7` for `z/7z`.
///
/// # Errors
/// Returns an error message if the set is unknown.
#[wasm_bindgen]
pub fn set_name(name: &str) -> Result<String, String> {
    name.parse::<SetChoice>().map(SetChoice::name)
}
