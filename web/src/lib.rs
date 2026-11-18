//! Bindings exposing the Formalith command line interface to the browser.

use formalith::repl::{self, SetChoice};
use wasm_bindgen::prelude::*;

/// Log panic messages to the browser console.
#[wasm_bindgen(start)]
pub fn start() {
    console_error_panic_hook::set_once();
}

/// Parse and evaluate `input` in the set named `set`, printed as Typst math source if `typst` is set.
///
/// # Errors
/// Returns an error message if the set is unknown or `input` is not a valid expression.
///
/// Operations unsupported by the set panic, which aborts the wasm instance: the caller has to reload it.
#[wasm_bindgen(js_name = evaluate)]
pub fn eval(input: &str, set: &str, typst: bool) -> Result<String, String> {
    set.parse::<SetChoice>()?.eval(input, typst)
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
