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

/// Names of the available sets.
#[wasm_bindgen]
#[must_use]
pub fn set_names() -> Vec<String> {
    SetChoice::ALL.iter().map(|set| set.name().to_owned()).collect()
}
