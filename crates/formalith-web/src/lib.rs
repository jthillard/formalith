//! Bindings exposing a Formalith session to the browser.

use std::cell::RefCell;

use formalith_session::{Output, Session};
use wasm_bindgen::prelude::*;

thread_local! {
    /// The session of the page. Lost when the wasm instance aborts on a panic.
    static SESSION: RefCell<Session> = RefCell::new(Session::new());
}

/// Log panic messages to the browser console.
#[wasm_bindgen(start)]
pub fn start() {
    console_error_panic_hook::set_once();
}

/// The answer of the session to a line.
#[wasm_bindgen]
pub struct Answer {
    kind: &'static str,
    text: String,
    replay: bool,
    set: String,
}

#[wasm_bindgen]
impl Answer {
    /// `none`, `result`, `typst` (a result as Typst math source), `message` or `error`.
    #[wasm_bindgen(getter)]
    #[must_use]
    pub fn kind(&self) -> String {
        self.kind.to_owned()
    }

    /// The text to show.
    #[wasm_bindgen(getter)]
    #[must_use]
    pub fn text(&self) -> String {
        self.text.clone()
    }

    /// Whether the line changed the state of the session, so it is run again in a new worker after a panic.
    #[wasm_bindgen(getter)]
    #[must_use]
    pub fn replay(&self) -> bool {
        self.replay
    }

    /// The name of the current set, after the line.
    #[wasm_bindgen(getter)]
    #[must_use]
    pub fn set(&self) -> String {
        self.set.clone()
    }
}

/// Run a line in the session: a command like `:set Z/7`, or an input evaluated in the current set.
///
/// Operations unsupported by the set panic, which aborts the wasm instance: the caller has to reload it.
#[wasm_bindgen]
#[must_use]
pub fn run(line: &str) -> Answer {
    SESSION.with_borrow_mut(|session| {
        let response = session.run(line);
        let kind = match &response.output {
            Output::None => "none",
            Output::Result { typst: true, .. } => "typst",
            Output::Result { .. } => "result",
            Output::Message(_) => "message",
            Output::Error(_) => "error",
        };
        Answer {
            kind,
            text: response.output.to_string(),
            replay: response.replay,
            set: session.set().name(),
        }
    })
}

/// Print results as Typst math source if `typst` is set.
#[wasm_bindgen]
pub fn set_typst(typst: bool) {
    SESSION.with_borrow_mut(|session| session.set_typst(typst));
}

/// The help of the session: inputs, commands and sets.
#[wasm_bindgen]
#[must_use]
pub fn help() -> String {
    Session::help()
}
