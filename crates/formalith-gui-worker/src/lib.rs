//! The Web Worker of the Formalith graphical interface in the browser ([`formalith_gui`]), evaluating the lines.
//!
//! It is a separate wasm module so that the interface doesn't hold the CAS, nor the worker the interface.

#[cfg(target_arch = "wasm32")]
mod web {
    use std::cell::RefCell;

    use formalith_gui::protocol::{Request, Worker};
    use wasm_bindgen::prelude::*;

    thread_local! {
        /// The state of the worker.
        static WORKER: RefCell<Worker> = RefCell::new(Worker::new());
    }

    /// Evaluate a JSON [`Request`] in a Web Worker, calling `reply` with each JSON
    /// [`formalith_gui::protocol::Reply`].
    ///
    /// A panic aborts the instance: the interface replaces the worker.
    #[wasm_bindgen]
    pub fn worker_evaluate(request: &str, reply: &js_sys::Function) {
        console_error_panic_hook::set_once();
        let Ok(request) = serde_json::from_str::<Request>(request) else {
            return;
        };
        WORKER.with_borrow_mut(|worker| {
            worker.evaluate(&request, |answer| {
                let json = serde_json::to_string(&answer).expect("Replies are serializable");
                reply
                    .call1(&JsValue::NULL, &JsValue::from_str(&json))
                    .is_ok()
            });
        });
    }
}
