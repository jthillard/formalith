//! Formalith graphical interface, natively and in the browser, like a graphing calculator: a list of lines with
//! their results, next to a plot of their graphs (curves, implicit curves, regions and points), with sliders for
//! their parameters and the remarkable points of the selected curve.
//!
//! Lines are evaluated off the interface thread ([`evaluator`]) and come back with their graphs compiled to
//! numerical expressions ([`formalith_session::graph`]), drawn without the CAS ([`plot`]): they are compiled to WGSL
//! ([`shader`]) and drawn per pixel on the GPU ([`gpu`]), which also searches remarkable points when it has compute
//! shaders.

pub mod app;
pub mod evaluator;
pub mod geometry;
pub mod gpu;
pub mod plot;
pub mod protocol;
pub mod shader;

pub use app::App;

#[cfg(target_arch = "wasm32")]
mod web {
    use std::cell::RefCell;

    use wasm_bindgen::{JsCast, prelude::*};

    use crate::{
        App,
        evaluator::{Backend, WebBackend},
        protocol::{Request, Worker},
    };

    thread_local! {
        /// The state of the worker, when this instance runs in a Web Worker.
        static WORKER: RefCell<Worker> = RefCell::new(Worker::new());
    }

    /// Start the application in the canvas with the identifier `canvas_id`.
    ///
    /// # Errors
    /// Returns an error if the canvas doesn't exist or the graphics can't be initialized.
    #[wasm_bindgen]
    pub async fn start(canvas_id: String) -> Result<(), JsValue> {
        console_error_panic_hook::set_once();
        let canvas = web_sys::window()
            .and_then(|window| window.document())
            .and_then(|document| document.get_element_by_id(&canvas_id))
            .ok_or_else(|| JsValue::from_str(&format!("no element `{canvas_id}`")))?
            .dyn_into::<web_sys::HtmlCanvasElement>()?;
        eframe::WebRunner::new()
            .start(
                canvas,
                eframe::WebOptions::default(),
                Box::new(|cc| {
                    let ctx = cc.egui_ctx.clone();
                    let backends = Box::new(move || {
                        let ctx = ctx.clone();
                        Box::new(WebBackend::new(move || ctx.request_repaint())) as Box<dyn Backend>
                    });
                    Ok(Box::new(App::new(cc, backends)))
                }),
            )
            .await
    }

    /// Evaluate a JSON [`Request`] in a Web Worker, calling `reply` with each JSON [`crate::protocol::Reply`].
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
