//! Formalith graphical interface, natively and in the browser, like a graphing calculator: a list of lines with
//! their results, next to a plot of their graphs (curves, implicit curves, regions and points), with sliders for
//! their parameters and the remarkable points of the selected curve.
//!
//! Lines are evaluated off the interface thread ([`evaluator`]) and come back with their graphs compiled to
//! numerical expressions ([`formalith_session::graph`]), drawn without the CAS ([`plot`]): they are compiled to WGSL
//! ([`shader`]) and drawn per pixel on the GPU ([`gpu`]), which also searches remarkable points when it has compute
//! shaders. In the browser, the worker is a separate wasm module (`formalith-gui-worker`), so this one doesn't
//! hold the CAS.
//!
//! With the feature `profile`, a profiler window ([`profiler`]) records all of it, down to the CAS and the GPU.

/// A profiling scope named `$name`, optionally with dynamic `$data`, lasting until the end of the enclosing block.
/// Nothing without the feature `profile`.
macro_rules! profile_scope {
    ($name:expr $(, $data:expr)?) => {
        #[cfg(feature = "profile")]
        profiling::scope!($name $(, $data)?);
    };
}

#[cfg(feature = "ui")]
pub mod app;
#[cfg(feature = "ui")]
pub mod evaluator;
#[cfg(feature = "ui")]
pub mod geometry;
#[cfg(feature = "ui")]
pub mod gpu;
#[cfg(feature = "ui")]
pub mod plot;
#[cfg(feature = "profile")]
pub mod profiler;
pub mod protocol;
#[cfg(feature = "ui")]
pub mod shader;

#[cfg(feature = "ui")]
pub use app::App;

#[cfg(all(target_arch = "wasm32", feature = "ui"))]
mod web {
    use wasm_bindgen::{JsCast, prelude::*};

    use crate::{
        App,
        evaluator::{Backend, WebBackend},
    };

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
        #[allow(unused_mut)]
        let mut options = eframe::WebOptions::default();
        #[cfg(feature = "profile")]
        crate::profiler::request_timestamps(&mut options.wgpu_options);
        eframe::WebRunner::new()
            .start(
                canvas,
                options,
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
}
