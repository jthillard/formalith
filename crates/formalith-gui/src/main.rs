//! The native Formalith graphical interface. In the browser, the library is started by `www/index.html`.

#[cfg(target_arch = "wasm32")]
fn main() {}

#[cfg(not(target_arch = "wasm32"))]
fn main() -> eframe::Result {
    use eframe::egui;
    use formalith_gui::{
        App,
        evaluator::{Backend, NativeBackend},
    };

    let options = eframe::NativeOptions {
        renderer: eframe::Renderer::Wgpu,
        viewport: egui::ViewportBuilder::default()
            .with_title("Formalith")
            .with_inner_size([1280., 800.])
            .with_min_inner_size([400., 300.]),
        ..Default::default()
    };
    eframe::run_native(
        "Formalith",
        options,
        Box::new(|cc| {
            let ctx = cc.egui_ctx.clone();
            let backends = Box::new(move || {
                let ctx = ctx.clone();
                Box::new(NativeBackend::new(move || ctx.request_repaint())) as Box<dyn Backend>
            });
            Ok(Box::new(App::new(cc, backends)))
        }),
    )
}
