//! Typesetting of results with Typst, in the interface: the worker sends each result printed as Typst math
//! ([`crate::protocol::LineResult::typst`]), compiled here to an SVG image, white on a transparent background, which
//! egui_extras' loader rasterizes and the interface tints with the color of its theme.
//!
//! Natively, the typst crates compile it ([`native`]). In the browser, they would make the wasm module about 20 MB
//! larger, so the page loads typst.ts from a CDN and defines `formalithTypeset` (`www/index.html`), called
//! asynchronously ([`web`]); without it, results stay text.

use std::{
    cell::RefCell,
    collections::{HashMap, HashSet},
    hash::{DefaultHasher, Hash, Hasher},
    rc::Rc,
    sync::Arc,
};

use eframe::egui::{self, load::Bytes};

#[cfg(not(target_arch = "wasm32"))]
mod native;

/// The size of the text, in points. The SVG is in points, rasterized at 4/3 pixels per point, so the math is a bit
/// larger than the 14 px monospace text, like in the web REPL. The page uses the same size.
#[cfg(not(target_arch = "wasm32"))]
const SIZE: f64 = 13.;

/// A typeset image.
#[derive(Clone)]
pub struct Image {
    /// Its URI for the image loader.
    pub uri: String,
    /// The SVG.
    pub bytes: Bytes,
    /// Its size, in points of egui (pixels of the SVG), as the loader rasterizes it at a scale of 1.
    pub size: egui::Vec2,
}

impl Image {
    /// Check if the image fits in a single texture of `ctx` at its scale, which its loader needs.
    pub fn fits(&self, ctx: &egui::Context) -> bool {
        // A little margin for the rounding of the rasterizer
        #[allow(clippy::cast_precision_loss)] // Texture sides are small
        let side = ctx.input(|input| input.max_texture_side) as f32 - 2.;
        self.size.max_elem() * ctx.pixels_per_point() <= side
    }
}

/// The state of a typeset source.
enum Typeset {
    /// Being typeset, in the browser.
    #[cfg(target_arch = "wasm32")]
    Pending,
    /// The image, with its URI for the image loader.
    Ready(Image),
    /// The source doesn't compile, or Typst isn't available.
    Failed,
}

impl Typeset {
    /// The state of `source`, typeset as `svg` if it compiled.
    fn new(source: &str, svg: Option<String>) -> Self {
        let Some((svg, size)) = svg.and_then(|svg| svg_size(&svg).map(|size| (svg, size))) else {
            return Self::Failed;
        };
        let mut hasher = DefaultHasher::new();
        source.hash(&mut hasher);
        Self::Ready(Image {
            uri: format!("bytes://typst/{:016x}.svg", hasher.finish()),
            bytes: Bytes::Shared(Arc::from(svg.into_bytes())),
            size,
        })
    }
}

/// The size of `svg` in pixels, from the `width` and `height` of its root element (`12pt`, `16px` or `16`), or its
/// `viewBox`.
fn svg_size(svg: &str) -> Option<egui::Vec2> {
    let start = svg.find("<svg")?;
    let tag = &svg[start..start + svg[start..].find('>')?];
    let attribute = |name: &str| {
        let value = tag.split(&format!(" {name}=\"")).nth(1)?;
        Some(&value[..value.find('"')?])
    };
    let length = |name: &str| {
        let value = attribute(name)?.trim();
        let (number, scale) = if let Some(number) = value.strip_suffix("pt") {
            (number, 4. / 3.)
        } else {
            (value.strip_suffix("px").unwrap_or(value), 1.)
        };
        number.trim().parse::<f32>().ok().map(|x| x * scale)
    };
    let size = if let (Some(width), Some(height)) = (length("width"), length("height")) {
        egui::vec2(width, height)
    } else {
        let numbers: Vec<f32> = attribute("viewBox")?
            .split([' ', ','])
            .filter(|x| !x.is_empty())
            .map(str::parse)
            .collect::<Result<_, _>>()
            .ok()?;
        let [_, _, width, height] = numbers[..] else {
            return None;
        };
        egui::vec2(width, height)
    };
    (size.is_finite() && size.min_elem() > 0.).then_some(size)
}

/// The typeset sources, kept while a line shows them.
#[derive(Default)]
pub struct Typesetter {
    /// Shared with the typesetting tasks in the browser.
    cache: Rc<RefCell<HashMap<String, Typeset>>>,
}

impl Typesetter {
    /// The image of `source`, Typst math markup, starting to typeset it if needed. `None` while it is typeset, or if
    /// it can't be.
    pub fn get(&self, ctx: &egui::Context, source: &str) -> Option<Image> {
        let mut cache = self.cache.borrow_mut();
        if !cache.contains_key(source) {
            #[cfg(not(target_arch = "wasm32"))]
            {
                let _ = ctx;
                profile_scope!("typst");
                // A panic of the compiler mustn't stop the interface
                let svg = std::panic::catch_unwind(|| native::render(source))
                    .ok()
                    .flatten();
                cache.insert(source.to_owned(), Typeset::new(source, svg));
            }
            #[cfg(target_arch = "wasm32")]
            {
                cache.insert(source.to_owned(), Typeset::Pending);
                web::start(source, Rc::clone(&self.cache), ctx.clone());
            }
        }
        match cache.get(source)? {
            Typeset::Ready(image) => Some(image.clone()),
            _ => None,
        }
    }

    /// Forget the sources not in `sources`, and their images.
    pub fn retain<'a>(&self, ctx: &egui::Context, sources: impl IntoIterator<Item = &'a str>) {
        let sources: HashSet<&str> = sources.into_iter().collect();
        self.cache.borrow_mut().retain(|source, typeset| {
            let keep = sources.contains(source.as_str());
            if !keep && let Typeset::Ready(image) = typeset {
                ctx.forget_image(&image.uri);
            }
            keep
        });
    }
}

#[cfg(target_arch = "wasm32")]
mod web {
    use std::{cell::RefCell, collections::HashMap, rc::Rc};

    use eframe::egui;
    use wasm_bindgen::prelude::*;
    use wasm_bindgen_futures::JsFuture;

    use super::Typeset;

    #[wasm_bindgen]
    extern "C" {
        /// Typeset Typst math markup as an SVG image, white on a transparent background, with typst.ts. Defined by
        /// `www/index.html`; throws if it isn't.
        #[wasm_bindgen(js_name = formalithTypeset, catch)]
        fn typeset(source: &str) -> Result<js_sys::Promise, JsValue>;
    }

    /// Typeset `source` in the background, then store it in `cache` unless it was forgotten meanwhile.
    pub(super) fn start(
        source: &str,
        cache: Rc<RefCell<HashMap<String, Typeset>>>,
        ctx: egui::Context,
    ) {
        let promise = typeset(source);
        let source = source.to_owned();
        wasm_bindgen_futures::spawn_local(async move {
            let svg = match promise {
                Ok(promise) => JsFuture::from(promise)
                    .await
                    .ok()
                    .and_then(|svg| svg.as_string()),
                Err(_) => None,
            };
            if let Some(typeset) = cache.borrow_mut().get_mut(&source) {
                *typeset = Typeset::new(&source, svg);
            }
            ctx.request_repaint();
        });
    }
}

#[cfg(all(test, not(target_arch = "wasm32")))]
mod tests {
    use super::*;

    #[test]
    fn test_typeset() {
        let ctx = egui::Context::default();
        let typesetter = Typesetter::default();
        let image = typesetter.get(&ctx, "x^2 + 1").unwrap();
        assert!(image.uri.starts_with("bytes://typst/"));
        assert!(image.size.x > 10. && image.size.x < 100. && image.size.y > 5.);
        assert!(image.fits(&ctx));
        let svg = std::str::from_utf8(&image.bytes).unwrap();
        assert!(svg.starts_with("<svg"));
        // Transparent, and only white glyphs to tint
        assert!(!svg.contains("#000000"));
        // Text in math, with the math font
        assert!(
            typesetter
                .get(&ctx, "\"no solution\" quad k in ZZ")
                .is_some()
        );
        assert!(typesetter.get(&ctx, "x + undefinedname").is_none());

        // Too wide for a texture, shown as text
        let long = (0..2000)
            .map(|i| format!("x_{i}"))
            .collect::<Vec<_>>()
            .join(" + ");
        let image = typesetter.get(&ctx, &long).unwrap();
        assert!(image.size.x > 8192.);
        assert!(!image.fits(&ctx));

        typesetter.retain(&ctx, ["x^2 + 1"]);
        assert_eq!(typesetter.cache.borrow().len(), 1);
    }

    #[test]
    fn test_svg_size() {
        assert_eq!(
            svg_size(r#"<svg class="a" width="12pt" height="3pt" viewBox="0 0 12 3">"#),
            Some(egui::vec2(16., 4.))
        );
        assert_eq!(
            svg_size(r#"<svg width="20px" height="5">"#),
            Some(egui::vec2(20., 5.))
        );
        assert_eq!(
            svg_size(r#"<?xml?><svg viewBox="0 0 20 5" xmlns="x"><g/></svg>"#),
            Some(egui::vec2(20., 5.))
        );
        assert_eq!(svg_size(r#"<svg width="100%" height="1">"#), None);
        assert_eq!(svg_size("<svg>"), None);
        assert_eq!(svg_size("text"), None);
    }
}
