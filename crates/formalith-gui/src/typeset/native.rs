//! Typesetting natively, with the typst crates.

use std::sync::LazyLock;

use typst::{
    Library, LibraryExt, World,
    diag::{FileError, FileResult},
    foundations::{Bytes, Datetime, Duration},
    syntax::{FileId, Source},
    text::{Font, FontBook},
    utils::LazyHash,
};
use typst_layout::PagedDocument;

use super::SIZE;

/// The only font, New Computer Modern Math (Typst's default math font), also used for text in math: Typst's other
/// bundled fonts would make the worker several megabytes larger.
const MATH_FONT: &[u8] = include_bytes!("../../fonts/NewCMMath-Regular.otf");

/// The standard library and the font, loaded once.
struct Resources {
    library: LazyHash<Library>,
    book: LazyHash<FontBook>,
    fonts: Vec<Font>,
}

static RESOURCES: LazyLock<Resources> = LazyLock::new(|| {
    let fonts: Vec<Font> = Font::iter(Bytes::new(MATH_FONT)).collect();
    Resources {
        library: LazyHash::new(Library::default()),
        book: LazyHash::new(FontBook::from_fonts(&fonts)),
        fonts,
    }
});

/// A world with a single source file, and no other file.
struct MathWorld {
    source: Source,
}

impl World for MathWorld {
    fn library(&self) -> &LazyHash<Library> {
        &RESOURCES.library
    }

    fn book(&self) -> &LazyHash<FontBook> {
        &RESOURCES.book
    }

    fn main(&self) -> FileId {
        self.source.id()
    }

    fn source(&self, id: FileId) -> FileResult<Source> {
        if id == self.source.id() {
            Ok(self.source.clone())
        } else {
            Err(FileError::AccessDenied)
        }
    }

    fn file(&self, id: FileId) -> FileResult<Bytes> {
        if id == self.source.id() {
            Ok(Bytes::from_string(self.source.text().to_owned()))
        } else {
            Err(FileError::AccessDenied)
        }
    }

    fn font(&self, index: usize) -> Option<Font> {
        RESOURCES.fonts.get(index).cloned()
    }

    fn today(&self, _offset: Option<Duration>) -> Option<Datetime> {
        None
    }
}

/// Typeset `math`, Typst math markup, as an SVG image, or `None` if it doesn't compile.
pub(super) fn render(math: &str) -> Option<String> {
    let world = MathWorld {
        source: Source::detached(format!(
            "#set page(width: auto, height: auto, margin: (x: 0pt, y: 0.3em), fill: none)\n\
             #show math.equation: set align(left)\n\
             #set text(font: \"New Computer Modern Math\", size: {SIZE}pt, fill: white)\n\
             $ {math} $"
        )),
    };
    let document: PagedDocument = typst::compile(&world).output.ok()?;
    let page = document.pages().first()?;
    Some(typst_svg::svg(page, &typst_svg::SvgOptions::default()))
}
