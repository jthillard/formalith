//! Helpers shared by integration tests.
#![allow(dead_code)]

use formalith::printer::{PrettyPrint, PrintOptions};

/// Print on a single line, without colors.
pub fn line<T: PrettyPrint>(value: &T) -> String {
    format!(
        "{}",
        value.with_options(PrintOptions {
            colors: false,
            typst: false,
            pretty_print: false,
        })
    )
}

/// Pretty print (2D layout), without colors.
pub fn pretty<T: PrettyPrint>(value: &T) -> String {
    format!(
        "{}",
        value.with_options(PrintOptions {
            colors: false,
            typst: false,
            pretty_print: true,
        })
    )
}
