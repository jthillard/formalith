//! Symbol expression.

use std::fmt::{Debug, Display};

use crate::{
    context::{Context, Symbol},
    printer::{PrettyPrint, PrettyPrinter, Print, PrintOptions},
};

use super::{Flags, NORMALIZED};

/// A symbol inside a mathematical expression.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct SymbolTerm<T> {
    flags: u8,
    pub(crate) symbol: Symbol,
    pub(crate) set: T,
}

impl<T> Flags for SymbolTerm<T> {
    fn get_flags(&self) -> u8 {
        self.flags
    }
    fn get_flags_mut(&mut self) -> &mut u8 {
        &mut self.flags
    }
}

impl<T> SymbolTerm<T> {
    /// Create a new symbol expression
    pub const fn new(symbol: Symbol, set: T) -> Self {
        Self {
            flags: NORMALIZED,
            symbol,
            set,
        }
    }
    /// The symbol.
    pub const fn symbol(&self) -> Symbol {
        self.symbol
    }
}
impl<T: Debug> Print for SymbolTerm<T> {
    fn print(&self, options: &PrintOptions, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if options.typst && self.symbol == Context::UNDEFINED {
            // A multi-letter identifier isn't a valid Typst variable
            return f.write_str("\"undefined\"");
        }
        if options.typst && self.symbol == Context::EULER_GAMMA {
            return f.write_str("gamma");
        }
        if options.typst {
            return f.write_str(&crate::printer::typst_name(self.symbol.name()));
        }
        write!(f, "{}", self.symbol.name())
    }
}
impl<T: Debug> PrettyPrint for SymbolTerm<T> {
    fn pretty_print(&self, _options: &PrintOptions) -> crate::printer::PrettyPrinter {
        PrettyPrinter::from(match self.symbol {
            Context::PI => "π".to_string(),
            Context::OO => "∞".to_string(),
            Context::EULER_GAMMA => "γ".to_string(),
            _ => crate::printer::pretty_name(self.symbol.name()).into_owned(),
        })
    }
}
impl<T: Debug> Display for SymbolTerm<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        PrettyPrint::fmt(self, &PrintOptions::default(), f)
    }
}
