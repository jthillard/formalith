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
}
impl<T: Debug> Print for SymbolTerm<T> {
    fn print(&self, options: &PrintOptions, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if options.typst && self.symbol == Context::UNDEFINED {
            // A multi-letter identifier isn't a valid Typst variable
            return f.write_str("\"undefined\"");
        }
        write!(f, "{}", Context::get_symbol_data(&self.symbol).name)
    }
}
impl<T: Debug> PrettyPrint for SymbolTerm<T> {
    fn pretty_print(&self, _options: &PrintOptions) -> crate::printer::PrettyPrinter {
        PrettyPrinter::from(match self.symbol {
            Context::PI => "π".to_string(),
            Context::OO => "∞".to_string(),
            _ => Context::get_symbol_data(&self.symbol).name.clone(),
        })
    }
}
impl<T: Debug> Display for SymbolTerm<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        PrettyPrint::fmt(self, &PrintOptions::default(), f)
    }
}
