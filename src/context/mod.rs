//! Contexts and symbols implementation.
//! Context are used to store a hashmap linking a variable name to its unique identifier. A same variable can have multiple names.

use std::{
    collections::HashMap,
    sync::{LazyLock, RwLock},
};

use append_only_vec::AppendOnlyVec;

use crate::printer::{PrettyPrint, PrettyPrinter, Print};

/// Store all symbols' data created
static SYMBOLS: AppendOnlyVec<SymbolData> = AppendOnlyVec::new();

/// Store the global context containing symbols' data
static GLOBAL_CONTEXT: LazyLock<RwLock<Context>> = LazyLock::new(|| RwLock::new(Context::new()));
/// A symbol, representing a named variable.
///
/// See [`crate::symbol`!] to create a new symbol.
#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct Symbol(usize);

impl Symbol {
    /// Create a symbol by name in the global context.
    ///
    /// If the symbol already exists, its identifier is returned, otherwise a new symbol is added in the global context.
    /// ```
    /// use formalith::context::Symbol;
    ///
    /// let x = Symbol::new("x");
    /// let x2 = Symbol::new("x");
    /// let y = Symbol::new("y");
    /// let another_symbol = Symbol::new("aReallyLongSymbol");
    ///
    /// assert_eq!(x, x2);
    /// assert_ne!(x, y);
    /// ```
    ///
    /// # Panics
    /// This function will panic if the lock on the global context is poisoned.
    #[must_use]
    pub fn new<T: Into<String>>(name: T) -> Self {
        Context::get_global_context()
            .write()
            .unwrap()
            .get_symbol(name.into())
    }
}

impl Print for Symbol {
    fn print(
        &self,
        _options: &crate::printer::PrintOptions,
        f: &mut std::fmt::Formatter<'_>,
    ) -> std::fmt::Result {
        f.write_str(&Context::get_symbol_data(self).name)
    }
}
impl PrettyPrint for Symbol {
    fn pretty_print(
        &self,
        _options: &crate::printer::PrintOptions,
    ) -> crate::printer::PrettyPrinter {
        PrettyPrinter::from(Context::get_symbol_data(self).name.clone())
    }
}

/// Create a symbol by name in the global context.
/// If the symbol already exists, its identifier is returned, otherwise a new symbol is added in the global context.
/// See [Symbol]
/// ```
/// use formalith::symbol;
///
/// let x = symbol!("x");
/// let x2 = symbol!("x");
/// let y = symbol!("y");
/// let another_symbol = symbol!("aReallyLongSymbol");
///
/// assert_eq!(x, x2);
/// assert_ne!(x, y);
/// ```
#[macro_export(local_inner_macros)]
macro_rules! symbol {
    ( $x:expr ) => {
        $crate::context::Symbol::new($x)
    };
    ( $x:expr, $f:expr) => {
        $crate::term::Term::Symbol($crate::term::SymbolTerm::new(
            $crate::context::Symbol::new($x),
            $f,
        ))
    };
}

/// Stores data associated with a symbol.
#[derive(Clone, Debug)]
pub struct SymbolData {
    /// The symbol visual representation
    pub name: String,
}

/// A context storing variables names in this specific context.
pub struct Context {
    symbols: HashMap<String, Symbol>,
}

impl Context {
    /// Absolute function
    pub const ABS: Symbol = Symbol(0);
    /// Determinant function
    pub const DET: Symbol = Symbol(1);
    /// Expansion function, evaluating to its expanded argument
    pub const EXPAND: Symbol = Symbol(2);
    /// Factorization function, evaluating to its factored argument
    pub const FACTOR: Symbol = Symbol(3);
    /// Simplification function, evaluating to its simplified argument
    pub const SIMPLIFY: Symbol = Symbol(4);
    /// Real part function
    pub const RE: Symbol = Symbol(5);
    /// Imaginary part function
    pub const IM: Symbol = Symbol(6);
    /// Complex conjugate function
    pub const CONJ: Symbol = Symbol(7);

    const BUILTIN_NAMES: [&'static str; 8] = [
        "abs", "det", "expand", "factor", "simplify", "re", "im", "conj",
    ];

    /// Create a new empty context
    #[must_use]
    pub fn new() -> Self {
        let mut ctx = Self {
            symbols: HashMap::new(),
        };
        for name in Self::BUILTIN_NAMES {
            ctx.get_symbol(name.to_string());
        }
        ctx
    }

    /// Returns a reference to the global static context, used by default
    pub(crate) fn get_global_context() -> &'static RwLock<Self> {
        &GLOBAL_CONTEXT
    }

    /// Return a [Symbol] from its name in a context, creating it if needed.
    pub fn get_symbol(&mut self, name: String) -> Symbol {
        *self
            .symbols
            .entry(name)
            .or_insert_with_key(|name| Symbol(SYMBOLS.push(SymbolData { name: name.clone() })))
    }
    /// Return a reference to the [`SymbolData`] of a given [Symbol]
    #[must_use]
    pub fn get_symbol_data(symbol: &Symbol) -> &'static SymbolData {
        &SYMBOLS[symbol.0]
    }
}

impl Default for Context {
    fn default() -> Self {
        Self::new()
    }
}
