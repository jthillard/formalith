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

    /// Square root function, evaluating to `{$x^(1/2)$}`
    pub const SQRT: Symbol = Symbol(8);
    /// Nth root function, `root(x, n)` evaluating to `{$x^(1/n)$}`
    pub const ROOT: Symbol = Symbol(9);
    /// Sign function
    pub const SIGN: Symbol = Symbol(10);
    /// Floor function
    pub const FLOOR: Symbol = Symbol(11);
    /// Ceiling function
    pub const CEIL: Symbol = Symbol(12);
    /// Minimum of its arguments
    pub const MIN: Symbol = Symbol(13);
    /// Maximum of its arguments
    pub const MAX: Symbol = Symbol(14);
    /// Greatest common divisor of two numbers or polynomials
    pub const GCD: Symbol = Symbol(15);
    /// Least common multiple of two numbers or polynomials
    pub const LCM: Symbol = Symbol(16);
    /// Quotient of the euclidean division of two numbers or polynomials
    pub const QUO: Symbol = Symbol(17);
    /// Remainder of the euclidean division of two numbers or polynomials
    pub const REM: Symbol = Symbol(18);
    /// Derivative of the first argument with respect to the second, a symbol
    pub const DIFF: Symbol = Symbol(19);
    /// Solve a system of equations, only allowed as a whole statement
    pub const SOLVE: Symbol = Symbol(20);
    /// Numerical approximation, `approx(x, n)` evaluating `x` to `n` significant digits (15 by default)
    pub const APPROX: Symbol = Symbol(21);
    /// Exponential function
    pub const EXP: Symbol = Symbol(22);
    /// Natural logarithm
    pub const LN: Symbol = Symbol(23);
    /// Sine function
    pub const SIN: Symbol = Symbol(24);
    /// Cosine function
    pub const COS: Symbol = Symbol(25);
    /// Tangent function
    pub const TAN: Symbol = Symbol(26);
    /// The constant `{$pi$}`
    pub const PI: Symbol = Symbol(27);
    /// Euler's number `{$e$}`
    pub const E: Symbol = Symbol(28);
    /// Limit `lim(f, x, a)`, or `lim(f, x, a, 1)` and `lim(f, x, a, -1)` for right and left limits
    pub const LIM: Symbol = Symbol(29);
    /// Infinity `{$oo$}`, a limit point or the result of a limit
    pub const OO: Symbol = Symbol(30);

    const BUILTIN_NAMES: [&'static str; 31] = [
        "abs", "det", "expand", "factor", "simplify", "re", "im", "conj", "sqrt", "root", "sign",
        "floor", "ceil", "min", "max", "gcd", "lcm", "quo", "rem", "diff", "solve", "approx",
        "exp", "ln", "sin", "cos", "tan", "pi", "e", "lim", "oo",
    ];

    /// Return `true` if `symbol` is a builtin constant, like `{$pi$}`, which is not a function.
    #[must_use]
    pub const fn is_builtin_constant(symbol: Symbol) -> bool {
        matches!(symbol, Self::PI | Self::E | Self::OO)
    }

    /// Return the minimum and maximum number of arguments of a builtin function, or `None` if `symbol` isn't a builtin.
    #[must_use]
    pub const fn builtin_arity(symbol: Symbol) -> Option<(usize, usize)> {
        match symbol {
            Self::ROOT | Self::GCD | Self::LCM | Self::QUO | Self::REM | Self::DIFF => Some((2, 2)),
            Self::MIN | Self::MAX | Self::SOLVE => Some((1, usize::MAX)),
            Self::APPROX => Some((1, 2)),
            Self::LIM => Some((3, 4)),
            Self::PI | Self::E | Self::OO => Some((0, 0)),
            Symbol(id) if id < Self::BUILTIN_NAMES.len() => Some((1, 1)),
            _ => None,
        }
    }

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
