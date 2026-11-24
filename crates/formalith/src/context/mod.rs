//! Contexts and symbols implementation.
//! Context are used to store a hashmap linking a variable name to its unique identifier. A same variable can have multiple names.

use std::{
    collections::HashMap,
    sync::{LazyLock, RwLock},
};

use append_only_vec::AppendOnlyVec;

use crate::printer::{PrettyPrint, PrettyPrinter, Print};

pub mod assumptions;
pub mod docs;

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

    /// The name of the symbol.
    #[must_use]
    pub fn name(self) -> &'static str {
        &Context::get_symbol_data(&self).name
    }
}

impl Print for Symbol {
    fn print(
        &self,
        _options: &crate::printer::PrintOptions,
        f: &mut std::fmt::Formatter<'_>,
    ) -> std::fmt::Result {
        f.write_str(self.name())
    }
}
impl PrettyPrint for Symbol {
    fn pretty_print(
        &self,
        _options: &crate::printer::PrintOptions,
    ) -> crate::printer::PrettyPrinter {
        PrettyPrinter::from(crate::printer::pretty_name(self.name()).into_owned())
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
    /// The result of a limit that doesn't exist, like `lim(1/x, x, 0)`
    pub const UNDEFINED: Symbol = Symbol(31);
    /// Series expansion `series(f, x, a, n)` up to `{$O((x - a)^n)$}`, `series(f, x, a, n, 1)` and
    /// `series(f, x, a, n, -1)` for right and left expansions
    pub const SERIES: Symbol = Symbol(32);
    /// Arcsine function
    pub const ASIN: Symbol = Symbol(33);
    /// Arccosine function
    pub const ACOS: Symbol = Symbol(34);
    /// Arctangent function
    pub const ATAN: Symbol = Symbol(35);
    /// Hyperbolic sine function
    pub const SINH: Symbol = Symbol(36);
    /// Hyperbolic cosine function
    pub const COSH: Symbol = Symbol(37);
    /// Hyperbolic tangent function
    pub const TANH: Symbol = Symbol(38);
    /// Inverse hyperbolic sine function
    pub const ASINH: Symbol = Symbol(39);
    /// Inverse hyperbolic cosine function
    pub const ACOSH: Symbol = Symbol(40);
    /// Inverse hyperbolic tangent function
    pub const ATANH: Symbol = Symbol(41);
    /// Cotangent function, rewritten as `{$cos / sin$}`
    pub const COT: Symbol = Symbol(42);
    /// Secant function, rewritten as `{$1 / cos$}`
    pub const SEC: Symbol = Symbol(43);
    /// Cosecant function, rewritten as `{$1 / sin$}`
    pub const CSC: Symbol = Symbol(44);
    /// Logarithm `log(x, b)` in base `b` (10 by default), rewritten as `{$ln(x) / ln(b)$}`
    pub const LOG: Symbol = Symbol(45);
    /// Factorial `{$n!$}` of a natural number
    pub const FACTORIAL: Symbol = Symbol(46);
    /// Binomial coefficient `binomial(n, k)`
    pub const BINOMIAL: Symbol = Symbol(47);
    /// Integral `integrate(f, x)` (an antiderivative) or `integrate(f, x, a, b)` (from `a` to `b`)
    pub const INTEGRATE: Symbol = Symbol(48);
    /// Error function `{$"erf"(x) = 2/sqrt(pi) integral_0^x e^(-t^2) d t$}`
    pub const ERF: Symbol = Symbol(49);
    /// Imaginary error function `{$"erfi"(x) = 2/sqrt(pi) integral_0^x e^(t^2) d t$}`
    pub const ERFI: Symbol = Symbol(50);
    /// Declare assumptions on symbols, like `assume(a > 0, n integer)`, only allowed as a whole statement
    pub const ASSUME: Symbol = Symbol(51);
    /// Gamma function `{$Gamma(x) = integral_0^oo t^(x - 1) e^(-t) d t$}`, with `{$Gamma(n + 1) = n!$}`
    pub const GAMMA: Symbol = Symbol(52);
    /// Beta function, rewritten as `{$B(a, b) = (Gamma(a) Gamma(b)) / Gamma(a + b)$}`
    pub const BETA: Symbol = Symbol(53);
    /// Digamma function, rewritten as `{$psi(x) = "polygamma"(0, x)$}`
    pub const DIGAMMA: Symbol = Symbol(54);
    /// Polygamma function `polygamma(m, x)`, the `m`-th derivative of `{$psi(x) = Gamma'(x) / Gamma(x)$}`
    pub const POLYGAMMA: Symbol = Symbol(55);
    /// Riemann zeta function `{$zeta(s) = sum_(n >= 1) n^(-s)$}`
    pub const ZETA: Symbol = Symbol(56);
    /// The Euler-Mascheroni constant `{$gamma = -psi(1)$}`
    pub const EULER_GAMMA: Symbol = Symbol(57);
    /// Sum `sum(f, k, a, b)` of `f` for the integers `k` from `a` to `b`, which may be infinite
    pub const SUM: Symbol = Symbol(58);
    /// Product `product(f, k, a, b)` of `f` for the integers `k` from `a` to `b`, which may be infinite
    pub const PRODUCT: Symbol = Symbol(59);
    /// Solve an ordinary differential equation, like `dsolve(y' = y)`, only allowed as a whole statement
    pub const DSOLVE: Symbol = Symbol(60);
    /// Transpose of a matrix
    pub const TRANSPOSE: Symbol = Symbol(61);
    /// Trace of a square matrix, the sum of its diagonal
    pub const TRACE: Symbol = Symbol(62);
    /// Rank of a matrix
    pub const RANK: Symbol = Symbol(63);
    /// Kernel of a matrix, a matrix whose columns are a basis of it
    pub const KERNEL: Symbol = Symbol(64);
    /// Characteristic polynomial `charpoly(A, x)` of a square matrix, `{$det(x I - A)$}`, in `x` by default
    pub const CHARPOLY: Symbol = Symbol(65);
    /// Eigenvalues of a square matrix, as a column vector repeating them by algebraic multiplicity
    pub const EIGENVALUES: Symbol = Symbol(66);
    /// Eigenvectors of a square matrix, as a matrix whose columns are bases of the eigenspaces, ordered like `eigenvalues`
    pub const EIGENVECTORS: Symbol = Symbol(67);
    /// Hermite normal form of a matrix over `{$ZZ$}` or `{$ZZ\/n ZZ$}`
    pub const HERMITE: Symbol = Symbol(68);
    /// Smith normal form of a matrix over `{$ZZ$}` or `{$ZZ\/n ZZ$}`
    pub const SMITH: Symbol = Symbol(69);
    /// Partial fraction decomposition `apart(f, x)` of a rational function, in its only symbol by default
    pub const APART: Symbol = Symbol(70);
    /// Principal branch `{$W_0$}` of the Lambert W function, the inverse of `{$x e^x$}` on `{$[-1, oo)$}`, or
    /// with a second argument `-1` the branch `{$W_(-1)$}` ([`Self::lambertw_m1`])
    pub const LAMBERTW: Symbol = Symbol(71);
    /// Piecewise function `piecewise(c_1, v_1, c_2, v_2, ..., default)`, the value of the first true condition
    pub const PIECEWISE: Symbol = Symbol(72);
    /// Gradient `gradient(f, x_1, ..., x_n)` of a scalar function, the column of its partial derivatives, in every
    /// symbol of `f` sorted by name by default
    pub const GRADIENT: Symbol = Symbol(73);
    /// Jacobian matrix `jacobian(F, x_1, ..., x_n)` of a row or column of functions, `{$J_(i j) = diff F_i / diff x_j$}`
    pub const JACOBIAN: Symbol = Symbol(74);
    /// Hessian matrix `hessian(f, x_1, ..., x_n)` of a scalar function, `{$H_(i j) = diff^2 f / (diff x_i diff x_j)$}`
    pub const HESSIAN: Symbol = Symbol(75);
    /// Identity matrix `I(n)` of size `n`
    pub const IDENTITY: Symbol = Symbol(76);
    /// Degree `degree(f, x)` of a polynomial `f` in `x`
    pub const DEGREE: Symbol = Symbol(77);
    /// Minimizers `argmin(f, x)` of a function, only allowed as a whole statement
    pub const ARGMIN: Symbol = Symbol(78);
    /// Maximizers `argmax(f, x)` of a function, only allowed as a whole statement
    pub const ARGMAX: Symbol = Symbol(79);
    /// Local minimizers `localmin(f, x)` of a function, only allowed as a whole statement
    pub const LOCALMIN: Symbol = Symbol(80);
    /// Local maximizers `localmax(f, x)` of a function, only allowed as a whole statement
    pub const LOCALMAX: Symbol = Symbol(81);
    /// Global minima and maxima `extrema(f, x)` of a function with their values, only allowed as a whole statement
    pub const EXTREMA: Symbol = Symbol(82);
    /// Local minima and maxima `localextrema(f, x)` of a function with their values, only allowed as a whole
    /// statement
    pub const LOCALEXTREMA: Symbol = Symbol(83);
    /// Substitution `subs(f, x, a)` of `x` by `a` in `f`
    pub const SUBS: Symbol = Symbol(84);
    /// Numerator `numer(f)` of `f` written as a fraction
    pub const NUMER: Symbol = Symbol(85);
    /// Denominator `denom(f)` of `f` written as a fraction
    pub const DENOM: Symbol = Symbol(86);
    /// Roots `roots(p, x)` of a polynomial, as a column repeated by multiplicity
    pub const ROOTS: Symbol = Symbol(87);
    /// Resultant `resultant(p, q, x)` of two polynomials
    pub const RESULTANT: Symbol = Symbol(88);
    /// Discriminant `discriminant(p, x)` of a polynomial
    pub const DISCRIMINANT: Symbol = Symbol(89);
    /// Complementary error function `{$"erfc"(x) = 1 - "erf"(x)$}`
    pub const ERFC: Symbol = Symbol(90);
    /// Nearest integer `round(x)`, halves rounded up
    pub const ROUND: Symbol = Symbol(91);
    /// Integer part `trunc(x)`, rounded toward zero
    pub const TRUNC: Symbol = Symbol(92);
    /// Primality test `isprime(n)`, 1 for a prime and 0 otherwise
    pub const ISPRIME: Symbol = Symbol(93);
    /// Prime factorization `factorint(n)` of an integer, as rows `[p, e]`
    pub const FACTORINT: Symbol = Symbol(94);
    /// Zero matrix `zeros(n, m)`
    pub const ZEROS: Symbol = Symbol(95);
    /// Diagonal matrix `diag(a_1, ..., a_n)`
    pub const DIAG: Symbol = Symbol(96);
    /// Sine integral `{$"Si"(x) = integral_0^x sin(t)/t dif t$}`
    pub const SI: Symbol = Symbol(97);
    /// Cosine integral `{$"Ci"(x) = gamma + ln x + integral_0^x (cos(t) - 1)/t dif t$}`
    pub const CI: Symbol = Symbol(98);
    /// Exponential integral `{$"Ei"(x) = gamma + ln|x| + integral_0^x (e^t - 1)/t dif t$}`
    pub const EI: Symbol = Symbol(99);
    /// Argument `{$arg(z)$}` of a complex number, in `{$(-pi, pi]$}`
    pub const ARG: Symbol = Symbol(100);
    /// Little-o `{$o(u)$}`, the remainder of a series, negligible compared to `u`
    pub const LITTLE_O: Symbol = Symbol(101);
    /// Real root `rootof(p, x, k)`, the `k`-th real root of the polynomial `p` by increasing order
    pub const ROOTOF: Symbol = Symbol(102);

    #[rustfmt::skip]
    const BUILTIN_NAMES: [&'static str; 103] = [
        "abs", "det", "expand", "factor", "simplify", "re", "im", "conj", "sqrt", "root", "sign",
        "floor", "ceil", "min", "max", "gcd", "lcm", "quo", "rem", "diff", "solve", "approx",
        "exp", "ln", "sin", "cos", "tan", "pi", "e", "lim", "oo", "undefined",
        "series", "asin", "acos", "atan", "sinh", "cosh", "tanh", "asinh", "acosh", "atanh", "cot",
        "sec", "csc", "log", "factorial", "binomial", "integrate", "erf", "erfi", "assume",
        "gamma", "beta", "digamma", "polygamma", "zeta", "euler_gamma", "sum", "product",
        "dsolve", "transpose", "trace", "rank", "kernel", "charpoly", "eigenvalues", "eigenvectors",
        "hermite", "smith", "apart", "lambertw", "piecewise", "gradient", "jacobian", "hessian",
        "I", "degree", "argmin", "argmax", "localmin",
        "localmax", "extrema", "localextrema", "subs", "numer", "denom", "roots", "resultant",
        "discriminant", "erfc", "round", "trunc", "isprime", "factorint", "zeros", "diag", "Si", "Ci",
        "Ei", "arg", "o", "rootof",
    ];

    /// The internal function `@sum(f, k, a, b)`, a sum which isn't evaluated, printed like `sum`: the result of
    /// `series(f, x, a, oo)`, which `sum` would evaluate back to `f`.
    pub(crate) fn held_sum() -> Symbol {
        static HELD_SUM: LazyLock<Symbol> = LazyLock::new(|| Symbol::new("@sum"));
        *HELD_SUM
    }

    /// The internal function `@lambertwm1(x)`, the branch `{$W_(-1)$}` of the Lambert W function, the inverse of
    /// `{$x e^x$}` on `{$(-oo, -1]$}`, written `lambertw(x, -1)`.
    pub(crate) fn lambertw_m1() -> Symbol {
        static LAMBERTW_M1: LazyLock<Symbol> = LazyLock::new(|| Symbol::new("@lambertwm1"));
        *LAMBERTW_M1
    }

    /// The internal function `@rootof(j, c_0, ..., c_n)`, the `j`-th real root (from 0, by increasing order) of the
    /// polynomial `{$c_0 + c_1 x + ... + c_n x^n$}` of degree at least 3, irreducible over `{$QQ$}`, primitive over
    /// `{$ZZ$}` with `{$c_n > 0$}`, written `rootof(p, k)`.
    pub(crate) fn real_root() -> Symbol {
        static REAL_ROOT: LazyLock<Symbol> = LazyLock::new(|| Symbol::new("@rootof"));
        *REAL_ROOT
    }

    /// The internal function `@zetare(a, b)`, `@zetaim`, `@gammare` or `@gammaim` (`function` being
    /// [`Self::ZETA`] or [`Self::GAMMA`]): the real or imaginary part of `{$f(a + i b)$}`, which only has a numerical
    /// form, written in graphs of complex functions.
    pub(crate) fn complex_part(function: Symbol, imaginary: bool) -> Symbol {
        static PARTS: LazyLock<[Symbol; 4]> =
            LazyLock::new(|| ["@zetare", "@zetaim", "@gammare", "@gammaim"].map(Symbol::new));
        PARTS[usize::from(function == Self::GAMMA) * 2 + usize::from(imaginary)]
    }

    /// Return `true` if `symbol` is a builtin constant, like `{$pi$}`, which is not a function.
    #[must_use]
    pub const fn is_builtin_constant(symbol: Symbol) -> bool {
        matches!(
            symbol,
            Self::PI | Self::E | Self::OO | Self::UNDEFINED | Self::EULER_GAMMA
        )
    }

    /// Return `true` if `symbol` is a builtin returning a matrix, like `transpose`, which is a function of the
    /// matrix set and not of its scalars.
    #[must_use]
    pub const fn returns_matrix(symbol: Symbol) -> bool {
        matches!(
            symbol,
            Self::TRANSPOSE
                | Self::KERNEL
                | Self::EIGENVALUES
                | Self::EIGENVECTORS
                | Self::HERMITE
                | Self::SMITH
                | Self::GRADIENT
                | Self::JACOBIAN
                | Self::HESSIAN
                | Self::IDENTITY
                | Self::ROOTS
                | Self::FACTORINT
                | Self::ZEROS
                | Self::DIAG
        )
    }

    /// Return the minimum and maximum number of arguments of a builtin function, or `None` if `symbol` isn't a builtin.
    #[must_use]
    pub const fn builtin_arity(symbol: Symbol) -> Option<(usize, usize)> {
        match symbol {
            Self::ROOT
            | Self::GCD
            | Self::LCM
            | Self::QUO
            | Self::REM
            | Self::BINOMIAL
            | Self::BETA
            | Self::POLYGAMMA => Some((2, 2)),
            Self::MIN
            | Self::MAX
            | Self::SOLVE
            | Self::ASSUME
            | Self::DSOLVE
            | Self::GRADIENT
            | Self::JACOBIAN
            | Self::HESSIAN
            | Self::ARGMIN
            | Self::ARGMAX
            | Self::LOCALMIN
            | Self::LOCALMAX
            | Self::EXTREMA
            | Self::LOCALEXTREMA
            | Self::DIAG => Some((1, usize::MAX)),
            Self::APPROX
            | Self::LOG
            | Self::CHARPOLY
            | Self::LAMBERTW
            | Self::ROOTS
            | Self::DISCRIMINANT
            | Self::ZEROS
            | Self::APART
            | Self::DEGREE => Some((1, 2)),
            Self::SUBS => Some((3, 3)),
            Self::RESULTANT | Self::DIFF | Self::ROOTOF => Some((2, 3)),
            Self::PIECEWISE => Some((2, usize::MAX)),
            Self::LIM => Some((3, 4)),
            Self::SERIES => Some((3, 5)),
            Self::INTEGRATE => Some((2, 4)),
            Self::SUM | Self::PRODUCT => Some((4, 4)),
            Self::PI | Self::E | Self::OO | Self::UNDEFINED | Self::EULER_GAMMA => Some((0, 0)),
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
        // Builtins like `Context::UNDEFINED` may be used before any symbol was interned
        LazyLock::force(&GLOBAL_CONTEXT);
        &SYMBOLS[symbol.0]
    }
}

impl Default for Context {
    fn default() -> Self {
        Self::new()
    }
}
