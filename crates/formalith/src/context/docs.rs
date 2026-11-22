//! User documentation of the builtins: signature, description and examples, shown by the `help` of sessions and
//! the documentation page of the website (`./dev docs`, the example `builtin_docs` of `formalith-session`).
//!
//! Example results are written by hand, as Typst math which also reads as plain text.

use super::{Context, Symbol};

/// A group of related builtins.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Category {
    /// Constants like `{$pi$}`
    Constants,
    /// Numbers: absolute value, rounding, divisibility...
    Arithmetic,
    /// Parts of complex numbers
    Complex,
    /// Exponential, logarithm, trigonometric and hyperbolic functions
    Elementary,
    /// Gamma, zeta, error functions...
    Special,
    /// Rewriting expressions: expansion, factorization, approximation...
    Algebra,
    /// Derivatives, integrals, limits, series, sums and products
    Calculus,
    /// Matrices and vector calculus
    Matrices,
    /// Builtins only allowed as a whole statement: solving equations, assumptions
    Statements,
}

impl Category {
    /// Every category, in the order they are documented.
    pub const ALL: [Self; 9] = [
        Self::Constants,
        Self::Arithmetic,
        Self::Complex,
        Self::Elementary,
        Self::Special,
        Self::Algebra,
        Self::Calculus,
        Self::Matrices,
        Self::Statements,
    ];

    /// The title of the category.
    #[must_use]
    pub const fn title(self) -> &'static str {
        match self {
            Self::Constants => "Constants",
            Self::Arithmetic => "Arithmetic",
            Self::Complex => "Complex numbers",
            Self::Elementary => "Elementary functions",
            Self::Special => "Special functions",
            Self::Algebra => "Algebra",
            Self::Calculus => "Calculus",
            Self::Matrices => "Matrices",
            Self::Statements => "Statements",
        }
    }

    /// The builtins of the category, in the order of their identifiers.
    pub fn builtins(self) -> impl Iterator<Item = &'static BuiltinDoc> {
        BUILTIN_DOCS.iter().filter(move |doc| doc.category == self)
    }
}

/// An example of a builtin: an input, the set it is evaluated in and its result.
#[derive(Clone, Copy, Debug)]
pub struct Example {
    /// The set, as written after `:set` (`R`, `Z/7`, `M(Z)`...)
    pub set: &'static str,
    /// The line evaluated
    pub input: &'static str,
    /// The result, as Typst math
    pub result: &'static str,
}

/// The documentation of a builtin.
#[derive(Clone, Copy, Debug)]
pub struct BuiltinDoc {
    /// The builtin
    pub symbol: Symbol,
    /// Its group
    pub category: Category,
    /// How it is called, optional arguments in brackets, like `integrate(f, x, [a, b])`
    pub signature: &'static str,
    /// What it is, in one line
    pub summary: &'static str,
    /// More details, possibly empty: the sets it is evaluated in, default arguments, rules...
    pub details: &'static str,
    /// Examples
    pub examples: &'static [Example],
}

impl BuiltinDoc {
    /// The name of the builtin.
    #[must_use]
    pub const fn name(&self) -> &'static str {
        Context::BUILTIN_NAMES[self.symbol.0]
    }
}

/// The documentation of the builtin named `name`, if there is one.
#[must_use]
pub fn find(name: &str) -> Option<&'static BuiltinDoc> {
    BUILTIN_DOCS.iter().find(|doc| doc.name() == name)
}

/// An example in `R`.
const fn ex(input: &'static str, result: &'static str) -> Example {
    ex_in("R", input, result)
}

/// An example in `set`.
const fn ex_in(set: &'static str, input: &'static str, result: &'static str) -> Example {
    Example { set, input, result }
}

const fn doc(
    symbol: Symbol,
    category: Category,
    signature: &'static str,
    summary: &'static str,
    details: &'static str,
    examples: &'static [Example],
) -> BuiltinDoc {
    BuiltinDoc {
        symbol,
        category,
        signature,
        summary,
        details,
        examples,
    }
}

use Category::{
    Algebra, Arithmetic, Calculus, Complex, Constants, Elementary, Matrices, Special, Statements,
};

/// The documentation of every builtin, indexed by their identifier.
pub static BUILTIN_DOCS: [BuiltinDoc; Context::BUILTIN_NAMES.len()] = [
    doc(
        Context::ABS,
        Arithmetic,
        "abs(x)",
        "Absolute value.",
        "Dropped when the sign of its argument is known, from its structure or the assumptions.",
        &[ex("abs(-3)", "3"), ex("abs(x^2 + 1)", "x^2 + 1")],
    ),
    doc(
        Context::DET,
        Matrices,
        "det(A)",
        "Determinant of a square matrix.",
        "Evaluated in every set, its argument being parsed as a matrix over the set.",
        &[
            ex_in("M", "det([[a, b], [c, d]])", "a d - b c"),
            ex("det([[1, 2], [3, 4]])", "-2"),
        ],
    ),
    doc(
        Context::EXPAND,
        Algebra,
        "expand(f)",
        "Expands products and powers of sums.",
        "In R, also applies the addition formulas of sin and cos.",
        &[
            ex("expand((x + 1)^3)", "x^3 + 3 x^2 + 3 x + 1"),
            ex("expand(sin(a + b))", "sin(a) cos(b) + sin(b) cos(a)"),
        ],
    ),
    doc(
        Context::FACTOR,
        Algebra,
        "factor(f)",
        "Factors a polynomial.",
        "Over the rationals in R, modulo a prime in Z/p for univariate polynomials.",
        &[
            ex("factor(x^4 - 1)", "(x^2 + 1) (x - 1) (x + 1)"),
            ex_in("Z/7", "factor(x^3 + 1)", "(x + 1) (x + 2) (x + 4)"),
        ],
    ),
    doc(
        Context::SIMPLIFY,
        Algebra,
        "simplify(f)",
        "Simplifies an expression.",
        "Cancels common factors of fractions. In R, also tries identities like sin^2 + cos^2 = 1, multiple \
         angles, hyperbolic functions as exponentials and exp(c ln u) = u^c, keeping the smallest result.",
        &[
            ex("simplify((x^2 - 1)/(x - 1))", "x + 1"),
            ex("simplify(sin(x)^2 + cos(x)^2)", "1"),
        ],
    ),
    doc(
        Context::RE,
        Complex,
        "re(z)",
        "Real part of a complex number.",
        "Symbols are assumed real.",
        &[ex_in("C", "re(3 + 4*i)", "3")],
    ),
    doc(
        Context::IM,
        Complex,
        "im(z)",
        "Imaginary part of a complex number.",
        "Symbols are assumed real.",
        &[ex_in("C", "im(3 + 4*i)", "4")],
    ),
    doc(
        Context::CONJ,
        Complex,
        "conj(z)",
        "Complex conjugate.",
        "Symbols are assumed real.",
        &[ex_in("C", "conj(3 + 4*i)", "3 - 4 i")],
    ),
    doc(
        Context::SQRT,
        Arithmetic,
        "sqrt(x)",
        "Square root, x^(1/2).",
        "Perfect squares are taken out and nested radicals are denested when possible. In C, the square root of a \
         negative number is imaginary.",
        &[
            ex("sqrt(8)", "2 sqrt(2)"),
            ex("sqrt(4*x^2)", "2 abs(x)"),
            ex_in("C", "sqrt(-4)", "2 i"),
        ],
    ),
    doc(
        Context::ROOT,
        Arithmetic,
        "root(x, n)",
        "n-th root, x^(1/n).",
        "",
        &[ex("root(27, 3)", "3")],
    ),
    doc(
        Context::SIGN,
        Arithmetic,
        "sign(x)",
        "Sign: -1, 0 or 1.",
        "Evaluated when the sign is known, from the structure or the assumptions.",
        &[ex("sign(-2)", "-1"), ex("sign(x^2 + 1)", "1")],
    ),
    doc(
        Context::FLOOR,
        Arithmetic,
        "floor(x)",
        "Largest integer less than or equal to x.",
        "",
        &[ex("floor(7/2)", "3")],
    ),
    doc(
        Context::CEIL,
        Arithmetic,
        "ceil(x)",
        "Smallest integer greater than or equal to x.",
        "",
        &[ex("ceil(7/2)", "4")],
    ),
    doc(
        Context::MIN,
        Arithmetic,
        "min(x_1, ..., x_n)",
        "Minimum of its arguments.",
        "",
        &[ex("min(3, 1, 2)", "1"), ex("min(x, 2)", "min(x, 2)")],
    ),
    doc(
        Context::MAX,
        Arithmetic,
        "max(x_1, ..., x_n)",
        "Maximum of its arguments.",
        "",
        &[ex("max(3, 1, 2)", "3")],
    ),
    doc(
        Context::GCD,
        Arithmetic,
        "gcd(a, b)",
        "Greatest common divisor of two integers or polynomials.",
        "Evaluated in Z, Z/n and the polynomial rings K[x].",
        &[
            ex_in("Z", "gcd(12, 18)", "6"),
            ex_in("R[x]", "gcd(x^2 - 1, x^2 + 2*x + 1)", "x + 1"),
        ],
    ),
    doc(
        Context::LCM,
        Arithmetic,
        "lcm(a, b)",
        "Least common multiple of two integers or polynomials.",
        "Evaluated in Z, Z/n and the polynomial rings K[x].",
        &[ex_in("Z", "lcm(4, 6)", "12")],
    ),
    doc(
        Context::QUO,
        Arithmetic,
        "quo(a, b)",
        "Quotient of the Euclidean division of a by b.",
        "Evaluated in Z, Z/n and the polynomial rings K[x].",
        &[ex_in("Z", "quo(17, 5)", "3")],
    ),
    doc(
        Context::REM,
        Arithmetic,
        "rem(a, b)",
        "Remainder of the Euclidean division of a by b.",
        "Evaluated in Z, Z/n and the polynomial rings K[x].",
        &[
            ex_in("Z", "rem(17, 5)", "2"),
            ex_in("R[x]", "rem(x^3 + 1, x - 1)", "2"),
        ],
    ),
    doc(
        Context::DIFF,
        Calculus,
        "diff(f, x, [n])",
        "n-th derivative of f with respect to x (the first by default).",
        "",
        &[
            ex("diff(x^3, x)", "3 x^2"),
            ex("diff(sin(x), x, 2)", "-sin(x)"),
        ],
    ),
    doc(
        Context::SOLVE,
        Statements,
        "solve(e_1, ..., e_n, [x_1, ..., x_m])",
        "Solves equations or inequalities for the listed unknowns.",
        "The other symbols are parameters. A line of comma-separated equations like x + y = 3, x - y = 1 is solved \
         for all its symbols. Several solutions are given one per line, and the integer parameters of periodic \
         solutions are named k, k_1... Inequalities are solved in R, with at most 3 unknowns.",
        &[
            ex(
                "solve(a*x + y = 1, x - y = b, x, y)",
                "x = (b + 1)/(a + 1), y = (1 - a b)/(a + 1)",
            ),
            ex("solve(x^2 = 2, x)", "x = sqrt(2) \\ x = -sqrt(2)"),
            ex("solve(x^2 > 1, x)", "x in (-oo, -1) union (1, oo)"),
        ],
    ),
    doc(
        Context::APPROX,
        Algebra,
        "approx(x, [digits])",
        "Numerical approximation to a number of significant digits (15 by default).",
        "Integrals are approximated by double exponential quadrature.",
        &[
            ex("approx(pi)", "3.14159265358979"),
            ex("approx(sqrt(2), 30)", "1.41421356237309504880168872421"),
            ex("approx(integrate(exp(-x^2), x, 0, 1))", "0.746824132812427"),
        ],
    ),
    doc(
        Context::EXP,
        Elementary,
        "exp(x)",
        "Exponential function, also written e^x.",
        "",
        &[
            ex("exp(ln(5))", "5"),
            ex("exp(2*ln(3))", "9"),
            ex_in("C", "exp(i*pi)", "-1"),
        ],
    ),
    doc(
        Context::LN,
        Elementary,
        "ln(x)",
        "Natural logarithm.",
        "",
        &[ex("ln(e^3)", "3"), ex("ln(1/2)", "-ln(2)")],
    ),
    doc(
        Context::SIN,
        Elementary,
        "sin(x)",
        "Sine.",
        "Exact values at multiples of pi/12, pi/10 and pi/8.",
        &[ex("sin(pi/6)", "1/2"), ex("sin(-x)", "-sin(x)")],
    ),
    doc(
        Context::COS,
        Elementary,
        "cos(x)",
        "Cosine.",
        "Exact values at multiples of pi/12, pi/10 and pi/8.",
        &[ex("cos(pi/4)", "sqrt(2)/2")],
    ),
    doc(
        Context::TAN,
        Elementary,
        "tan(x)",
        "Tangent.",
        "",
        &[ex("tan(pi/3)", "sqrt(3)")],
    ),
    doc(
        Context::PI,
        Constants,
        "pi",
        "The constant pi = 3.14159...",
        "",
        &[ex("approx(pi)", "3.14159265358979")],
    ),
    doc(
        Context::E,
        Constants,
        "e",
        "Euler's number e = 2.71828..., the base of the natural logarithm.",
        "",
        &[ex("ln(e^3)", "3")],
    ),
    doc(
        Context::LIM,
        Calculus,
        "lim(f, x, a, [side])",
        "Limit of f when x tends to a.",
        "a may be oo or -oo. side is 1 for the limit from the right, -1 from the left. A limit that doesn't exist \
         is undefined.",
        &[
            ex("lim(sin(x)/x, x, 0)", "1"),
            ex("lim(1/x, x, 0, 1)", "oo"),
            ex("lim(x*sin(1/x), x, 0)", "0"),
        ],
    ),
    doc(
        Context::OO,
        Constants,
        "oo",
        "Infinity, a limit point or the result of a limit.",
        "",
        &[ex("exp(-oo)", "0"), ex("lim(1/x, x, 0, 1)", "oo")],
    ),
    doc(
        Context::UNDEFINED,
        Constants,
        "undefined",
        "The result of a limit that doesn't exist, or of an indeterminate form like oo - oo.",
        "",
        &[ex("lim(1/x, x, 0)", "\"undefined\"")],
    ),
    doc(
        Context::SERIES,
        Calculus,
        "series(f, x, a, [n, side])",
        "Series expansion of f at a, the terms below (x - a)^n (6 by default).",
        "At oo, the terms below x^-n. side is 1 or -1 like for lim. Exponents may be negative or fractional.",
        &[
            ex("series(exp(x), x, 0, 4)", "1 + x + x^2/2 + x^3/6"),
            ex("series(sin(x), x, 0)", "x - x^3/6 + x^5/120"),
        ],
    ),
    doc(
        Context::ASIN,
        Elementary,
        "asin(x)",
        "Arcsine.",
        "",
        &[ex("asin(1/2)", "pi/6")],
    ),
    doc(
        Context::ACOS,
        Elementary,
        "acos(x)",
        "Arccosine.",
        "",
        &[ex("acos(0)", "pi/2")],
    ),
    doc(
        Context::ATAN,
        Elementary,
        "atan(x)",
        "Arctangent.",
        "",
        &[ex("atan(1)", "pi/4")],
    ),
    doc(
        Context::SINH,
        Elementary,
        "sinh(x)",
        "Hyperbolic sine.",
        "",
        &[ex("sinh(0)", "0")],
    ),
    doc(
        Context::COSH,
        Elementary,
        "cosh(x)",
        "Hyperbolic cosine.",
        "",
        &[ex("diff(cosh(x), x)", "sinh(x)")],
    ),
    doc(
        Context::TANH,
        Elementary,
        "tanh(x)",
        "Hyperbolic tangent.",
        "",
        &[ex("tanh(0)", "0")],
    ),
    doc(
        Context::ASINH,
        Elementary,
        "asinh(x)",
        "Inverse hyperbolic sine.",
        "",
        &[ex("asinh(0)", "0")],
    ),
    doc(
        Context::ACOSH,
        Elementary,
        "acosh(x)",
        "Inverse hyperbolic cosine.",
        "",
        &[ex("acosh(1)", "0")],
    ),
    doc(
        Context::ATANH,
        Elementary,
        "atanh(x)",
        "Inverse hyperbolic tangent.",
        "",
        &[ex("atanh(0)", "0")],
    ),
    doc(
        Context::COT,
        Elementary,
        "cot(x)",
        "Cotangent, rewritten as cos(x)/sin(x).",
        "",
        &[ex("cot(x)", "cos(x)/sin(x)")],
    ),
    doc(
        Context::SEC,
        Elementary,
        "sec(x)",
        "Secant, rewritten as 1/cos(x).",
        "",
        &[ex("sec(x)", "1/cos(x)")],
    ),
    doc(
        Context::CSC,
        Elementary,
        "csc(x)",
        "Cosecant, rewritten as 1/sin(x).",
        "",
        &[ex("csc(x)", "1/sin(x)")],
    ),
    doc(
        Context::LOG,
        Elementary,
        "log(x, [b])",
        "Logarithm in base b (10 by default), rewritten as ln(x)/ln(b).",
        "",
        &[ex("log(100)", "2"), ex("log(8, 2)", "3")],
    ),
    doc(
        Context::FACTORIAL,
        Arithmetic,
        "factorial(n)",
        "Factorial n!, extended to half-integers.",
        "",
        &[
            ex("factorial(5)", "120"),
            ex("factorial(1/2)", "sqrt(pi)/2"),
        ],
    ),
    doc(
        Context::BINOMIAL,
        Arithmetic,
        "binomial(n, k)",
        "Binomial coefficient, n choose k.",
        "Evaluated for a natural k and a rational n.",
        &[ex("binomial(5, 2)", "10")],
    ),
    doc(
        Context::INTEGRATE,
        Calculus,
        "integrate(f, x, [a, b])",
        "Antiderivative of f with respect to x, or definite integral from a to b.",
        "Bounds may be oo or -oo, and depend on other variables. Rational functions, the Risch algorithm, \
         substitutions and integration by parts are used. An integral with no elementary antiderivative stays \
         unevaluated, a divergent one is oo, -oo or undefined. Logarithms are ln|u| unless u is positive.",
        &[
            ex("integrate(x^2, x)", "x^3/3"),
            ex("integrate(ln(x), x)", "x ln(x) - x"),
            ex("integrate(exp(-x^2), x, -oo, oo)", "sqrt(pi)"),
            ex("integrate(1/(x^2 + 1), x, 0, 1)", "pi/4"),
        ],
    ),
    doc(
        Context::ERF,
        Special,
        "erf(x)",
        "Error function, 2/sqrt(pi) times the integral of e^(-t^2) from 0 to x.",
        "",
        &[
            ex("erf(0)", "0"),
            ex("diff(erf(x), x)", "2 exp(-x^2)/sqrt(pi)"),
        ],
    ),
    doc(
        Context::ERFI,
        Special,
        "erfi(x)",
        "Imaginary error function, 2/sqrt(pi) times the integral of e^(t^2) from 0 to x.",
        "",
        &[ex("diff(erfi(x), x)", "2 exp(x^2)/sqrt(pi)")],
    ),
    doc(
        Context::ASSUME,
        Statements,
        "assume(r_1, ..., r_n)",
        "Declares assumptions on symbols, like a > 0, b != 0, c <= 0 or n integer.",
        "Each comparison compares a symbol with 0. Assumptions simplify expressions (sqrt(a^2) = a when a > 0), \
         and are used by integrals, limits and solving. assume(a) shows the assumptions on a, :clear a removes \
         them.",
        &[
            ex("assume(a > 0)", "a > 0"),
            ex("assume(n integer)", "n in ZZ"),
        ],
    ),
    doc(
        Context::GAMMA,
        Special,
        "gamma(x)",
        "Gamma function, with gamma(n + 1) = n!.",
        "Exact values at integers and half-integers.",
        &[ex("gamma(5)", "24"), ex("gamma(1/2)", "sqrt(pi)")],
    ),
    doc(
        Context::BETA,
        Special,
        "beta(a, b)",
        "Beta function, rewritten as gamma(a) gamma(b)/gamma(a + b).",
        "",
        &[ex("beta(2, 3)", "1/12")],
    ),
    doc(
        Context::DIGAMMA,
        Special,
        "digamma(x)",
        "Digamma function psi = gamma'/gamma, rewritten as polygamma(0, x).",
        "",
        &[ex("digamma(1)", "-gamma")],
    ),
    doc(
        Context::POLYGAMMA,
        Special,
        "polygamma(m, x)",
        "Polygamma function, the m-th derivative of the digamma function.",
        "Exact values at integers and half-integers.",
        &[
            ex("polygamma(0, 2)", "1 - gamma"),
            ex("polygamma(1, 1)", "pi^2/6"),
        ],
    ),
    doc(
        Context::ZETA,
        Special,
        "zeta(s)",
        "Riemann zeta function, the sum of n^(-s) for n >= 1.",
        "Exact values at even and non-positive integers.",
        &[ex("zeta(2)", "pi^2/6"), ex("zeta(-1)", "-1/12")],
    ),
    doc(
        Context::EULER_GAMMA,
        Constants,
        "euler_gamma",
        "The Euler-Mascheroni constant gamma = 0.57721..., equal to -digamma(1).",
        "",
        &[ex("digamma(1)", "-gamma")],
    ),
    doc(
        Context::SUM,
        Calculus,
        "sum(f, k, a, b)",
        "Sum of f for the integers k from a to b.",
        "Bounds may be oo or -oo. Closed forms come from Faulhaber's formula, geometric sums, Gosper's algorithm, \
         digamma functions for rational functions and known series.",
        &[
            ex("sum(k, k, 1, n)", "n (n + 1)/2"),
            ex("sum(1/k^2, k, 1, oo)", "pi^2/6"),
        ],
    ),
    doc(
        Context::PRODUCT,
        Calculus,
        "product(f, k, a, b)",
        "Product of f for the integers k from a to b.",
        "Bounds may be oo or -oo.",
        &[
            ex("product(k, k, 1, n)", "n!"),
            ex("product(1 + 1/k, k, 1, n)", "n + 1"),
        ],
    ),
    doc(
        Context::DSOLVE,
        Statements,
        "dsolve(equation, [conditions...], [y, x])",
        "Solves an ordinary differential equation, with initial conditions like y(0) = 1 or y'(0) = 0.",
        "The function and the variable are found from the equation (y and x by default), or given as the last two \
         arguments. First order equations may be linear or separable, higher orders linear with constant \
         coefficients. Constants are named c_1, c_2...",
        &[
            ex("dsolve(y' = x*y)", "y(x) = c_1 exp(x^2/2)"),
            ex("dsolve(y'' + y = 0, y(0) = 1, y'(0) = 0)", "y(x) = cos(x)"),
            ex("dsolve(diff(y(t), t) = t, y, t)", "y(t) = t^2/2 + c_1"),
        ],
    ),
    doc(
        Context::TRANSPOSE,
        Matrices,
        "transpose(A)",
        "Transpose of a matrix.",
        "",
        &[ex_in("M", "transpose([[1, 2], [3, 4]])", "mat(1, 3; 2, 4)")],
    ),
    doc(
        Context::TRACE,
        Matrices,
        "trace(A)",
        "Trace of a square matrix, the sum of its diagonal.",
        "",
        &[ex_in("M", "trace([[1, 2], [3, 4]])", "5")],
    ),
    doc(
        Context::RANK,
        Matrices,
        "rank(A)",
        "Rank of a matrix.",
        "",
        &[ex_in("M", "rank([[1, 2], [2, 4]])", "1")],
    ),
    doc(
        Context::KERNEL,
        Matrices,
        "kernel(A)",
        "Kernel of a matrix, as a matrix whose columns are a basis of it.",
        "A zero column for the zero kernel. Over Z, a basis of the lattice.",
        &[ex_in("M", "kernel([[1, 2], [2, 4]])", "mat(-2; 1)")],
    ),
    doc(
        Context::CHARPOLY,
        Matrices,
        "charpoly(A, [x])",
        "Characteristic polynomial det(x I - A) of a square matrix, in x by default.",
        "",
        &[ex_in("M", "charpoly([[1, 2], [3, 4]])", "x^2 - 5 x - 2")],
    ),
    doc(
        Context::EIGENVALUES,
        Matrices,
        "eigenvalues(A)",
        "Eigenvalues of a square matrix, as a column repeating them by algebraic multiplicity.",
        "In M, when every root of the characteristic polynomial is found.",
        &[ex_in("M", "eigenvalues([[2, 1], [1, 2]])", "mat(1; 3)")],
    ),
    doc(
        Context::EIGENVECTORS,
        Matrices,
        "eigenvectors(A)",
        "Eigenvectors of a square matrix, as columns, by eigenspace in the order of eigenvalues.",
        "",
        &[ex_in(
            "M",
            "eigenvectors([[2, 1], [1, 2]])",
            "mat(-1, 1; 1, 1)",
        )],
    ),
    doc(
        Context::HERMITE,
        Matrices,
        "hermite(A)",
        "Hermite normal form H = U A of an integer matrix.",
        "In M(Z) and M(Z/n).",
        &[ex_in(
            "M(Z)",
            "hermite([[2, 4], [6, 8]])",
            "mat(2, 0; 0, 4)",
        )],
    ),
    doc(
        Context::SMITH,
        Matrices,
        "smith(A)",
        "Smith normal form D = U A V of an integer matrix.",
        "In M(Z) and M(Z/n).",
        &[ex_in("M(Z)", "smith([[2, 4], [6, 8]])", "mat(2, 0; 0, 4)")],
    ),
    doc(
        Context::APART,
        Algebra,
        "apart(f, [x])",
        "Partial fraction decomposition of a rational function in x.",
        "x may be omitted when f has a single symbol. Over the rationals in R, over the Gaussian rationals in C.",
        &[
            ex("apart(1/(x^2 - 1))", "1/(2 (x - 1)) - 1/(2 (x + 1))"),
            ex_in("C", "apart(1/(x^2 + 1))", "i/(2 (x + i)) - i/(2 (x - i))"),
        ],
    ),
    doc(
        Context::LAMBERTW,
        Special,
        "lambertw(x)",
        "Principal branch W_0 of the Lambert W function, the inverse of x e^x on [-1, oo).",
        "",
        &[ex("lambertw(e)", "1"), ex("lambertw(0)", "0")],
    ),
    doc(
        Context::PIECEWISE,
        Special,
        "piecewise(c_1, v_1, ..., c_n, v_n, [default])",
        "The value of the first true condition, else the default value.",
        "Conditions are comparisons. Without a default and no true condition, the value is undefined.",
        &[
            ex(
                "piecewise(x < 0, -x, x)",
                "cases(-x & \"if \" x < 0, x & \"otherwise\")",
            ),
            ex("piecewise(2 < 1, 0, 1)", "1"),
        ],
    ),
    doc(
        Context::GRADIENT,
        Matrices,
        "gradient(f, [x_1, ..., x_n])",
        "Gradient of a scalar function, the column of its partial derivatives.",
        "The variables are every symbol of f, sorted by name, by default. In M.",
        &[ex_in("M", "gradient(x^2*y, x, y)", "mat(2 x y; x^2)")],
    ),
    doc(
        Context::JACOBIAN,
        Matrices,
        "jacobian(F, [x_1, ..., x_n])",
        "Jacobian matrix of a row or column of functions, J_(i j) = d F_i / d x_j.",
        "The variables are every symbol of F, sorted by name, by default. In M.",
        &[ex_in(
            "M",
            "jacobian([[x*y, x + y]], x, y)",
            "mat(y, x; 1, 1)",
        )],
    ),
    doc(
        Context::HESSIAN,
        Matrices,
        "hessian(f, [x_1, ..., x_n])",
        "Hessian matrix of a scalar function, its second partial derivatives.",
        "The variables are every symbol of f, sorted by name, by default. In M.",
        &[ex_in("M", "hessian(x^2*y)", "mat(2 y, 2 x; 2 x, 0)")],
    ),
    doc(
        Context::IDENTITY,
        Matrices,
        "I(n)",
        "Identity matrix of size n.",
        "",
        &[
            ex_in("M", "I(2)", "mat(1, 0; 0, 1)"),
            ex_in("M", "2*I(2)", "mat(2, 0; 0, 2)"),
        ],
    ),
    doc(
        Context::DEGREE,
        Algebra,
        "degree(f, [x])",
        "Degree of a polynomial in x.",
        "x may be omitted when f has a single symbol. Unevaluated for 0 and non-polynomials. In R, exponents may \
         be symbols assumed to be natural numbers.",
        &[
            ex("degree(x^3 + x)", "3"),
            ex("degree(x^2*y + y^3, y)", "3"),
        ],
    ),
];

#[cfg(test)]
mod tests {
    use std::collections::HashSet;

    use super::*;

    #[test]
    fn every_builtin_is_documented_once() {
        for (id, doc) in BUILTIN_DOCS.iter().enumerate() {
            assert_eq!(
                doc.symbol,
                Symbol(id),
                "the documentation of `{}`",
                doc.name()
            );
            assert!(!doc.examples.is_empty(), "`{}` has no example", doc.name());
        }
        let names: HashSet<_> = BUILTIN_DOCS.iter().map(BuiltinDoc::name).collect();
        assert_eq!(names.len(), BUILTIN_DOCS.len());
    }

    #[test]
    fn find_by_name() {
        assert_eq!(find("integrate").unwrap().symbol, Context::INTEGRATE);
        assert!(find("x").is_none());
    }
}
