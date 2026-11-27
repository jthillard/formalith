//! User documentation of the builtins: signature, description and examples.
//!
//! It is shown by the `help` of sessions and the documentation page of the website (`./dev docs`, the example `builtin_docs` of `formalith-session`).
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
            ex_in("M(R)", "det([[a, b], [c, d]])", "a d - b c"),
            ex("det([[1, 2], [3, 4]])", "-2"),
        ],
    ),
    doc(
        Context::EXPAND,
        Algebra,
        "expand(f)",
        "Expands products and powers of sums.",
        "In R, also applies the addition formulas of sin and cos. On a matrix, expands each entry.",
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
        "Over the rationals in R, over the integers in Z (the content first), modulo a prime in Z/p for univariate polynomials. Powers with fractional exponents are factored as polynomials in a root of their base.",
        &[
            ex("factor(x^4 - 1)", "(x^2 + 1) (x - 1) (x + 1)"),
            ex_in("Z", "factor(6x^2 + 3x)", "3 x (2 x + 1)"),
            ex("factor(x + sqrt(x))", "sqrt(x) (sqrt(x) + 1)"),
            ex_in("Z/7", "factor(x^3 + 1)", "(x + 1) (x + 2) (x + 4)"),
        ],
    ),
    doc(
        Context::SIMPLIFY,
        Algebra,
        "simplify(f)",
        "Simplifies an expression.",
        "Cancels common factors of fractions. In R, also tries identities like sin^2 + cos^2 = 1, multiple \
         angles, hyperbolic functions as exponentials and exp(c ln u) = u^c, keeping the smallest result. On a \
         matrix, simplifies each entry.",
        &[
            ex("simplify((x^2 - 1)/(x - 1))", "x + 1"),
            ex("simplify(sin(x)^2 + cos(x)^2)", "1"),
            ex_in(
                "M(R)",
                "simplify([[sin(x)^2 + cos(x)^2, 1], [0, x]])",
                "mat(1, 1; 0, x)",
            ),
        ],
    ),
    doc(
        Context::RE,
        Complex,
        "re(z)",
        "Real part of a complex number.",
        "Linear over sums and constant factors; constants are split into their parts (re(x) stays unevaluated).",
        &[
            ex_in("C", "re(3 + 4*i)", "3"),
            ex_in("C", "re(exp(i))", "cos(1)"),
        ],
    ),
    doc(
        Context::IM,
        Complex,
        "im(z)",
        "Imaginary part of a complex number.",
        "Linear over sums and constant factors; constants are split into their parts (im(x) stays unevaluated).",
        &[
            ex_in("C", "im(3 + 4*i)", "4"),
            ex_in("C", "im(exp(1 + i))", "e sin(1)"),
        ],
    ),
    doc(
        Context::CONJ,
        Complex,
        "conj(z)",
        "Complex conjugate.",
        "Over sums and products; constants are split into their parts (conj(x) stays unevaluated).",
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
        "Evaluated in Z, Z/n and the polynomial rings K[x]. In Z/n, the arguments are integers and the result is reduced mod n. \
         In Z/n[x] with n composite, it stays unevaluated when a leading coefficient isn't invertible, like 2 x in Z/4[x].",
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
        "Evaluated in Z, Z/n and the polynomial rings K[x]. In Z/n, the arguments are integers and the result is reduced mod n. \
         In Z/n[x] with n composite, it stays unevaluated when a leading coefficient isn't invertible, like 2 x in Z/4[x].",
        &[ex_in("Z", "lcm(4, 6)", "12")],
    ),
    doc(
        Context::QUO,
        Arithmetic,
        "quo(a, b)",
        "Quotient of the Euclidean division of a by b.",
        "Evaluated in Z, Z/n and the polynomial rings K[x]. In Z/n, the arguments are integers and the result is reduced mod n. \
         In Z/n[x] with n composite, it stays unevaluated when a leading coefficient isn't invertible, like 2 x in Z/4[x].",
        &[ex_in("Z", "quo(17, 5)", "3")],
    ),
    doc(
        Context::REM,
        Arithmetic,
        "rem(a, b)",
        "Remainder of the Euclidean division of a by b.",
        "Evaluated in Z, Z/n and the polynomial rings K[x]. In Z/n, the arguments are integers and the result is reduced mod n. \
         In Z/n[x] with n composite, it stays unevaluated when a leading coefficient isn't invertible, like 2 x in Z/4[x].",
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
        "On a matrix, differentiates each entry. The prime notation f'(a), f''(a)... is the derivative of a function \
         of one variable f (a definition, a builtin or an unknown function, kept as diff(g(x), x) at a symbol) at a.",
        &[
            ex("diff(x^3, x)", "3 x^2"),
            ex("diff(sin(x), x, 2)", "-sin(x)"),
            ex("sin''(2 x)", "-sin(2 x)"),
            ex_in(
                "M(R)",
                "diff([[x^2, x], [1, x^3]], x)",
                "mat(2 x, 1; 0, 3 x^2)",
            ),
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
            ex("solve(x^2 > 1, x)", "x in (-oo, -1) union (1, +oo)"),
            ex(
                "solve(sin(x) = cos(x), x)",
                "x = frac(1, 4) pi + pi k \\ k in ZZ",
            ),
            ex("solve(2^x = 3^(x + 1), x)", "x = ln(3)/(ln(2) - ln(3))"),
        ],
    ),
    doc(
        Context::APPROX,
        Algebra,
        "approx(x, [digits])",
        "Numerical approximation to a number of significant digits (15 by default).",
        "Integrals are approximated by double exponential quadrature. In C, the real and imaginary parts of \
         constants are approximated.",
        &[
            ex("approx(pi)", "3.14159265358979"),
            ex("approx(sqrt(2), 30)", "1.41421356237309504880168872421"),
            ex("approx(integrate(exp(-x^2), x, 0, 1))", "0.746824132812427"),
            ex_in(
                "C",
                "approx(exp(i))",
                "0.54030230586814 + 0.841470984807897 i",
            ),
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
        "In C, the principal value ln|z| + i arg(z) of constants other than positive numbers, the argument being \
         in (-pi, pi].",
        &[
            ex("ln(e^3)", "3"),
            ex("ln(1/2)", "-ln(2)"),
            ex_in("C", "ln(-1)", "i pi"),
            ex_in("C", "ln(1 + i)", "ln(2)/2 + (i pi)/4"),
        ],
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
            ex("lim(1/x, x, 0, 1)", "+oo"),
            ex("lim(x*sin(1/x), x, 0)", "0"),
        ],
    ),
    doc(
        Context::OO,
        Constants,
        "oo",
        "Infinity, a limit point or the result of a limit.",
        "",
        &[ex("exp(-oo)", "0"), ex("lim(1/x, x, 0, 1)", "+oo")],
    ),
    doc(
        Context::UNDEFINED,
        Constants,
        "undefined",
        "The value of an expression that has none: a limit that doesn't exist, an indeterminate form like oo - oo, \
         a division by zero, a pole of a function, or an operation on matrices of incompatible sizes.",
        "It absorbs sums, products, powers and functions of it (except the branches of piecewise). Poles: ln(0), \
         tan at odd multiples of pi/2, factorial and gamma at negative integers, polygamma at non-positive \
         integers, zeta(1), atanh(1) and atanh(-1).",
        &[
            ex("lim(1/x, x, 0)", "\"undefined\""),
            ex("1/0", "\"undefined\""),
            ex("ln(0) + 1", "\"undefined\""),
        ],
    ),
    doc(
        Context::SERIES,
        Calculus,
        "series(f, x, a, [n, side])",
        "Series expansion of f at a, the terms below (x - a)^n (6 by default), plus the remainder o((x - a)^(n - 1)).",
        "At oo, the terms below x^-n plus o(x^(1 - n)). side is 1 or -1 like for lim. Exponents may be negative or \
         fractional. With n = oo, the whole series as sums of general terms, when the coefficients satisfy a \
         recurrence c(k + m) = r(k) c(k) with a rational function r (exp, sin, atan, asin, erf, ln(1 + x), \
         (1 + x)^a, their sums and products, rational functions with real poles...). Every general term is proven: \
         from the differential equation of f, or by checking the one the term implies; otherwise the series stays \
         unevaluated. These sums aren't evaluated back.",
        &[
            ex("series(exp(x), x, 0, 4)", "1 + x + x^2/2 + x^3/6 + o(x^3)"),
            ex("series(sin(x), x, 0)", "x - x^3/6 + x^5/120 + o(x^5)"),
            ex("series(exp(x), x, 0, oo)", "sum_(k = 0)^(+oo) x^k/k!"),
            ex(
                "series(sin(x), x, 0, oo)",
                "sum_(k = 0)^(+oo) (-1)^k x^(2k + 1)/(2k + 1)!",
            ),
            ex(
                "series(ln(1 + x), x, 0, oo)",
                "sum_(k = 1)^(+oo) (-1)^(k + 1) x^k/k",
            ),
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
        "Also written `n!`, binding tighter than any operator (`n!^2` is `(n!)^2`, `-3!` is `-6`); `n!=3` is `n != 3`, \
         write `n! = 3`. In Z/n, n is an integer and the result is reduced mod n.",
        &[
            ex("factorial(5)", "120"),
            ex_in("Z/7", "factorial(8)", "0"),
            ex("3!^2", "36"),
            ex("factorial(1/2)", "sqrt(pi)/2"),
        ],
    ),
    doc(
        Context::BINOMIAL,
        Arithmetic,
        "binomial(n, k)",
        "Binomial coefficient, n choose k.",
        "Evaluated for a natural k and a rational n. In Z/n, n and k are integers and the result is reduced mod n.",
        &[
            ex("binomial(5, 2)", "10"),
            ex_in("Z/7", "binomial(10, 3)", "1"),
        ],
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
        "Declares assumptions on symbols, like a > 0, b != 0, a > 1, a > b + 1 or n integer.",
        "Each comparison is a linear relation between symbols with rational coefficients (=, <, <=, >, >=, !=). \
         Bounds of integers are rounded (n > 1/2 is n >= 1). Assumptions simplify expressions (sqrt(a^2) = a when \
         a > 0, abs(a - b) = a - b when a > b), and are used by integrals, limits and solving. assume(a) shows the \
         assumptions on a, :clear a removes them with the relations involving a. Sessions start with k, m and n \
         assumed integer: :assumptions lists every assumption, defaults included, and :clear restores the \
         defaults.",
        &[
            ex("assume(a > 0)", "a > 0"),
            ex("assume(a > 2*b + 1)", "a > 2 b + 1"),
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
         digamma functions for rational functions and known series, and definite sums of hypergeometric terms up to \
         a bound depending on n (like binomial(n, k) from 0 to n) from Zeilberger's algorithm. In Z and Z/n, sums with \
         integer bounds are expanded (up to 1000 terms), the terms and bounds being integers reduced mod n.",
        &[
            ex("sum(k, k, 1, n)", "n (n + 1)/2"),
            ex("sum(1/k^2, k, 1, oo)", "pi^2/6"),
            ex("sum(binomial(n, k), k, 0, n)", "2^n"),
        ],
    ),
    doc(
        Context::PRODUCT,
        Calculus,
        "product(f, k, a, b)",
        "Product of f for the integers k from a to b.",
        "Bounds may be oo or -oo. In Z and Z/n, products with integer bounds are expanded (up to 1000 factors), the \
         factors and bounds being integers reduced mod n.",
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
         coefficients, or homogeneous linear with rational coefficients, solved by power series at an ordinary \
         point (0, or the point of the conditions). Constants are named c_1, c_2...",
        &[
            ex("dsolve(y' = x*y)", "y(x) = c_1 exp(x^2/2)"),
            ex("dsolve(y'' + y = 0, y(0) = 1, y'(0) = 0)", "y(x) = cos(x)"),
            ex("dsolve(diff(y(t), t) = t, y, t)", "y(t) = t^2/2 + c_1"),
            ex(
                "dsolve(y'' - x*y' - y = 0, y(0) = 1, y'(0) = 0)",
                "y(x) = sum_(k = 0)^(+oo) frac(x^(2 k) 2^(-k), k!)",
            ),
        ],
    ),
    doc(
        Context::TRANSPOSE,
        Matrices,
        "transpose(A)",
        "Transpose of a matrix.",
        "",
        &[ex_in(
            "M(R)",
            "transpose([[1, 2], [3, 4]])",
            "mat(1, 3; 2, 4)",
        )],
    ),
    doc(
        Context::TRACE,
        Matrices,
        "trace(A)",
        "Trace of a square matrix, the sum of its diagonal.",
        "",
        &[ex_in("M(R)", "trace([[1, 2], [3, 4]])", "5")],
    ),
    doc(
        Context::RANK,
        Matrices,
        "rank(A)",
        "Rank of a matrix.",
        "",
        &[ex_in("M(R)", "rank([[1, 2], [2, 4]])", "1")],
    ),
    doc(
        Context::KERNEL,
        Matrices,
        "kernel(A)",
        "Kernel of a matrix, as a matrix whose columns are a basis of it.",
        "A zero column for the zero kernel. Over Z, a basis of the lattice.",
        &[ex_in("M(R)", "kernel([[1, 2], [2, 4]])", "mat(-2; 1)")],
    ),
    doc(
        Context::CHARPOLY,
        Matrices,
        "charpoly(A, [x])",
        "Characteristic polynomial det(x I - A) of a square matrix, in x by default.",
        "",
        &[ex_in("M(R)", "charpoly([[1, 2], [3, 4]])", "x^2 - 5 x - 2")],
    ),
    doc(
        Context::EIGENVALUES,
        Matrices,
        "eigenvalues(A)",
        "Eigenvalues of a square matrix, as a column repeating them by algebraic multiplicity.",
        "When every root of the characteristic polynomial is found: in M(R) when they are all real, in M(C) \
         complex ones too.",
        &[
            ex_in("M(R)", "eigenvalues([[2, 1], [1, 2]])", "mat(1; 3)"),
            ex_in("M(C)", "eigenvalues([[0, -1], [1, 0]])", "mat(-i; i)"),
        ],
    ),
    doc(
        Context::EIGENVECTORS,
        Matrices,
        "eigenvectors(A)",
        "Eigenvectors of a square matrix, as columns, by eigenspace in the order of eigenvalues.",
        "In M and M(C), like eigenvalues.",
        &[ex_in(
            "M(R)",
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
        "lambertw(x, [k])",
        "Lambert W function, the inverse of x e^x: the principal branch W_0 on [-1, oo), or W_-1 on (-oo, -1] for k = -1.",
        "W_0 is defined for x >= -1/e, W_-1 for -1/e <= x < 0, where x e^x = c has two solutions.",
        &[
            ex("lambertw(e)", "1"),
            ex("lambertw(0)", "0"),
            ex("lambertw(-2exp(-2), -1)", "-2"),
        ],
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
        "The variables are every symbol of f, sorted by name, by default. In M and M(C).",
        &[ex_in("M(R)", "gradient(x^2*y, x, y)", "mat(2 x y; x^2)")],
    ),
    doc(
        Context::JACOBIAN,
        Matrices,
        "jacobian(F, [x_1, ..., x_n])",
        "Jacobian matrix of a row or column of functions, J_(i j) = d F_i / d x_j.",
        "The variables are every symbol of F, sorted by name, by default. In M and M(C).",
        &[ex_in(
            "M(R)",
            "jacobian([[x*y, x + y]], x, y)",
            "mat(y, x; 1, 1)",
        )],
    ),
    doc(
        Context::HESSIAN,
        Matrices,
        "hessian(f, [x_1, ..., x_n])",
        "Hessian matrix of a scalar function, its second partial derivatives.",
        "The variables are every symbol of f, sorted by name, by default. In M and M(C).",
        &[ex_in("M(R)", "hessian(x^2*y)", "mat(2 y, 2 x; 2 x, 0)")],
    ),
    doc(
        Context::IDENTITY,
        Matrices,
        "I(n)",
        "Identity matrix of size n.",
        "",
        &[
            ex_in("M(R)", "I(2)", "mat(1, 0; 0, 1)"),
            ex_in("M(R)", "2*I(2)", "mat(2, 0; 0, 2)"),
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
    doc(
        Context::ARGMIN,
        Statements,
        "argmin(f, [x_1, ..., x_n]) or argmin(f, x, a, b)",
        "Points where f reaches its global minimum, over the reals or over [a, b].",
        "The variables are every symbol of f by default. With one variable and two more arguments which aren't \
         both symbols of f, they are the bounds (possibly -oo or oo). In R only: functions of one variable are \
         compared at their critical points, where they stop being defined or differentiable, and at the bounds, \
         and with their limits; functions of several variables must be rational functions without parameters. \
         Gives no solution when the minimum isn't reached, like for exp(x).",
        &[
            ex("argmin(x^4 - 2*x^2, x)", "x = -1 \\ x = 1"),
            ex("argmin(x^3 - 3*x, x, -3, 3)", "x = -3"),
            ex("argmin(x^2 + y^2 - 2*x, x, y)", "x = 1, y = 0"),
            ex("argmin(exp(x), x)", "\"no solution\""),
        ],
    ),
    doc(
        Context::ARGMAX,
        Statements,
        "argmax(f, [x_1, ..., x_n]) or argmax(f, x, a, b)",
        "Points where f reaches its global maximum, over the reals or over [a, b].",
        "Like argmin of -f.",
        &[
            ex("argmax(x*exp(-x), x)", "x = 1"),
            ex("argmax(sin(x), x, 0, 4)", "x = pi/2"),
        ],
    ),
    doc(
        Context::LOCALMIN,
        Statements,
        "localmin(f, [x_1, ..., x_n]) or localmin(f, x, a, b)",
        "Points where f has a local minimum, over the reals or over [a, b].",
        "Arguments like argmin. Minima are relative to the domain, so bounds and points where f stops being \
         defined may be local minima. In R only: functions of one variable by the signs of the derivative between \
         the critical points, functions of several variables by the Hessian matrix (degenerate critical points are \
         classified only when they are global extrema of rational functions).",
        &[
            ex("localmin(x^3 - 3*x, x)", "x = 1"),
            ex("localmin(x^3 - 3*x, x, -3, 3)", "x = -3 \\ x = 1"),
            ex("localmin(cos(x), x)", "x = pi + 2 k pi \\ k in ZZ"),
            ex("localmin(x^3 - 3*x + y^2, x, y)", "x = 1, y = 0"),
        ],
    ),
    doc(
        Context::LOCALMAX,
        Statements,
        "localmax(f, [x_1, ..., x_n]) or localmax(f, x, a, b)",
        "Points where f has a local maximum, over the reals or over [a, b].",
        "Like localmin of -f.",
        &[
            ex("localmax(x^3 - 3*x, x)", "x = -1"),
            ex("localmax(x^3, x)", "\"no solution\""),
        ],
    ),
    doc(
        Context::EXTREMA,
        Statements,
        "extrema(f, [x_1, ..., x_n]) or extrema(f, x, a, b)",
        "Points where f has its global minimum and maximum, with the values of f there.",
        "Arguments like argmin. The minima found by argmin then the maxima found by argmax, labeled min and max, \
         with the value of f at each point.",
        &[
            ex(
                "extrema(x^2 - 2*x, x, 0, 3)",
                "\"min:\" x = 1, quad f = -1 \\ \"max:\" x = 3, quad f = 3",
            ),
            ex("extrema(x^3, x)", "\"no extremum\""),
        ],
    ),
    doc(
        Context::LOCALEXTREMA,
        Statements,
        "localextrema(f, [x_1, ..., x_n]) or localextrema(f, x, a, b)",
        "Points where f has a local minimum or maximum, with the values of f there.",
        "Arguments like argmin. The minima found by localmin then the maxima found by localmax, labeled min and \
         max, with the value of f at each point.",
        &[
            ex(
                "localextrema(x^3 - 3*x, x)",
                "\"min:\" x = 1, quad f = -2 \\ \"max:\" x = -1, quad f = 2",
            ),
            ex(
                "localextrema(x^2 + y^2, x, y)",
                "\"min:\" x = 0, y = 0, quad f = 0",
            ),
        ],
    ),
    doc(
        Context::SUBS,
        Algebra,
        "subs(f, x, a)",
        "Replaces the symbol x by a in f.",
        "In R, x is also replaced in exponents; in other sets, the substitution stays unevaluated when x is in an \
         exponent.",
        &[
            ex("subs(x^2 + y, x, y + 1)", "y + (y + 1)^2"),
            ex("subs(sin(x) + 2^x, x, 0)", "1"),
        ],
    ),
    doc(
        Context::NUMER,
        Algebra,
        "numer(f)",
        "Numerator of f written as a single fraction.",
        "",
        &[ex("numer(1/x + 1/y)", "x + y"), ex("numer(3/4)", "3")],
    ),
    doc(
        Context::DENOM,
        Algebra,
        "denom(f)",
        "Denominator of f written as a single fraction.",
        "",
        &[ex("denom(1/x + 1/y)", "x y"), ex("denom(3/4)", "4")],
    ),
    doc(
        Context::ROOTS,
        Algebra,
        "roots(p, [x])",
        "Roots of a polynomial, as a column repeated by multiplicity.",
        "x may be omitted when p has a single symbol. In M(R), the real roots found by solve, and in M(C) the \
         complex ones; unevaluated when there is none.",
        &[
            ex_in("M(R)", "roots(x^3 - x^2)", "mat(0; 0; 1)"),
            ex_in("M(R)", "roots(x^2 - 2)", "mat(sqrt(2); -sqrt(2))"),
            ex_in("M(C)", "roots(x^2 + 1)", "mat(-i; i)"),
        ],
    ),
    doc(
        Context::RESULTANT,
        Algebra,
        "resultant(p, q, [x])",
        "Resultant of two polynomials in x, the determinant of their Sylvester matrix.",
        "x may be omitted when p and q have a single symbol. It is zero exactly when p and q have a common root \
         (or both leading coefficients vanish). Evaluated when the degrees add up to at most 14.",
        &[
            ex("resultant(x^2 - 1, x - 2)", "3"),
            ex("resultant(x^2 + a, x - b, x)", "a + b^2"),
        ],
    ),
    doc(
        Context::DISCRIMINANT,
        Algebra,
        "discriminant(p, [x])",
        "Discriminant of a polynomial in x, zero exactly when p has a multiple root.",
        "x may be omitted when p has a single symbol. (-1)^(n (n - 1)/2) resultant(p, p')/a_n for a polynomial of \
         degree n with leading coefficient a_n, 1 for degree 1.",
        &[
            ex("discriminant(a*x^2 + b*x + c, x)", "b^2 - 4 a c"),
            ex("discriminant(x^3 - x)", "4"),
        ],
    ),
    doc(
        Context::ERFC,
        Special,
        "erfc(x)",
        "Complementary error function, 1 - erf(x).",
        "In R, rewritten as 1 - erf(x).",
        &[ex("erfc(0)", "1"), ex("lim(erfc(x), x, oo)", "0")],
    ),
    doc(
        Context::ROUND,
        Arithmetic,
        "round(x)",
        "Nearest integer to x, halves being rounded up.",
        "In R, rewritten as floor(x + 1/2).",
        &[
            ex("round(5/2)", "3"),
            ex("round(-7/4)", "-2"),
            ex("round(x)", "floor(x + 1/2)"),
        ],
    ),
    doc(
        Context::TRUNC,
        Arithmetic,
        "trunc(x)",
        "Integer part of x, rounded toward zero.",
        "In R, rewritten as sign(x) floor(|x|) unless x is a value.",
        &[ex("trunc(-7/4)", "-1"), ex("trunc(7/4)", "1")],
    ),
    doc(
        Context::ISPRIME,
        Arithmetic,
        "isprime(n)",
        "1 if the integer n is a prime number, 0 otherwise.",
        "In Z, R and Z/m (where n is read as an integer, then the result is reduced mod m). Exact below 3.3 10^24, a strong probable prime test with many bases above.",
        &[ex("isprime(97)", "1"), ex("isprime(91)", "0")],
    ),
    doc(
        Context::FACTORINT,
        Arithmetic,
        "factorint(n)",
        "Prime factorization of a non-zero integer or rational, as rows [p, e] for each factor p^e.",
        "In M and M(Z). A negative number has a first row [-1, 1], denominators have negative exponents, and 1 \
         is [1, 1]. Unevaluated when a factor is too large to be found.",
        &[
            ex_in("M(R)", "factorint(360)", "mat(2, 3; 3, 2; 5, 1)"),
            ex_in("M(R)", "factorint(-3/4)", "mat(-1, 1; 2, -2; 3, 1)"),
        ],
    ),
    doc(
        Context::ZEROS,
        Matrices,
        "zeros(n, [m])",
        "Zero matrix with n rows and m columns, square by default.",
        "",
        &[
            ex_in("M(R)", "zeros(2)", "mat(0, 0; 0, 0)"),
            ex_in("M(R)", "zeros(1, 3)", "mat(0, 0, 0)"),
        ],
    ),
    doc(
        Context::DIAG,
        Matrices,
        "diag(a_1, ..., a_n)",
        "Diagonal matrix with the entries a_1, ..., a_n.",
        "The entries may also be given as a single row or column.",
        &[
            ex_in("M(R)", "diag(1, 2)", "mat(1, 0; 0, 2)"),
            ex_in("M(R)", "diag([[a, b]])", "mat(a, 0; 0, b)"),
        ],
    ),
    doc(
        Context::SI,
        Special,
        "Si(x)",
        "Sine integral, the integral of sin(t)/t from 0 to x.",
        "Odd, with Si(oo) = pi/2. It is the antiderivative of sin(a x + b)/x.",
        &[
            ex("diff(Si(x), x)", "sin(x)/x"),
            ex("integrate(sin(x)/x, x, 0, oo)", "pi/2"),
        ],
    ),
    doc(
        Context::CI,
        Special,
        "Ci(x)",
        "Cosine integral, euler_gamma + ln x + the integral of (cos(t) - 1)/t from 0 to x, for x > 0.",
        "Ci(oo) = 0. It is the antiderivative of cos(a x + b)/x, written Ci(|a x|) when a x may be negative. In C, \
         Ci(-x) = Ci(x) + i pi for x > 0.",
        &[
            ex("diff(Ci(x), x)", "cos(x)/x"),
            ex("integrate(cos(2*x)/x, x)", "op(\"Ci\")(2 abs(x))"),
            ex(
                "integrate(cos(x)/x, x, -2, -1)",
                "op(\"Ci\")(1) - op(\"Ci\")(2)",
            ),
        ],
    ),
    doc(
        Context::EI,
        Special,
        "Ei(x)",
        "Exponential integral, euler_gamma + ln|x| + the integral of (e^t - 1)/t from 0 to x.",
        "Ei(-oo) = 0 and Ei(oo) = oo. It is the antiderivative of e^(a x + b)/x.",
        &[
            ex("diff(Ei(x), x)", "exp(x)/x"),
            ex("integrate(exp(-x)/x, x)", "op(\"Ei\")(-x)"),
        ],
    ),
    doc(
        Context::ARG,
        Complex,
        "arg(z)",
        "Argument of a complex number.",
        "The principal value, in (-pi, pi], from atan(im/re) and the signs of the parts; undefined at 0. Symbols \
         are assumed real, and the argument stays unevaluated when a sign is unknown.",
        &[
            ex_in("C", "arg(1 + i)", "pi/4"),
            ex_in("C", "arg(-1 - sqrt(3)*i)", "-(2 pi)/3"),
            ex("arg(-2)", "pi"),
        ],
    ),
    doc(
        Context::LITTLE_O,
        Calculus,
        "o(u)",
        "Little-o: a term negligible compared to u, the remainder of a series.",
        "Constant factors are absorbed, and products are moved inside: f o(u) = o(f u). It is left out when the \
         expression is drawn.",
        &[
            ex("series(cos(x), x, 0, 3)", "1 - x^2/2 + o(x^2)"),
            ex("3*x*o(x^2)", "o(x^3)"),
        ],
    ),
    doc(
        Context::ROOTOF,
        Algebra,
        "rootof(p, [x], k)",
        "The k-th real root of a polynomial with rational coefficients, by increasing order.",
        "x may be omitted when p has a single symbol. Roots of linear and quadratic factors are written with \
         radicals, the others stay rootof of their irreducible factor, which solve gives for polynomials without \
         radical roots. Powers of a root are reduced by its polynomial, and approx refines its isolating interval.",
        &[
            ex("rootof(x^3 - 2*x^2 - 2*x, 1)", "1 - sqrt(3)"),
            ex(
                "rootof(x^5 - x - 1, 1)^5",
                "op(\"rootof\")(-x + x^5 - 1, 1) + 1",
            ),
            ex("approx(rootof(x^5 - x - 1, 1))", "1.16730397826142"),
        ],
    ),
    doc(
        Context::BERNOULLI,
        Special,
        "bernoulli(n)",
        "The Bernoulli number B_n, the coefficient of t^n/n! in t/(e^t - 1).",
        "Exact values for natural numbers n <= 1000, B_1 being -1/2. They are the general terms of the whole \
         series of tan, cot, csc, tanh and t/(e^t - 1).",
        &[ex("bernoulli(10)", "5/66"), ex("bernoulli(1)", "-1/2")],
    ),
    doc(
        Context::EULER,
        Special,
        "euler(n)",
        "The Euler number E_n, the coefficient of t^n/n! in 1/cosh(t).",
        "Exact values for natural numbers n <= 1000, zero for odd n. They are the general terms of the whole \
         series of sec and 1/cosh.",
        &[ex("euler(10)", "-50521"), ex("euler(3)", "0")],
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
