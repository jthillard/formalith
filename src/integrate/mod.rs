//! Integrals of real expressions, `integrate(f, x)` and `integrate(f, x, a, b)`.
//!
//! Antiderivatives are computed by a recursive search, the first strategy which succeeds being used:
//! - linearity: sums are integrated term by term, and constant factors are taken out,
//! - rational functions of `x` with rational coefficients are always integrated, see [`rational`]: the
//!   Hermite reduction gives the rational part, and the logarithmic part is written with `ln` and `atan`, as long
//!   as the roots of the irreducible factors of the denominator can be expressed with radicals,
//! - a table of elementary functions of a linear argument, square roots of quadratic polynomials, products
//!   `{$e^u sin v$}`, and Gaussian integrals `{$integral p e^q$}` (polynomial `p`, quadratic `q`) with
//!   `{$"erf"$}` and `{$"erfi"$}`,
//! - products of powers of `sin` and `cos` of a same argument, substituting `cos`, `sin` or `tan`, or reducing the
//!   powers,
//! - substitutions `{$u = g(x)$}` when `{$f / g'$}` is an expression of `u` (derivative-divides),
//! - integration by parts, of logarithms and inverse functions, or of polynomials times functions that can be
//!   integrated,
//! - rewrites: hyperbolic functions as exponentials, products of trigonometric functions as sums, and the
//!   substitution `{$t = tan(x / 2)$}` for rational functions of `sin` and `cos`,
//! - the Risch algorithm for towers of exponentials and logarithms over `{$QQ(x)$}` (module `risch`), which also
//!   proves that integrals like `{$integral e^x / x dif x$}` aren't elementary
//!   ([`IntegrateError::NonElementary`]).
//!
//! Logarithms of expressions that may be negative are written `{$ln|u|$}`. Integrals which aren't found stay
//! unevaluated: unless the error is [`IntegrateError::NonElementary`], this is not a proof that there is no
//! elementary antiderivative.
//!
//! Definite integrals evaluate the antiderivative at the bounds with limits, so bounds may be `{$plus.minus oo$}`,
//! after splitting the interval at the points where the integrand or the antiderivative is singular (poles, and
//! `tan` of the substitution `{$t = tan(x / 2)$}`). Parts of the integrand constant on the interval are replaced by
//! their value, and symmetric intervals use `{$f(x) + f(-x)$}` when it is simpler. `approx` evaluates definite integrals numerically when no
//! antiderivative is found.
//!
//! ```
//! use formalith::{field::real::R, parse};
//!
//! assert_eq!(parse!("integrate(x^2, x)", R), parse!("x^3/3", R));
//! assert_eq!(parse!("integrate(1/(x^2+1), x)", R), parse!("atan(x)", R));
//! assert_eq!(parse!("integrate(exp(-x), x, 0, oo)", R), parse!("1", R));
//! ```

mod definite;
mod parts;
pub(crate) mod poly;
pub(crate) mod rational;
mod risch;
mod substitution;
mod table;
mod trig;

use std::{cmp::Ordering, collections::HashMap, error::Error, fmt};

use malachite::Rational;

use crate::{
    context::{Context, Symbol, assumptions::SignSet},
    field::real::{
        R,
        expr::{
            Expr, Real, constant_sign, depends, fun, has_special_constant, map_tree, one, unary,
            value, variable, zero,
        },
        sign::{SignMode, sign_set},
    },
    term::{Expand, Mul, Normalize, Term},
};

use poly::Poly;

/// Maximum depth of the recursive search of an antiderivative.
const MAX_DEPTH: usize = 7;

/// The reason why an integral can't be evaluated.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum IntegrateError {
    /// No antiderivative was found, or the definite integral can't be evaluated.
    Unsupported,
    /// The definite integral diverges to `{$+oo$}` (`Greater`) or `{$-oo$}` (`Less`).
    Divergent(Ordering),
    /// The definite integral doesn't exist, like `{$integral_(-1)^1 1/x dif x$}`.
    Undefined,
    /// The integrand is proved to have no elementary antiderivative, like `{$e^(x^2)$}`, by the Risch algorithm.
    NonElementary,
}

impl fmt::Display for IntegrateError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Unsupported => f.write_str("the integral can't be computed"),
            Self::Divergent(_) => f.write_str("the integral diverges"),
            Self::Undefined => f.write_str("the integral doesn't exist"),
            Self::NonElementary => f.write_str("the integral has no elementary antiderivative"),
        }
    }
}

impl Error for IntegrateError {}

/// The result of an integration.
pub type IntegrateResult<T> = Result<T, IntegrateError>;

impl Term<Real> {
    /// An antiderivative of the expression with respect to `x`.
    ///
    /// # Errors
    /// [`IntegrateError::NonElementary`] when the antiderivative is proved not to be elementary,
    /// [`IntegrateError::Unsupported`] when no antiderivative is found otherwise.
    ///
    /// ```
    /// use formalith::{field::real::R, integrate::IntegrateError, parse, symbol};
    ///
    /// let x = symbol!("x");
    /// assert_eq!(parse!("cos(x)", R).integrate(x), Ok(parse!("sin(x)", R)));
    /// assert_eq!(parse!("x*exp(x)", R).integrate(x), Ok(parse!("x*exp(x) - exp(x)", R)));
    /// assert_eq!(parse!("exp(x)/x", R).integrate(x), Err(IntegrateError::NonElementary));
    /// ```
    pub fn integrate(&self, x: Symbol) -> IntegrateResult<Self> {
        if has_special_constant(self) {
            return Err(IntegrateError::Unsupported);
        }
        let mut integrator = Integrator::default();
        if let Some(res) = integrator.integrate(self, x) {
            return Ok(res);
        }
        match integrator.risch(self, x) {
            Ok(res) => Ok(res),
            Err(risch::RischError::NonElementary) => Err(IntegrateError::NonElementary),
            Err(risch::RischError::Unsupported) => Err(IntegrateError::Unsupported),
        }
    }

    /// The integral of the expression with respect to `x` from `a` to `b`, which may be infinite.
    ///
    /// # Errors
    /// [`IntegrateError::Unsupported`] when no antiderivative is found or the singularities of the integrand
    /// can't be located, [`IntegrateError::Divergent`] and [`IntegrateError::Undefined`] when the integral
    /// diverges.
    ///
    /// ```
    /// use std::cmp::Ordering;
    /// use formalith::{field::real::R, integrate::IntegrateError, parse, symbol};
    ///
    /// let x = symbol!("x");
    /// let integral = |f: &str, a: &str, b: &str| parse!(f, R).integrate_definite(x, &parse!(a, R), &parse!(b, R));
    /// assert_eq!(integral("1/x^2", "1", "oo"), Ok(parse!("1", R)));
    /// assert_eq!(integral("1/x^2", "-1", "1"), Err(IntegrateError::Divergent(Ordering::Greater)));
    /// assert_eq!(integral("1/x", "-1", "1"), Err(IntegrateError::Undefined));
    /// ```
    pub fn integrate_definite(&self, x: Symbol, a: &Self, b: &Self) -> IntegrateResult<Self> {
        definite::integrate(self, x, a, b)
    }
}

/// The recursive search of antiderivatives, caching the results.
#[derive(Default)]
struct Integrator {
    depth: usize,
    cache: HashMap<(Symbol, Expr), Option<Expr>>,
    risch_cache: HashMap<(Symbol, Expr), risch::RischResult<Expr>>,
}

impl Integrator {
    /// An antiderivative of `f` with respect to `x`.
    fn integrate(&mut self, f: &Expr, x: Symbol) -> Option<Expr> {
        if !depends(f, x) {
            return Some(f * &variable(x));
        }
        let key = (x, f.clone());
        if let Some(res) = self.cache.get(&key) {
            return res.clone();
        }
        if self.depth >= MAX_DEPTH {
            return None;
        }
        self.depth += 1;
        let res = self.integrate_uncached(f, x);
        self.depth -= 1;
        self.cache.insert(key, res.clone());
        res
    }

    fn integrate_uncached(&mut self, f: &Expr, x: Symbol) -> Option<Expr> {
        if let Some((num, den)) = poly::rational_function(f, x) {
            return rational::integrate(&num, &den, x);
        }
        if let Term::Add(add) = f
            && let Some(res) = add
                .iter()
                .try_fold(zero(), |res, term| Some(res + self.integrate(term, x)?))
        {
            return Some(res);
        }
        let (constant, g) = split_constant(f, x);
        if !constant.is_one() {
            return Some(constant * self.integrate(&g, x)?);
        }
        let strategies: [fn(&mut Self, &Expr, Symbol) -> Option<Expr>; 5] = [
            table::integrate,
            trig::integrate_powers,
            substitution::integrate,
            parts::integrate,
            trig::integrate_rewritten,
        ];
        for strategy in strategies {
            if let Some(res) = strategy(self, f, x) {
                return Some(res);
            }
        }
        match self.risch(f, x) {
            Ok(res) => return Some(res),
            Err(risch::RischError::NonElementary) => return None,
            Err(risch::RischError::Unsupported) => {}
        }
        let expanded = f.expand();
        if expanded != *f {
            return self.integrate(&expanded, x);
        }
        None
    }

    /// The Risch algorithm on `f`, cached.
    fn risch(&mut self, f: &Expr, x: Symbol) -> risch::RischResult<Expr> {
        let key = (x, f.clone());
        if let Some(res) = self.risch_cache.get(&key) {
            return res.clone();
        }
        let res = risch::integrate(f, x);
        self.risch_cache.insert(key, res.clone());
        res
    }

    /// A fresh symbol for a substitution, distinct for each depth of the search. Not a valid identifier, so it
    /// can't conflict with a symbol of the expression.
    fn fresh_symbol(&self) -> Symbol {
        Symbol::new(format!("@i{}", self.depth))
    }
}

/// `f` as `{$c g$}`, the factor `c` not depending on `x`.
fn split_constant(f: &Expr, x: Symbol) -> (Expr, Expr) {
    match f {
        Term::Mul(mul) => {
            let constant = mul
                .iter()
                .filter(|factor| !depends(factor, x))
                .fold(value(mul.coefficient.clone()), |res, factor| res * factor);
            let rest = Term::Mul(Mul::new(
                Rational::from(1),
                mul.iter()
                    .filter(|factor| depends(factor, x))
                    .cloned()
                    .collect(),
                R,
            ))
            .normalize();
            (constant, rest)
        }
        _ => (one(), f.clone()),
    }
}

/// `{$a = u'$}` if `u` is a linear expression `{$a x + b$}` of `x`.
fn linear(u: &Expr, x: Symbol) -> Option<Expr> {
    let a = u.derivative(x);
    (!a.is_zero() && !depends(&a, x)).then_some(a)
}

/// The factors of a product, or the term itself.
fn factors(term: &Expr) -> Vec<Expr> {
    match term {
        Term::Mul(mul) => {
            let mut factors: Vec<_> = mul.iter().cloned().collect();
            if mul.coefficient != 1 {
                factors.push(value(mul.coefficient.clone()));
            }
            factors
        }
        _ => vec![term.clone()],
    }
}

/// Replace the symbol `x` by `with`, even in exponents.
fn replace_symbol(term: &Expr, x: Symbol, with: &Expr) -> Expr {
    map_tree(term, &|t| match t {
        Term::Symbol(s) if s.symbol == x => Some(with.clone()),
        _ if !depends(t, x) => Some(t.clone()),
        _ => None,
    })
}

/// `{$ln|u|$}`, or `{$ln u$}` when `u` is positive for every `x`.
fn ln_abs(u: &Expr, x: Symbol) -> Expr {
    if is_positive(u, x) {
        fun(Context::LN, u.clone())
    } else {
        fun(Context::LN, fun(Context::ABS, u.clone()))
    }
}

/// Whether `u` is positive for every `x`, which is checked on constants, exponentials, and polynomials of degree
/// two or with only even powers and non-negative coefficients.
fn is_positive(u: &Expr, x: Symbol) -> bool {
    if !depends(u, x) {
        return constant_sign(u) == Some(Ordering::Greater);
    }
    // From its structure, `x` having any sign
    if sign_set(u, SignMode::STRUCTURAL) == SignSet::POSITIVE {
        return true;
    }
    if matches!(unary(u), Some((Context::EXP | Context::COSH, _))) {
        return true;
    }
    let Some(p) = Poly::from_term(u, x) else {
        return false;
    };
    let c = p.coefficients();
    if p.degree() == 2 {
        return c[2] > 0 && &c[1] * &c[1] < Rational::from(4) * &c[2] * &c[0];
    }
    c[0] > 0
        && c.iter()
            .enumerate()
            .all(|(i, c)| if i % 2 == 1 { *c == 0 } else { *c >= 0 })
}
