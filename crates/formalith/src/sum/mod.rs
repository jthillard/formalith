//! Sums `sum(f, k, a, b)` and products `product(f, k, a, b)` over the integers `k` from `a` to `b`.
//!
//! Sums are computed with an antidifference `F`, `{$F(k + 1) - F(k) = f(k)$}`, as `{$F(b + 1) - F(a)$}`, the
//! first strategy which succeeds giving `F`:
//! - linearity: constant factors are taken out,
//! - polynomials in `k`, with Faulhaber's formula,
//! - geometric terms `{$r^k p(k)$}` for a polynomial `p`,
//! - hypergeometric terms (products of rational functions, powers `{$c^k$}`, factorials and binomial
//!   coefficients of linear arguments), with Gosper's algorithm (module `gosper`),
//! - rational functions with rational coefficients whose denominator has rational roots, as sums of polygamma
//!   functions `{$psi^((m))(k - r)$}`,
//! - sums term by term.
//!
//! Definite sums `{$sum_(k = a)^(s n + c) F(n, k)$}` of hypergeometric terms without antidifference, like
//! `{$sum_(k = 0)^n binom(n, k) = 2^n$}`, are found with Zeilberger's algorithm (module `zeilberger`).
//!
//! Infinite bounds are limits of the antidifference, with [`Term::limit`], so divergent sums give
//! [`SumError::Divergent`]. A few classic series without antidifference are also known: `{$zeta(s)$}` and
//! `{$e^x$}`. Products use an antiquotient `G`, `{$G(k + 1) / G(k) = f(k)$}`, made of powers and `{$Gamma$}`
//! functions of the linear factors of `f`. Sums and products with integer bounds and few terms are computed term
//! by term. Expressions without closed form stay unevaluated.
//!
//! ```
//! use formalith::{field::real::R, parse};
//!
//! assert_eq!(parse!("sum(k, k, 1, n)", R), parse!("n*(n + 1)/2", R));
//! assert_eq!(parse!("sum(1/2^k, k, 0, oo)", R), parse!("2", R));
//! assert_eq!(parse!("product(k, k, 1, n)", R), parse!("factorial(n)", R));
//! ```

pub(crate) mod field;
mod gosper;
mod polynomial;
mod product;
mod taylor;
mod zeilberger;

pub(crate) use taylor::{
    derive_held_sum, has_held_sum, held_sum_at, held_sum_between, integrate_held_sum,
};

use std::{cmp::Ordering, error::Error, fmt};

use malachite::Rational;

use crate::{
    context::{
        Context, Symbol,
        assumptions::{Assumption, Assumptions, AssumptionsGuard},
    },
    field::real::R,
    field::real::expr::{
        Expr, Real, constant_sign, depends, fun, has_special_constant, infinity_sign, map_tree,
        one, size, subs, value, variable, zero,
    },
    limit::{Direction, LimitError},
    term::{Expand, Fun, Normalize, Term},
};

/// Maximum number of terms of a sum or product computed term by term.
pub(crate) const MAX_TERMS: u64 = 1000;
/// Number of terms below which a sum or product with integer bounds is computed term by term before looking
/// for a closed form.
const DIRECT_TERMS: u64 = 100;
/// Largest `m` for which `{$binom(u, m)$}` is written as a polynomial in `u` in sums.
const MAX_BINOMIAL: u64 = 20;

/// The reason why a sum or a product can't be evaluated.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SumError {
    /// No closed form was found.
    Unsupported,
    /// The infinite sum or product diverges to `{$+oo$}` (`Greater`) or `{$-oo$}` (`Less`).
    Divergent(Ordering),
    /// The infinite sum or product doesn't converge, like `{$sum_(k >= 0) (-1)^k$}`.
    Undefined,
}

impl fmt::Display for SumError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Self::Unsupported => "the sum can't be computed",
            Self::Divergent(_) => "the sum diverges",
            Self::Undefined => "the sum doesn't converge",
        })
    }
}

impl Error for SumError {}

/// The result of a sum or a product.
pub type SumResult<T> = Result<T, SumError>;

impl Term<Real> {
    /// The sum of the expression for the integers `k` from `a` to `b`, which may be `{$-oo$}` and `{$oo$}`.
    ///
    /// # Errors
    /// [`SumError::Unsupported`] when no closed form is found, [`SumError::Divergent`] and
    /// [`SumError::Undefined`] when an infinite sum doesn't converge.
    ///
    /// ```
    /// use std::cmp::Ordering;
    /// use formalith::{field::real::R, parse, sum::SumError, symbol};
    ///
    /// let (k, n) = (symbol!("k"), parse!("n", R));
    /// assert_eq!(parse!("2^k", R).sum(k, &parse!("0", R), &n), Ok(parse!("2^(n+1) - 1", R)));
    /// assert_eq!(
    ///     parse!("1/k", R).sum(k, &parse!("1", R), &parse!("oo", R)),
    ///     Err(SumError::Divergent(Ordering::Greater))
    /// );
    /// ```
    pub fn sum(&self, k: Symbol, a: &Self, b: &Self) -> SumResult<Self> {
        profile_scope!("sum");
        check_bounds(self, k, a, b)?;
        if let Some(count) = count(a, b) {
            if count == 0 {
                return Ok(zero());
            }
            if count <= DIRECT_TERMS {
                return Ok(direct(self, k, a, count, zero(), |res, t| res + t));
            }
        }
        if !depends(self, k) {
            return match (infinity_sign(a), infinity_sign(b)) {
                (None, None) => Ok(tidy(&(self * &(b - a + one())))),
                _ if self.is_zero() => Ok(zero()),
                _ => Err(constant_sign(self).map_or(SumError::Unsupported, SumError::Divergent)),
            };
        }
        let _guard = integer_index(k);
        let res = antidifference(self, k).map_or(Err(SumError::Unsupported), |antidifference| {
            difference(&antidifference, k, a, b)
        });
        match (res, count(a, b)) {
            (Err(SumError::Unsupported), _) if infinity_sign(b) == Some(Ordering::Greater) => {
                polynomial::known_series(self, k, a)
                    .map(|res| tidy(&res))
                    .ok_or(SumError::Unsupported)
            }
            (Err(SumError::Unsupported), Some(count)) if count <= MAX_TERMS => {
                Ok(direct(self, k, a, count, zero(), |res, t| res + t))
            }
            (Err(SumError::Unsupported), None) => zeilberger::definite(self, k, a, b)
                .map(|res| tidy(&res))
                .ok_or(SumError::Unsupported),
            (res, _) => res.map(|res| tidy(&res)),
        }
    }

    /// The product of the expression for the integers `k` from `a` to `b`, which may be `{$oo$}`.
    ///
    /// # Errors
    /// [`SumError::Unsupported`] when no closed form is found, [`SumError::Divergent`] and
    /// [`SumError::Undefined`] when an infinite product doesn't converge.
    ///
    /// ```
    /// use formalith::{field::real::R, parse, symbol};
    ///
    /// let k = symbol!("k");
    /// let product = parse!("(k + 1)/k", R).product(k, &parse!("1", R), &parse!("n", R));
    /// assert_eq!(product, Ok(parse!("n + 1", R)));
    /// ```
    pub fn product(&self, k: Symbol, a: &Self, b: &Self) -> SumResult<Self> {
        profile_scope!("product");
        check_bounds(self, k, a, b)?;
        if let Some(count) = count(a, b) {
            if count == 0 {
                return Ok(one());
            }
            if count <= DIRECT_TERMS {
                return Ok(direct(self, k, a, count, one(), |res, t| res * t));
            }
        }
        if infinity_sign(a).is_some() {
            return Err(SumError::Unsupported);
        }
        if !depends(self, k) && infinity_sign(b).is_none() {
            return Ok(self.pow(&(b - a + one())));
        }
        let _guard = integer_index(k);
        let res = product::antiquotient(self, k)
            .map_or(Err(SumError::Unsupported), |antiquotient| {
                product::quotient(&antiquotient, k, a, b)
            });
        match (res, count(a, b)) {
            (Err(SumError::Unsupported), Some(count)) if count <= MAX_TERMS => {
                Ok(direct(self, k, a, count, one(), |res, t| res * t))
            }
            (res, _) => res.map(|res| tidy(&res)),
        }
    }
}

/// Reject bounds depending on `k`, `{$a = oo$}`, `{$b = -oo$}`, and terms with `{$oo$}`.
fn check_bounds(f: &Expr, k: Symbol, a: &Expr, b: &Expr) -> SumResult<()> {
    if has_special_constant(f)
        || depends(a, k)
        || depends(b, k)
        || infinity_sign(a) == Some(Ordering::Greater)
        || infinity_sign(b) == Some(Ordering::Less)
        || (infinity_sign(a).is_none() && has_special_constant(a))
        || (infinity_sign(b).is_none() && has_special_constant(b))
    {
        return Err(SumError::Unsupported);
    }
    Ok(())
}

/// The number of integers from `a` to `b`, if they are integer values.
fn count(a: &Expr, b: &Expr) -> Option<u64> {
    let (Term::Value(a), Term::Value(b)) = (a, b) else {
        return None;
    };
    let (a, b) = (
        malachite::Integer::try_from(&a.value).ok()?,
        malachite::Integer::try_from(&b.value).ok()?,
    );
    if b < a {
        return Some(0);
    }
    u64::try_from(&(b - a + malachite::Integer::from(1))).ok()
}

/// The terms `{$f(a), ..., f(a + count - 1)$}` combined with `op`, from `init`.
fn direct(
    f: &Expr,
    k: Symbol,
    a: &Expr,
    count: u64,
    init: Expr,
    op: impl Fn(Expr, Expr) -> Expr,
) -> Expr {
    (0..count).fold(init, |res, i| {
        op(res, subs(f, k, &(a + &value(Rational::from(i)))))
    })
}

/// Assume that `k` is an integer until the guard is dropped.
fn integer_index(k: Symbol) -> Option<AssumptionsGuard> {
    let mut assumptions = Assumptions::current();
    assumptions.assume(k, Assumption::INTEGER).ok()?;
    Some(assumptions.enter())
}

/// An antidifference of `f` with respect to `k`.
pub(crate) fn antidifference(f: &Expr, k: Symbol) -> Option<Expr> {
    if !depends(f, k) {
        return Some(f * &variable(k));
    }
    if let Term::Mul(mul) = f {
        let constant = mul
            .iter()
            .filter(|t| !depends(t, k))
            .fold(value(mul.coefficient.clone()), |res, t| res * t);
        if constant != one() {
            let rest = mul
                .iter()
                .filter(|t| depends(t, k))
                .fold(one(), |res, t| res * t);
            return antidifference(&rest, k).map(|res| constant * res);
        }
    }
    if let Some(f) = falling_binomials(f, k) {
        return antidifference(&f, k);
    }
    polynomial::polynomial(f, k)
        .or_else(|| polynomial::geometric(f, k))
        .or_else(|| gosper::antidifference(f, k))
        .or_else(|| polynomial::rational(f, k))
        .or_else(|| match f {
            Term::Add(add) => add
                .iter()
                .try_fold(zero(), |res, t| Some(res + antidifference(t, k)?)),
            _ => None,
        })
}

/// `f` with the binomial coefficients `{$binom(u, m)$}` depending on `k`, for a small natural `m`, written as
/// polynomials `{$u (u - 1) ... (u - m + 1) / m!$}`, or `None` if there is none.
fn falling_binomials(f: &Expr, k: Symbol) -> Option<Expr> {
    let found = std::cell::Cell::new(false);
    let res = map_tree(f, &|t| {
        let Term::Fun(fun) = t else {
            return None;
        };
        let (Context::BINOMIAL, Some([u, Term::Value(m)])) =
            (fun.get_ident(), fun.get_args::<Real>().map(Vec::as_slice))
        else {
            return None;
        };
        let m = u64::try_from(&m.value)
            .ok()
            .filter(|m| *m <= MAX_BINOMIAL)?;
        if !depends(u, k) {
            return None;
        }
        found.set(true);
        Some((0..m).fold(one(), |res, i| {
            res * (u - &value(Rational::from(i))) / value(Rational::from(i + 1))
        }))
    });
    found.get().then_some(res)
}

/// `{$F(b + 1) - F(a)$}`, with limits at infinite bounds.
fn difference(antidifference: &Expr, k: Symbol, a: &Expr, b: &Expr) -> SumResult<Expr> {
    let upper = match infinity_sign(b) {
        Some(_) => limit(antidifference, k, b)?,
        None => at(antidifference, k, &(b + &one()))?,
    };
    let lower = match infinity_sign(a) {
        Some(_) => limit(antidifference, k, a)?,
        None => at(antidifference, k, a)?,
    };
    if let Some(sign) = infinity_sign(&upper) {
        return if infinity_sign(&lower).is_some() {
            Err(SumError::Unsupported)
        } else {
            Err(SumError::Divergent(sign))
        };
    }
    if let Some(sign) = infinity_sign(&lower) {
        return Err(SumError::Divergent(sign.reverse()));
    }
    let res = upper - lower;
    if res == variable(Context::UNDEFINED) {
        return Err(SumError::Undefined);
    }
    Ok(res)
}

/// The value of `f` at `{$k = a$}`, or its limit when it is a removable singularity, like `{$k / k$}` at 0.
pub(super) fn at(f: &Expr, k: Symbol, a: &Expr) -> SumResult<Expr> {
    let res = shifted_binomials(&subs(f, k, a));
    if has_special_constant(&res) {
        return limit(f, k, a);
    }
    Ok(res)
}

/// `{$binom(u, v)$}` with `{$u - v = d$}` an integer value written `{$binom(u, d)$}`, or 0 for `{$d < 0$}` (`{$1 / Gamma$}`
/// vanishing at non-positive integers): the terms at symbolic bounds, like `{$binom(n, n) = 1$}`.
fn shifted_binomials(term: &Expr) -> Expr {
    map_tree(term, &|t| {
        let Term::Fun(f) = t else { return None };
        let (Context::BINOMIAL, Some([u, v])) =
            (f.get_ident(), f.get_args::<Real>().map(Vec::as_slice))
        else {
            return None;
        };
        let Term::Value(d) = (u - v).expand() else {
            return None;
        };
        if d.value.denominator_ref() != &1u32 || matches!(v, Term::Value(_)) {
            return None;
        }
        Some(if d.value < 0u32 {
            zero()
        } else {
            Term::Fun(Box::new(Fun::new(
                Context::BINOMIAL,
                vec![u.clone(), Term::Value(d)],
                R,
            )))
            .normalize()
        })
    })
}

/// The limit of `f` when the integer `k` tends to `point`, an infinite point or a removable singularity.
pub(super) fn limit(f: &Expr, k: Symbol, point: &Expr) -> SumResult<Expr> {
    // Limits are taken over the reals, with a variable `x` not assumed to be an integer, and
    // `{$c^g = |c|^g cos(pi g)$}` for a negative `c`, `g` being an integer
    let x = Symbol::new("@k".to_string());
    let f = map_tree(&subs(f, k, &variable(x)), &|t| match t {
        Term::Pow(pow)
            if depends(&pow.exponant, x)
                && !depends(&pow.base, x)
                && constant_sign(&pow.base) == Some(Ordering::Less) =>
        {
            let g = (**pow.exponant).clone();
            Some((-&*pow.base).pow(&g) * fun(Context::COS, variable(Context::PI) * g))
        }
        _ => None,
    });
    match f.limit(x, point, Direction::Both) {
        Ok(res) if res == variable(Context::UNDEFINED) => Err(SumError::Undefined),
        Ok(res)
            if crate::field::real::expr::has_special_constant(&res)
                && infinity_sign(&res).is_none() =>
        {
            Err(SumError::Unsupported)
        }
        Ok(res) => Ok(res),
        Err(LimitError::Undefined) => Err(SumError::Undefined),
        Err(_) => Err(SumError::Unsupported),
    }
}

/// The smallest of the result, its expansion, and its simplification and factorization when it is a rational
/// function (simplifications of other terms may not terminate).
fn tidy(res: &Expr) -> Expr {
    let res = &product::combine_factorials(res);
    let expanded = res.expand();
    let mut candidates = vec![];
    if is_rational_function(&expanded) {
        candidates.push(res.simplify());
        candidates.push(expanded.factor());
    }
    candidates.push(expanded);
    candidates.into_iter().fold(res.clone(), |best, candidate| {
        if size(&candidate) < size(&best) {
            candidate
        } else {
            best
        }
    })
}

/// Whether the term is a rational function of its symbols with rational coefficients.
pub(crate) fn is_rational_function(term: &Expr) -> bool {
    match term {
        Term::Value(_) => true,
        Term::Symbol(s) => !Context::is_builtin_constant(s.symbol),
        Term::Pow(pow) => {
            is_rational_function(&pow.base)
                && matches!(&**pow.exponant, Term::Value(e) if e.value.denominator_ref() == &1u32)
        }
        Term::Add(add) => add.iter().all(is_rational_function),
        Term::Mul(mul) => mul.iter().all(is_rational_function),
        Term::Fun(_) => false,
    }
}
