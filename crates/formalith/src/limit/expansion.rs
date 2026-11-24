//! Series expansions `series(f, x, a, n)`, with the series of the Gruntz algorithm.
//!
//! `x` is replaced by `{$a + w$}` (`{$a - w$}` from the left, `{$1/w$}` at `{$oo$}`), and the series of `f` in
//! `{$w -> 0^+$}` is computed, then `w` is replaced back by `{$x - a$}`. Exponents may be negative or fractional,
//! and coefficients may contain `{$ln(x - a)$}`.

use crate::field::real::expr::{
    Expr, Real, depends, fun, infinity_sign, one, value, variable, zero,
};
use malachite::{Rational, base::num::arithmetic::traits::Parity};

use crate::{
    context::{Context, Symbol},
    term::Term,
};

use super::{Direction, LimitError, LimitResult, gruntz::Gruntz, prepare, series};

/// The terms `{$c_i w^(e_i)$}` of a series in `w`, which stands for an expression in `x`.
pub struct SeriesTerms {
    /// Pairs `{$(e_i, c_i)$}` with rational exponents, sorted by increasing exponent, without zero coefficients.
    pub(crate) terms: Vec<(Rational, Expr)>,
    /// Whether the terms are the whole series, without remainder.
    pub(crate) exact: bool,
    /// The expression `w` in `x`: `{$x - a$}`, `{$a - x$}` or `{$plus.minus 1/x$}`.
    pub(crate) w: Expr,
}

impl Term<Real> {
    /// Series of the expression when `x` tends to `point`, from the side given by `direction`, up to
    /// `{$O((x - a)^n)$}` with `n` being `order` (`{$O(x^(-n))$}` at `{$plus.minus oo$}`). The remainder isn't
    /// included.
    ///
    /// # Errors
    /// [`LimitError::Unsupported`] or [`LimitError::Unknown`] when the series can't be computed, like
    /// `{$exp(1/x)$}` at 0, and [`LimitError::Undefined`] when both sides have different series, like `{$|x|$}`
    /// at 0.
    ///
    /// ```
    /// use formalith::{field::real::R, limit::Direction, parse, symbol};
    ///
    /// let x = symbol!("x");
    /// let series = |f: &str, n: i64| parse!(f, R).series(x, &parse!("0", R), &n.into(), Direction::Both);
    /// assert_eq!(series("exp(x)", 4), Ok(parse!("1 + x + x^2/2 + x^3/6", R)));
    /// assert_eq!(series("sin(x)", 6), Ok(parse!("x - x^3/6 + x^5/120", R)));
    /// assert_eq!(series("1/sin(x)", 2), Ok(parse!("1/x + x/6", R)));
    /// ```
    pub fn series(
        &self,
        x: Symbol,
        point: &Self,
        order: &Rational,
        direction: Direction,
    ) -> LimitResult<Self> {
        profile_scope!("series");
        let (f, infinite) = prepare(self, x, point, direction)?;
        if let Some(sign) = infinite {
            // `{$x = s/w$}`, so `{$w = s/x$}` and `{$ln w = -ln(s x)$}`
            let sign = value(Rational::from(sign as i64));
            let ln_back = -fun(Context::LN, &sign * &variable(x));
            return side_series(
                &f,
                x,
                order,
                |w| &sign / w,
                &(&sign / &variable(x)),
                &ln_back,
            );
        }
        // `{$x = a + s w$}`, so `{$w = s (x - a)$}`
        let side = |sign: i64| {
            let sign = value(Rational::from(sign));
            let w = &sign * &(variable(x) - point.clone());
            let ln_back = fun(Context::LN, w.clone());
            side_series(&f, x, order, |w| point + &(&sign * w), &w, &ln_back)
        };
        match direction {
            Direction::Right => side(1),
            Direction::Left => side(-1),
            Direction::Both => {
                let (right, left) = (side(1)?, side(-1)?);
                if right == left || (&right - &left).simplify().is_zero() {
                    Ok(right)
                } else {
                    Err(LimitError::Undefined)
                }
            }
        }
    }
}

/// The terms of the series of `f` when `x` tends to `point` up to `{$O(w^n)$}`, `n` being `order`, with `w` being
/// `{$x - a$}` (`{$a - x$}` from the left, `{$plus.minus 1/x$}` at `{$plus.minus oo$}`). Exponents must be rational
/// and coefficients free of `{$ln w$}`.
///
/// # Errors
/// Like [`Term::series`], [`LimitError::Unsupported`] for irrational exponents and logarithms.
pub fn series_terms(
    f: &Expr,
    x: Symbol,
    point: &Expr,
    order: &Rational,
    direction: Direction,
) -> LimitResult<SeriesTerms> {
    let (f, infinite) = prepare(f, x, point, direction)?;
    if let Some(sign) = infinite {
        let sign = value(Rational::from(sign as i64));
        return side_terms(&f, x, order, |w| &sign / w, &sign / &variable(x));
    }
    let side = |sign: i64| {
        let sign = value(Rational::from(sign));
        let w = &sign * &(variable(x) - point.clone());
        side_terms(&f, x, order, |w| point + &(&sign * w), w)
    };
    match direction {
        Direction::Right => side(1),
        Direction::Left => side(-1),
        Direction::Both => {
            // `{$sum c_i (x - a)^(e_i) = sum c'_i (a - x)^(e_i)$}` when the exponents are integers and
            // `{$c'_i = (-1)^(e_i) c_i$}`
            let (right, left) = (side(1)?, side(-1)?);
            let same = right.exact == left.exact
                && right.terms.len() == left.terms.len()
                && right
                    .terms
                    .iter()
                    .zip(&left.terms)
                    .all(|((er, cr), (el, cl))| {
                        er == el && er.denominator_ref() == &1u32 && {
                            let sign = if er.numerator_ref().even() {
                                one()
                            } else {
                                -one()
                            };
                            cl == &(&sign * cr) || (cl - &(&sign * cr)).simplify().is_zero()
                        }
                    });
            if same {
                Ok(right)
            } else {
                Err(LimitError::Undefined)
            }
        }
    }
}

/// The terms of the series of `f` with `x` replaced by `at(w)` for `{$w -> 0^+$}`, up to `{$O(w^n)$}`.
fn side_terms(
    f: &Expr,
    x: Symbol,
    order: &Rational,
    at: impl Fn(&Expr) -> Expr,
    back: Expr,
) -> LimitResult<SeriesTerms> {
    let mut gruntz = Gruntz::new(x);
    let logw = Symbol::new("@l");
    let f = f
        .substitute(x, &at(&variable(gruntz.w)))
        .ok_or(LimitError::Unsupported)?;
    let (terms, exact) = series::expand_exact(&mut gruntz, &f, &variable(logw), order)?;
    let terms = terms
        .into_iter()
        .map(|(exponant, coefficient)| match exponant {
            Term::Value(e) if !depends(&coefficient, logw) => Ok((e.value, coefficient)),
            _ => Err(LimitError::Unsupported),
        })
        .collect::<LimitResult<_>>()?;
    Ok(SeriesTerms {
        terms,
        exact,
        w: back,
    })
}

/// The remainder `{$o((x - a)^(n - 1))$}` of a series at `point` (`{$o(x^(1 - n))$}` at `{$plus.minus oo$}`), `n`
/// being `order`, added to the terms by the builtin `series`.
pub fn remainder(x: Symbol, point: &Expr, order: &Rational) -> Expr {
    let exponant = value(order - Rational::from(1));
    let bound = if infinity_sign(point).is_some() {
        variable(x).pow(&-exponant)
    } else {
        (variable(x) - point.clone()).pow(&exponant)
    };
    fun(Context::LITTLE_O, bound)
}

/// The series of `f` with `x` replaced by `at(w)` for `{$w -> 0^+$}`, up to `{$O(w^n)$}`, with `w` replaced back
/// by `back` and `{$ln w$}` by `ln_back`.
fn side_series(
    f: &Expr,
    x: Symbol,
    order: &Rational,
    at: impl Fn(&Expr) -> Expr,
    back: &Expr,
    ln_back: &Expr,
) -> LimitResult<Expr> {
    let mut gruntz = Gruntz::new(x);
    // Not a valid identifier, so it can't conflict with a symbol of the expression
    let logw = Symbol::new("@l");
    let f = f
        .substitute(x, &at(&variable(gruntz.w)))
        .ok_or(LimitError::Unsupported)?;
    let terms = series::expand(&mut gruntz, &f, &variable(logw), order)?;
    terms
        .into_iter()
        .try_fold(zero(), |res, (exponant, coefficient)| {
            let coefficient = coefficient
                .substitute(logw, ln_back)
                .ok_or(LimitError::Unsupported)?;
            Ok(res + coefficient * back.pow(&exponant))
        })
}
