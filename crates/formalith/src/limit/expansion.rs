//! Series expansions `series(f, x, a, n)`, with the series of the Gruntz algorithm.
//!
//! `x` is replaced by `{$a + w$}` (`{$a - w$}` from the left, `{$1/w$}` at `{$oo$}`), and the series of `f` in
//! `{$w -> 0^+$}` is computed, then `w` is replaced back by `{$x - a$}`. Exponents may be negative or fractional,
//! and coefficients may contain `{$ln(x - a)$}`.

use crate::field::real::expr::{Expr, Real, fun, value, variable, zero};
use malachite::Rational;

use crate::{
    context::{Context, Symbol},
    term::Term,
};

use super::{Direction, LimitError, LimitResult, gruntz::Gruntz, prepare, series};

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
            return side_series(&f, x, order, |w| &sign / w, &sign / &variable(x), ln_back);
        }
        // `{$x = a + s w$}`, so `{$w = s (x - a)$}`
        let side = |sign: i64| {
            let sign = value(Rational::from(sign));
            let w = &sign * &(variable(x) - point.clone());
            let ln_back = fun(Context::LN, w.clone());
            side_series(&f, x, order, |w| point + &(&sign * w), w, ln_back)
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

/// The series of `f` with `x` replaced by `at(w)` for `{$w -> 0^+$}`, up to `{$O(w^n)$}`, with `w` replaced back
/// by `back` and `{$ln w$}` by `ln_back`.
fn side_series(
    f: &Expr,
    x: Symbol,
    order: &Rational,
    at: impl Fn(&Expr) -> Expr,
    back: Expr,
    ln_back: Expr,
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
                .substitute(logw, &ln_back)
                .ok_or(LimitError::Unsupported)?;
            Ok(res + coefficient * back.pow(&exponant))
        })
}
