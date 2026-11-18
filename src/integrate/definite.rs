//! Definite integrals, evaluating an antiderivative at the bounds with limits.
//!
//! The interval is split at the singular points of the integrand and of the antiderivative: real roots of
//! polynomial denominators, zeros of `sin` and `cos` in denominators, and poles of `tan` in the antiderivative
//! (from the substitution `{$t = tan(u / 2)$}`). Other denominators must keep the same sign on the interval, which
//! is checked at sample points.
//!
//! Before that, parts of the integrand made of inverse trigonometric functions which are constant on the interval
//! are replaced by their value, and on symmetric intervals `{$[-b, b]$}`, `{$f(x) + f(-x)$}` is integrated on
//! `{$[0, b]$}` when it simplifies to a rational function.

use crate::field::real::expr::sqrt;
use crate::field::real::expr::{
    DIGITS, Expr, Real, constant_sign, depends, half, has_special_constant, infinity_sign,
    is_infinite, one, unary, value, variable, zero,
};
use std::cmp::Ordering;

use malachite::{
    Rational,
    base::{
        num::{
            arithmetic::traits::{Abs, Ceiling, CheckedSqrt, Floor, PowerOf2},
            conversion::traits::RoundingFrom,
        },
        rounding_modes::RoundingMode,
    },
    rational::arithmetic::traits::SimplestRationalInInterval,
};

use crate::{
    context::{Context, Symbol},
    field::real::approx::{approximate, approximate_fixed},
    limit::{Direction, LimitError},
    solve::polynomial::PolynomialRoots,
    term::{Expand, Term},
};

use super::{
    IntegrateError, IntegrateResult, factors, linear, map_tree,
    poly::{Poly, rational_function},
    risch,
};

/// Bits of the numerical check of values computed by substitution.
const CHECK_BITS: u64 = 96;
/// Samples checking the sign of denominators which aren't analyzed.
const SAMPLES: i64 = 64;
/// Maximum number of poles of `tan` or zeros of `sin` and `cos` in the interval.
const MAX_PERIODS: i64 = 1000;

pub(super) fn integrate(f: &Expr, x: Symbol, a: &Expr, b: &Expr) -> IntegrateResult<Expr> {
    if depends(a, x) || depends(b, x) {
        return Err(IntegrateError::Unsupported);
    }
    if a == b {
        return Ok(zero());
    }
    let numeric = |t: &Expr| is_infinite(t) || is_constant(t);
    if !(numeric(a) && numeric(b)) {
        // Symbolic bounds: only without any possible singularity
        let antiderivative = f.integrate(x)?;
        if !regular(f, x) || !regular(&antiderivative, x) {
            return Err(IntegrateError::Unsupported);
        }
        return evaluate(&antiderivative, x, &[(a.clone(), true), (b.clone(), true)]);
    }
    let (a_value, b_value) = (approximate_bound(a)?, approximate_bound(b)?);
    match a_value.partial_cmp(&b_value) {
        Some(Ordering::Equal) => return Ok(zero()),
        Some(Ordering::Greater) => return integrate(f, x, b, a).map(|res| -res),
        _ => {}
    }
    let interval = (a_value, b_value);
    let f = &constant_parts(f, x, interval);
    if let Some(res) = symmetric(f, x, a, b, interval) {
        return res;
    }
    let antiderivative = f.integrate(x)?;
    let mut points = vec![];
    singular_points(f, x, (a_value, b_value), &mut points)?;
    singular_points(&antiderivative, x, (a_value, b_value), &mut points)?;
    points.sort_by(|(p, _), (q, _)| p.partial_cmp(q).unwrap_or(Ordering::Equal));
    points.dedup_by(|(p, _), (q, _)| (*p - *q).abs() < 1e-12);
    // Singular points are searched in the closed interval, the bounds being regular when none is found there
    let near = |p: f64, q: f64| (p - q).abs() < 1e-12 || p == q;
    let regular = |bound: f64| !points.iter().any(|(p, _)| near(*p, bound));
    let mut bounds = vec![(a.clone(), regular(a_value))];
    bounds.push((b.clone(), regular(b_value)));
    let inner = points
        .iter()
        .filter(|(p, _)| !near(*p, a_value) && !near(*p, b_value))
        .map(|(_, point)| (point.clone(), false));
    bounds.splice(1..1, inner);
    evaluate(&antiderivative, x, &bounds)
}

/// `{$sum_i F(p_(i+1)^-) - F(p_i^+)$}` for the increasing points `p_i`, with whether `F` is regular there.
fn evaluate(antiderivative: &Expr, x: Symbol, points: &[(Expr, bool)]) -> IntegrateResult<Expr> {
    let limit = |(point, regular): &(Expr, bool), direction: Direction| {
        let direction = if is_infinite(point) {
            Direction::Both
        } else {
            direction
        };
        match antiderivative.limit(x, point, direction) {
            Ok(res) if *regular => Ok(nicer_value(antiderivative, x, point, res)),
            Ok(res) => Ok(res),
            Err(LimitError::Undefined) => Err(IntegrateError::Undefined),
            Err(_) => Err(IntegrateError::Unsupported),
        }
    };
    let mut finite = zero();
    let mut infinite: Option<Ordering> = None;
    let mut add = |term: Expr, sign: Ordering| -> IntegrateResult<()> {
        let oo = variable(Context::OO);
        let direction = if term == oo {
            Some(sign)
        } else if term == -&oo {
            Some(sign.reverse())
        } else if has_special_constant(&term) {
            return Err(IntegrateError::Unsupported);
        } else {
            None
        };
        match (direction, infinite) {
            (None, _) => {
                finite += if sign == Ordering::Less { -term } else { term };
            }
            (Some(d), None) => infinite = Some(d),
            (Some(d), Some(e)) if d == e => {}
            (Some(_), Some(_)) => return Err(IntegrateError::Undefined),
        }
        Ok(())
    };
    for pair in points.windows(2) {
        add(limit(&pair[1], Direction::Left)?, Ordering::Greater)?;
        add(limit(&pair[0], Direction::Right)?, Ordering::Less)?;
    }
    match infinite {
        Some(sign) => Err(IntegrateError::Divergent(sign)),
        None => Ok(finite),
    }
}

/// `{$F(p)$}` by substitution when it is the limit `res` (which may be written differently, like `sin / cos` for
/// `tan`), and `res` otherwise.
fn nicer_value(antiderivative: &Expr, x: Symbol, point: &Expr, res: Expr) -> Expr {
    if is_infinite(point) || has_special_constant(&res) {
        return res;
    }
    let Some(substituted) = antiderivative.substitute(x, point) else {
        return res;
    };
    // Singular values like `{$0^(-1)$}` normalize to wrong constants, so the value is checked numerically
    let tolerance = Rational::power_of_2(-i64::try_from(CHECK_BITS / 2).unwrap_or(0));
    match approximate_fixed(&(&substituted - &res), CHECK_BITS) {
        Some(difference) if (&difference).abs() < tolerance => substituted,
        _ => res,
    }
}

/// Whether `term` is a number, possibly with constants like `{$pi$}`.
fn is_constant(term: &Expr) -> bool {
    term.symbols()
        .iter()
        .all(|s| matches!(*s, Context::PI | Context::E))
}

/// A bound as a float, `{$plus.minus oo$}` for infinite bounds.
fn approximate_bound(term: &Expr) -> IntegrateResult<f64> {
    match infinity_sign(term) {
        Some(Ordering::Greater) => Ok(f64::INFINITY),
        Some(_) => Ok(f64::NEG_INFINITY),
        None => to_f64(term).ok_or(IntegrateError::Unsupported),
    }
}

fn to_f64(term: &Expr) -> Option<f64> {
    approximate(term, DIGITS).map(|v| f64::rounding_from(&v, RoundingMode::Nearest).0)
}

/// Whether `term` has no denominator, `tan`, `ln` or fractional power depending on `x`, so that it is continuous.
fn regular(term: &Expr, x: Symbol) -> bool {
    const FUNCTIONS: [Symbol; 5] = [
        Context::EXP,
        Context::SIN,
        Context::COS,
        Context::ATAN,
        Context::ABS,
    ];
    only_continuous_parts(term, x, false, &FUNCTIONS)
}

/// Whether the parts of `term` depending on `x` are sums, products, integer powers (non-negative unless
/// `negative_powers`) with an exponant free of `x`, and `functions` of one argument.
fn only_continuous_parts(
    term: &Expr,
    x: Symbol,
    negative_powers: bool,
    functions: &[Symbol],
) -> bool {
    if !depends(term, x) {
        return true;
    }
    let recurse = |t: &Expr| only_continuous_parts(t, x, negative_powers, functions);
    match term {
        Term::Value(_) | Term::Symbol(_) => true,
        Term::Add(add) => add.iter().all(recurse),
        Term::Mul(mul) => mul.iter().all(recurse),
        Term::Pow(pow) => {
            !depends(&pow.exponant, x)
                && pow
                    .exponant
                    .to_i64()
                    .is_some_and(|n| negative_powers || n >= 0)
                && recurse(&pow.base)
        }
        Term::Fun(_) => {
            unary(term).is_some_and(|(ident, u)| functions.contains(&ident) && recurse(u))
        }
    }
}

/// Add to `points` the singular points of `term` in the closed interval: zeros of its denominators and poles
/// of `tan`, with their approximation.
fn singular_points(
    term: &Expr,
    x: Symbol,
    interval: (f64, f64),
    points: &mut Vec<(f64, Expr)>,
) -> IntegrateResult<()> {
    if !depends(term, x) {
        return Ok(());
    }
    match term {
        Term::Value(_) | Term::Symbol(_) => {}
        Term::Add(add) => {
            for t in add {
                singular_points(t, x, interval, points)?;
            }
        }
        Term::Mul(mul) => {
            for t in mul {
                singular_points(t, x, interval, points)?;
            }
        }
        Term::Pow(pow) => {
            singular_points(&pow.base, x, interval, points)?;
            if pow.exponant.is_strictly_negative() {
                zeros(&pow.base, x, interval, points)?;
            }
        }
        Term::Fun(fun) => {
            if let Some((Context::TAN, u)) = unary(term) {
                // Poles of `{$tan u$}` are the zeros of `{$cos u$}`
                periodic_zeros(u, x, interval, &half(), points)?;
            }
            for arg in fun.get_args::<Real>().into_iter().flatten() {
                singular_points(arg, x, interval, points)?;
            }
        }
    }
    Ok(())
}

/// Add to `points` the zeros of `term` in the closed interval.
fn zeros(
    term: &Expr,
    x: Symbol,
    interval: (f64, f64),
    points: &mut Vec<(f64, Expr)>,
) -> IntegrateResult<()> {
    for factor in factors(term) {
        let factor = match &factor {
            Term::Pow(pow) if !depends(&pow.exponant, x) => (*pow.base).clone(),
            _ => factor,
        };
        if !depends(&factor, x) {
            continue;
        }
        match unary(&factor) {
            Some((Context::EXP, _)) => continue,
            Some((Context::SIN, u)) => {
                periodic_zeros(u, x, interval, &zero(), points)?;
                continue;
            }
            Some((Context::COS, u)) => {
                periodic_zeros(u, x, interval, &half(), points)?;
                continue;
            }
            _ => {}
        }
        if let Some(p) = Poly::from_term(&factor, x) {
            polynomial_zeros(&p, x, interval, points)?;
        } else {
            same_sign(&factor, x, interval)?;
        }
    }
    Ok(())
}

/// Add the real roots of `p` inside the interval.
fn polynomial_zeros(
    p: &Poly,
    x: Symbol,
    interval: (f64, f64),
    points: &mut Vec<(f64, Expr)>,
) -> IntegrateResult<()> {
    let factored = p.to_term(x).factor();
    for factor in factors(&factored) {
        let factor = match &factor {
            Term::Pow(pow) => (*pow.base).clone(),
            _ => factor,
        };
        let Some(q) = Poly::from_term(&factor, x) else {
            continue;
        };
        if q.degree() == 0 {
            continue;
        }
        let coefficients: Vec<_> = q.coefficients().iter().map(|c| value(c.clone())).collect();
        let roots =
            <Real as PolynomialRoots>::roots(&coefficients).ok_or(IntegrateError::Unsupported)?;
        for root in roots {
            let r = to_f64(&root).ok_or(IntegrateError::Unsupported)?;
            if interval.0 <= r && r <= interval.1 {
                points.push((r, root.expand()));
            }
        }
    }
    Ok(())
}

/// Add the points where `{$u = (k + "offset") pi$}` for an integer `k`, `u` being linear in `x`.
fn periodic_zeros(
    u: &Expr,
    x: Symbol,
    interval: (f64, f64),
    offset: &Expr,
    points: &mut Vec<(f64, Expr)>,
) -> IntegrateResult<()> {
    let a = linear(u, x).ok_or(IntegrateError::Unsupported)?;
    if !interval.0.is_finite() || !interval.1.is_finite() {
        return Err(IntegrateError::Unsupported);
    }
    let b = u
        .substitute(x, &zero())
        .ok_or(IntegrateError::Unsupported)?;
    let (a_value, b_value) = (
        to_f64(&a).ok_or(IntegrateError::Unsupported)?,
        to_f64(&b).ok_or(IntegrateError::Unsupported)?,
    );
    let offset_value = to_f64(offset).ok_or(IntegrateError::Unsupported)?;
    let pi = std::f64::consts::PI;
    // `{$k pi + "offset" pi$}` between `u(a)` and `u(b)`
    let (u0, u1) = (
        a_value * interval.0 + b_value,
        a_value * interval.1 + b_value,
    );
    let (low, high) = (
        u0.min(u1) / pi - offset_value,
        u0.max(u1) / pi - offset_value,
    );
    let first = Rational::try_from(low)
        .map_err(|_| IntegrateError::Unsupported)?
        .ceiling();
    let first = i64::try_from(&first).map_err(|_| IntegrateError::Unsupported)?;
    let last = high.floor() as i64;
    if last - first > MAX_PERIODS {
        return Err(IntegrateError::Unsupported);
    }
    for k in first..=last {
        let point = ((value(Rational::from(k)) + offset) * variable(Context::PI) - &b) / &a;
        let p = to_f64(&point).ok_or(IntegrateError::Unsupported)?;
        if interval.0 <= p && p <= interval.1 {
            points.push((p, point.expand()));
        }
    }
    Ok(())
}

/// Check that `term` keeps the same sign on the finite interval, at sample points.
fn same_sign(term: &Expr, x: Symbol, interval: (f64, f64)) -> IntegrateResult<()> {
    if !interval.0.is_finite() || !interval.1.is_finite() {
        return Err(IntegrateError::Unsupported);
    }
    let mut sign = None;
    for i in 1..SAMPLES {
        let point = interval.0 + (interval.1 - interval.0) * (i as f64) / (SAMPLES as f64);
        let point = Rational::try_from(point).map_err(|_| IntegrateError::Unsupported)?;
        let s = term
            .substitute(x, &value(point))
            .as_ref()
            .and_then(constant_sign)
            .ok_or(IntegrateError::Unsupported)?;
        match (sign, s) {
            (_, Ordering::Equal) => return Err(IntegrateError::Unsupported),
            (None, s) => sign = Some(s),
            (Some(previous), s) if previous != s => return Err(IntegrateError::Unsupported),
            _ => {}
        }
    }
    Ok(())
}

/// Whether `p` is strictly inside the interval, away from its bounds.
fn interior(p: f64, interval: (f64, f64)) -> bool {
    interval.0 + 1e-12 < p && p < interval.1 - 1e-12
}

/// A simple rational point strictly inside the interval, 0 when possible.
fn interior_point(interval: (f64, f64)) -> Option<Rational> {
    Some(match (interval.0.is_finite(), interval.1.is_finite()) {
        (true, true) => Rational::simplest_rational_in_open_interval(
            &Rational::try_from(interval.0).ok()?,
            &Rational::try_from(interval.1).ok()?,
        ),
        (false, true) => {
            Rational::from((&Rational::try_from(interval.1).ok()?).floor()) - Rational::from(1)
        }
        (true, false) => {
            Rational::from((&Rational::try_from(interval.0).ok()?).ceiling()) + Rational::from(1)
        }
        (false, false) => Rational::from(0),
    })
}

/// Whether `term` contains `asin`, `acos` or `atan`.
fn has_inverse_trig(term: &Expr) -> bool {
    match term {
        Term::Value(_) | Term::Symbol(_) => false,
        Term::Add(add) => add.iter().any(has_inverse_trig),
        Term::Mul(mul) => mul.iter().any(has_inverse_trig),
        Term::Pow(pow) => has_inverse_trig(&pow.base) || has_inverse_trig(&pow.exponant),
        Term::Fun(fun) => {
            matches!(
                fun.get_ident(),
                Context::ASIN | Context::ACOS | Context::ATAN
            ) || fun
                .get_args::<Real>()
                .into_iter()
                .flatten()
                .any(has_inverse_trig)
        }
    }
}

/// `f` with its sums and functions of inverse trigonometric functions which are constant on the open interval
/// replaced by their value, like `{$acos(2x / (1 + x^2)) + atan(2x / (1 - x^2)) = pi/2$}` on `{$(-1, 1)$}`.
fn constant_parts(f: &Expr, x: Symbol, interval: (f64, f64)) -> Expr {
    if !has_inverse_trig(f) {
        return f.clone();
    }
    let Some(point) = interior_point(interval) else {
        return f.clone();
    };
    // Points where inverse trigonometric functions have exact values, tried first for a value without them
    let sqrt = |n: i64| sqrt(value(Rational::from(n)));
    let mut candidates = vec![value(point)];
    for p in [
        zero(),
        one(),
        half(),
        sqrt(3),
        sqrt(3) / value(Rational::from(3)),
        sqrt(2) / value(Rational::from(2)),
        sqrt(3) / value(Rational::from(2)),
    ] {
        candidates.insert(candidates.len() - 1, -&p);
        candidates.insert(candidates.len() - 1, p);
    }
    candidates.retain(|p| to_f64(p).is_some_and(|p| interior(p, interval)));
    map_tree(f, &|t| {
        if !depends(t, x) {
            return Some(t.clone());
        }
        if matches!(t, Term::Add(_) | Term::Fun(_))
            && has_inverse_trig(t)
            && locally_constant(t, x, interval)
        {
            let values = candidates.iter().filter_map(|p| t.substitute(x, p));
            let values: Vec<_> = values.collect();
            return values
                .iter()
                .find(|v| !has_inverse_trig(v))
                .or_else(|| values.last())
                .cloned();
        }
        None
    })
}

/// Whether `g` is constant on the open interval: it has no singular point there, and its derivative is exactly
/// zero once square roots of squares are written with the sign they have on the interval.
fn locally_constant(g: &Expr, x: Symbol, interval: (f64, f64)) -> bool {
    let mut points = vec![];
    if singular_points(g, x, interval, &mut points).is_err()
        || points.iter().any(|(p, _)| interior(*p, interval))
    {
        return false;
    }
    let derivative = map_tree(&g.derivative(x), &|t| square_root(t, x, interval));
    rational_function(&derivative, x).is_some_and(|(p, _)| p.is_zero())
}

/// `{$r^(n/2)$}` as `{$(plus.minus c p / q)^n$}` for a rational function `{$r = c^2 p^2 / q^2$}` of `x`, the sign
/// of `{$p / q$}` being constant on the interval.
fn square_root(t: &Expr, x: Symbol, interval: (f64, f64)) -> Option<Expr> {
    let Term::Pow(pow) = t else {
        return None;
    };
    let Term::Value(exponant) = &**pow.exponant else {
        return None;
    };
    if exponant.value.denominator_ref() != &2 || !depends(&pow.base, x) {
        return None;
    }
    let (p, q) = rational_function(&pow.base, x)?;
    let (c, p) = polynomial_sqrt(&p)?;
    let (d, q) = polynomial_sqrt(&q)?;
    let mut points = vec![];
    polynomial_zeros(&p, x, interval, &mut points).ok()?;
    polynomial_zeros(&q, x, interval, &mut points).ok()?;
    if points.iter().any(|(p, _)| interior(*p, interval)) {
        return None;
    }
    let point = interior_point(interval)?;
    let c = match (p.eval(&point) * q.eval(&point)).partial_cmp(&0)? {
        Ordering::Greater => c / d,
        Ordering::Less => -c / d,
        Ordering::Equal => return None,
    };
    let root = value(c) * p.to_term(x) / q.to_term(x);
    Some(root.pow(&value(Rational::from(2) * &exponant.value)))
}

/// `{$(c, q)$}` with `{$p = c^2 q^2$}`, `c` rational and `q` monic, if `p` is such a square.
fn polynomial_sqrt(p: &Poly) -> Option<(Rational, Poly)> {
    if p.is_zero() {
        return None;
    }
    let c = (&p.leading()).checked_sqrt()?;
    let mut root = Poly::one();
    for (i, factor) in p.square_free().iter().enumerate() {
        let multiplicity = i + 1;
        if factor.degree() > 0 {
            if multiplicity % 2 == 1 {
                return None;
            }
            root = root.mul(&factor.pow(multiplicity / 2));
        }
    }
    Some((c, root))
}

/// Whether `term` is continuous wherever its denominators don't vanish (which [`singular_points`] checks): it has
/// no `ln`, no fractional power, and only functions continuous on their argument (or `tan`, whose poles are found
/// by [`singular_points`]).
fn continuous(term: &Expr, x: Symbol) -> bool {
    const FUNCTIONS: [Symbol; 8] = [
        Context::EXP,
        Context::SIN,
        Context::COS,
        Context::TAN,
        Context::ATAN,
        Context::ABS,
        Context::ERF,
        Context::ERFI,
    ];
    only_continuous_parts(term, x, true, &FUNCTIONS)
}

/// `{$integral_(-b)^b f = integral_0^b (f(x) + f(-x))$}` when `f` is continuous on the finite interval, is not a
/// rational function, and `{$f(x) + f(-x)$}` is one (like `{$1/(e^x + 1) + 1/(e^(-x) + 1) = 1$}`), checked by
/// writing it in its Risch tower. Constant factors are left out.
fn symmetric(
    f: &Expr,
    x: Symbol,
    a: &Expr,
    b: &Expr,
    interval: (f64, f64),
) -> Option<IntegrateResult<Expr>> {
    if !(interval.0.is_finite() && interval.1.is_finite())
        || !(a + b).is_zero()
        || !continuous(f, x)
    {
        return None;
    }
    let mut points = vec![];
    singular_points(f, x, interval, &mut points).ok()?;
    if !points.is_empty() {
        return None;
    }
    let one = one();
    let (constant, g) = factors(f)
        .into_iter()
        .partition::<Vec<_>, _>(|t| !depends(t, x));
    let constant = constant.iter().fold(one.clone(), |res, t| res * t);
    let g = g.iter().fold(one, |res, t| res * t);
    if risch::canonical(&g, x).is_none_or(|(_, level)| level <= 1) {
        return None;
    }
    let (s, level) = risch::canonical(&(&g + &g.substitute(x, &-variable(x))?), x)?;
    if level > 1 {
        return None;
    }
    Some(integrate(&s, x, &zero(), b).map(|res| constant * res))
}
