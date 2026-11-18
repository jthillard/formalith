//! Definite integrals, evaluating an antiderivative at the bounds with limits.
//!
//! The interval is split at the singular points of the integrand and of the antiderivative: real roots of
//! polynomial denominators, zeros of `sin` and `cos` in denominators, and poles of `tan` in the antiderivative
//! (from the substitution `{$t = tan(u / 2)$}`). Other denominators must keep the same sign on the interval, which
//! is checked at sample points.

use std::cmp::Ordering;

use malachite::{
    Rational,
    base::{
        num::{
            arithmetic::traits::{Abs, Ceiling, PowerOf2},
            conversion::traits::RoundingFrom,
        },
        rounding_modes::RoundingMode,
    },
};

use crate::{
    context::{Context, Symbol},
    field::real::{
        R,
        approx::{approximate, approximate_fixed},
    },
    limit::{Direction, LimitError, depends, value, variable},
    solve::polynomial::PolynomialRoots,
    term::{Expand, Term},
};

use super::{
    DIGITS, Expr, IntegrateError, IntegrateResult, Real, constant_sign, factors, linear, poly::Poly,
    unary,
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
        return Ok(Term::zero(R));
    }
    let antiderivative = f.integrate(x)?;
    let numeric = |t: &Expr| is_infinite(t) || is_constant(t);
    if !(numeric(a) && numeric(b)) {
        // Symbolic bounds: only without any possible singularity
        if !regular(f, x) || !regular(&antiderivative, x) {
            return Err(IntegrateError::Unsupported);
        }
        return evaluate(&antiderivative, x, &[(a.clone(), true), (b.clone(), true)]);
    }
    let (a_value, b_value) = (approximate_bound(a)?, approximate_bound(b)?);
    match a_value.partial_cmp(&b_value) {
        Some(Ordering::Equal) => return Ok(Term::zero(R)),
        Some(Ordering::Greater) => return integrate(f, x, b, a).map(|res| -res),
        _ => {}
    }
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
        let direction = if is_infinite(point) { Direction::Both } else { direction };
        match antiderivative.limit(x, point, direction) {
            Ok(res) if *regular => Ok(nicer_value(antiderivative, x, point, res)),
            Ok(res) => Ok(res),
            Err(LimitError::Undefined) => Err(IntegrateError::Undefined),
            Err(_) => Err(IntegrateError::Unsupported),
        }
    };
    let mut finite = Term::zero(R);
    let mut infinite: Option<Ordering> = None;
    let mut add = |term: Expr, sign: Ordering| -> IntegrateResult<()> {
        let oo = variable(Context::OO);
        let direction = if term == oo {
            Some(sign)
        } else if term == -&oo {
            Some(sign.reverse())
        } else if depends(&term, Context::OO) || depends(&term, Context::UNDEFINED) {
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
    if is_infinite(point) || depends(&res, Context::OO) || depends(&res, Context::UNDEFINED) {
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

fn is_infinite(term: &Expr) -> bool {
    let oo = variable(Context::OO);
    *term == oo || *term == -oo
}

/// Whether `term` is a number, possibly with constants like `{$pi$}`.
fn is_constant(term: &Expr) -> bool {
    term.symbols()
        .iter()
        .all(|s| matches!(*s, Context::PI | Context::E))
}

/// A bound as a float, `{$plus.minus oo$}` for infinite bounds.
fn approximate_bound(term: &Expr) -> IntegrateResult<f64> {
    if *term == variable(Context::OO) {
        return Ok(f64::INFINITY);
    }
    if *term == -variable(Context::OO) {
        return Ok(f64::NEG_INFINITY);
    }
    to_f64(term).ok_or(IntegrateError::Unsupported)
}

fn to_f64(term: &Expr) -> Option<f64> {
    approximate(term, DIGITS).map(|v| f64::rounding_from(&v, RoundingMode::Nearest).0)
}

/// Whether `term` has no denominator, `tan`, `ln` or fractional power depending on `x`, so that it is continuous.
fn regular(term: &Expr, x: Symbol) -> bool {
    if !depends(term, x) {
        return true;
    }
    match term {
        Term::Value(_) | Term::Symbol(_) => true,
        Term::Add(add) => add.iter().all(|t| regular(t, x)),
        Term::Mul(mul) => mul.iter().all(|t| regular(t, x)),
        Term::Pow(pow) => {
            !depends(&pow.exponant, x)
                && pow.exponant.to_i64().is_some_and(|n| n >= 0)
                && regular(&pow.base, x)
        }
        Term::Fun(_) => match unary(term) {
            Some((Context::EXP | Context::SIN | Context::COS | Context::ATAN | Context::ABS, u)) => {
                regular(u, x)
            }
            _ => false,
        },
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
                periodic_zeros(u, x, interval, &value(Rational::from_signeds(1, 2)), points)?;
            }
            for arg in fun.get_args::<Real>().into_iter().flatten() {
                singular_points(arg, x, interval, points)?;
            }
        }
    }
    Ok(())
}

/// Add to `points` the zeros of `term` in the closed interval.
fn zeros(term: &Expr, x: Symbol, interval: (f64, f64), points: &mut Vec<(f64, Expr)>) -> IntegrateResult<()> {
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
                periodic_zeros(u, x, interval, &Term::zero(R), points)?;
                continue;
            }
            Some((Context::COS, u)) => {
                periodic_zeros(u, x, interval, &value(Rational::from_signeds(1, 2)), points)?;
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
    let b = u.substitute(x, &Term::zero(R)).ok_or(IntegrateError::Unsupported)?;
    let (a_value, b_value) = (
        to_f64(&a).ok_or(IntegrateError::Unsupported)?,
        to_f64(&b).ok_or(IntegrateError::Unsupported)?,
    );
    let offset_value = to_f64(offset).ok_or(IntegrateError::Unsupported)?;
    let pi = std::f64::consts::PI;
    // `{$k pi + "offset" pi$}` between `u(a)` and `u(b)`
    let (u0, u1) = (a_value * interval.0 + b_value, a_value * interval.1 + b_value);
    let (low, high) = (u0.min(u1) / pi - offset_value, u0.max(u1) / pi - offset_value);
    let first = Rational::try_from(low).map_err(|_| IntegrateError::Unsupported)?.ceiling();
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
