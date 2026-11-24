//! Antiderivatives of functions of `{$|u|$}` and `{$sign u$}`, from the antiderivatives on the intervals where `u`
//! keeps its sign, joined continuously at the zeros of `u`: with `{$sign u$}` for a single zero
//! (`{$integral e^(-|x|) dif x = sign(x) (1 - e^(-|x|))$}`), with `piecewise` otherwise.

use std::cmp::Ordering;

use malachite::Rational;

use super::{
    IntegrateError, IntegrateResult,
    definite::{interior_point, zeros},
    linear,
};
use crate::{
    context::{Context, Symbol},
    field::real::{
        R,
        expr::{Expr, Real, constant_sign, depends, fun, map_tree, unary, value, variable},
    },
    limit::Direction,
    term::{Expand, Fun, Normalize, Term, relation::Relation},
};

/// An antiderivative of `f`, which contains `abs` or `sign` of terms depending on `x` whose real zeros are found.
pub(super) fn integrate(f: &Expr, x: Symbol) -> IntegrateResult<Expr> {
    let mut arguments = vec![];
    abs_arguments(f, x, &mut arguments);
    if arguments.is_empty() {
        return Err(IntegrateError::Unsupported);
    }
    let line = (f64::NEG_INFINITY, f64::INFINITY);
    let mut points = vec![];
    for u in &arguments {
        zeros(u, x, line, &mut points)?;
    }
    points.sort_by(|(p, _), (q, _)| p.partial_cmp(q).unwrap_or(Ordering::Equal));
    points.dedup_by(|(p, _), (q, _)| (*p - *q).abs() < 1e-12);
    // The antiderivative on each interval between the zeros
    let mut bounds = vec![f64::NEG_INFINITY];
    bounds.extend(points.iter().map(|(p, _)| *p));
    bounds.push(f64::INFINITY);
    let mut pieces = vec![];
    for pair in bounds.windows(2) {
        let sample = value(interior_point((pair[0], pair[1])).ok_or(IntegrateError::Unsupported)?);
        let piece = without_abs(f, x, &sample).ok_or(IntegrateError::Unsupported)?;
        pieces.push((piece.integrate(x)?, sample));
    }
    let at = |antiderivative: &Expr, point: &Expr| {
        antiderivative
            .limit(x, point, Direction::Both)
            .map_err(|_| IntegrateError::Unsupported)
    };
    match (points.as_slice(), pieces.as_slice()) {
        ([], [(antiderivative, _)]) => Ok(antiderivative.clone()),
        ([(_, point)], [(left, _), (right, sample)]) => {
            let left = left - &at(left, point)?;
            let right = right - &at(right, point)?;
            Ok(join_with_sign(
                &arguments[0],
                x,
                point,
                sample,
                &left,
                &right,
            ))
        }
        _ => {
            // `{$F_k + C_k$}` on the `k`-th interval, `{$C_k$}` making the antiderivative continuous
            let mut args = vec![];
            let mut constant = Term::zero(R);
            for (k, (_, point)) in points.iter().enumerate() {
                let ((antiderivative, _), (next, _)) = (&pieces[k], &pieces[k + 1]);
                let condition =
                    Fun::new(Relation::Less.symbol(), vec![variable(x), point.clone()], R);
                args.push(Term::Fun(Box::new(condition)));
                args.push(antiderivative + &constant);
                constant = constant + at(antiderivative, point)? - at(next, point)?;
            }
            let (last, _) = pieces.last().ok_or(IntegrateError::Unsupported)?;
            args.push(last + &constant);
            Ok(Term::Fun(Box::new(Fun::new(Context::PIECEWISE, args, R))).normalize())
        }
    }
}

/// The antiderivative equal to `left` and `right` (both zero at the zero `point` of `u`) on each side of it:
/// `{$(L + R)/2 + s sign(u) (R - L)/2$}`, `s` being the sign of `u` on the right, or `{$sign(u) R$}`
/// (`{$sign(u) L$}` for `{$s = -1$}`) when `{$L = -R$}`. For a linear `u`, `left` and `right` are first written with `{$|u|$}`, giving a single term when
/// they agree up to the sign.
fn join_with_sign(
    u: &Expr,
    x: Symbol,
    point: &Expr,
    sample: &Expr,
    left: &Expr,
    right: &Expr,
) -> Expr {
    let decreasing =
        u.substitute(x, sample).as_ref().and_then(constant_sign) == Some(Ordering::Less);
    let sign = fun(Context::SIGN, u.clone());
    // `{$s sign(u) R = sign(u) L$}` when `{$s = -1$}` and `{$L = -R$}`
    let positive_side = |left: Expr, right: Expr| if decreasing { left } else { right };
    if let Some(a) = linear(u, x) {
        // `{$x = x_0 plus.minus |u| / |a|$}` on each side
        let distance = fun(Context::ABS, u.clone()) / fun(Context::ABS, a);
        let (left, right) = (
            left.substitute(x, &(point - &distance)),
            right.substitute(x, &(point + &distance)),
        );
        if let (Some(left), Some(right)) = (left, right) {
            if (&left - &right).expand().is_zero() {
                return right;
            }
            if (&left + &right).expand().is_zero() {
                return sign * positive_side(left, right);
            }
        }
    }
    if (left + right).expand().is_zero() {
        return sign * positive_side(left.clone(), right.clone());
    }
    let sign = if decreasing { -sign } else { sign };
    let half = value(Rational::from_signeds(1, 2));
    &half * &(left + right) + half * sign * (right - left)
}

/// Add to `arguments` the arguments of `abs` and `sign` depending on `x` in `term`.
pub(super) fn abs_arguments(term: &Expr, x: Symbol, arguments: &mut Vec<Expr>) {
    if !depends(term, x) {
        return;
    }
    match term {
        Term::Value(_) | Term::Symbol(_) => {}
        Term::Add(add) => add.iter().for_each(|t| abs_arguments(t, x, arguments)),
        Term::Mul(mul) => mul.iter().for_each(|t| abs_arguments(t, x, arguments)),
        Term::Pow(pow) => {
            abs_arguments(&pow.base, x, arguments);
            abs_arguments(&pow.exponant, x, arguments);
        }
        Term::Fun(fun) => {
            if let Some((Context::ABS | Context::SIGN, u)) = unary(term)
                && !arguments.contains(u)
            {
                arguments.push(u.clone());
            }
            for arg in fun.get_args::<Real>().into_iter().flatten() {
                abs_arguments(arg, x, arguments);
            }
        }
    }
}

/// `term` with `{$|u|$}` written `{$plus.minus u$}` and `{$sign u$}` written `{$plus.minus 1$}`, by the sign of `u`
/// at the point `sample`. `None` if a sign is unknown.
pub(super) fn without_abs(term: &Expr, x: Symbol, sample: &Expr) -> Option<Expr> {
    let failed = std::cell::Cell::new(false);
    let res = map_tree(term, &|t| {
        let (ident @ (Context::ABS | Context::SIGN), u) = unary(t)? else {
            return None;
        };
        if !depends(u, x) {
            return None;
        }
        let u = without_abs(u, x, sample).or_else(|| {
            failed.set(true);
            None
        })?;
        let sign = if let Some(sign @ (Ordering::Less | Ordering::Greater)) =
            u.substitute(x, sample).as_ref().and_then(constant_sign)
        {
            value(Rational::from(sign as i8))
        } else {
            failed.set(true);
            return None;
        };
        Some(if ident == Context::ABS {
            sign * u
        } else {
            sign
        })
    });
    (!failed.get()).then_some(res)
}
