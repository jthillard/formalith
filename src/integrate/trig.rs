//! Integrals of trigonometric and hyperbolic expressions.

use malachite::Rational;

use crate::{
    context::{Context, Symbol},
    field::real::R,
    limit::{depends, fun, value, variable},
    term::{Expand, Term},
};

use super::{Expr, Integrator, factors, linear, map_tree, poly, replace_symbol, unary};

/// `{$p / q$}` as an expression.
fn ratio(p: i64, q: i64) -> Expr {
    value(Rational::from_signeds(p, q))
}

/// `{$sin^m u$}` times `{$cos^n u$}`, as `(u, m, n)`, with `u` being linear in `x` (`{$tan u = sin u / cos u$}`).
fn sin_cos_powers(f: &Expr, x: Symbol) -> Option<(Expr, i64, i64)> {
    let mut argument: Option<Expr> = None;
    let (mut m, mut n) = (0, 0);
    for factor in factors(f) {
        let (base, k) = match &factor {
            Term::Pow(pow) => (&*pow.base, pow.exponant.to_i64()?),
            _ => (&factor, 1),
        };
        let (ident, u) = unary(base)?;
        if argument.as_ref().is_some_and(|argument| argument != u) {
            return None;
        }
        argument = Some(u.clone());
        match ident {
            Context::SIN => m += k,
            Context::COS => n += k,
            Context::TAN => (m, n) = (m + k, n - k),
            _ => return None,
        }
    }
    let u = argument?;
    linear(&u, x)?;
    Some((u, m, n))
}

/// `{$integral sin^m u cos^n u$}` for integers `m` and `n`: with `{$t = cos u$}` when `m` is odd,
/// `{$t = sin u$}` when `n` is odd, by reducing the powers with `{$sin^2 u = (1 - cos 2u) / 2$}` and
/// `{$cos^2 u = (1 + cos 2u) / 2$}` when both are even and positive, and with `{$t = tan u$}` otherwise.
pub(super) fn integrate_powers(integrator: &mut Integrator, f: &Expr, x: Symbol) -> Option<Expr> {
    let (u, m, n) = sin_cos_powers(f, x)?;
    let a = linear(&u, x)?;
    let one = Term::one(R);
    let int = |k: i64| value(Rational::from(k));
    let t_symbol = integrator.fresh_symbol();
    let t = variable(t_symbol);
    let (g, back) = if m.rem_euclid(2) == 1 {
        // `{$sin^m u cos^n u dif u = -(1 - t^2)^((m-1)/2) t^n dif t$}`
        let g = -(&one - &(&t * &t)).pow(&int((m - 1) / 2)) * t.pow(&int(n));
        (g, fun(Context::COS, u.clone()))
    } else if n.rem_euclid(2) == 1 {
        let g = (&one - &(&t * &t)).pow(&int((n - 1) / 2)) * t.pow(&int(m));
        (g, fun(Context::SIN, u.clone()))
    } else if m >= 0 && n >= 0 {
        let cos_2u = fun(Context::COS, int(2) * &u);
        let reduced = ((&one - &cos_2u) / int(2)).pow(&int(m / 2))
            * ((&one + &cos_2u) / int(2)).pow(&int(n / 2));
        return integrator.integrate(&reduced.expand(), x);
    } else {
        // `{$sin^m u cos^n u dif u = t^m (1 + t^2)^(-(m+n)/2 - 1) dif t$}`
        let g = t.pow(&int(m)) * (&one + &(&t * &t)).pow(&int(-(m + n) / 2 - 1));
        (g, fun(Context::TAN, u.clone()))
    };
    let res = integrator.integrate(&g.expand(), t_symbol)?;
    let res = replace_symbol(&res, t_symbol, &back);
    // `{$arctan(tan u) = u$}` up to a piecewise constant, which also makes the antiderivative continuous
    let res = map_tree(&res, &|term| match unary(term) {
        Some((Context::ATAN, v)) if *v == back => Some(u.clone()),
        _ => None,
    });
    Some(res / a)
}

/// Integrals after rewriting `f`: hyperbolic functions as exponentials, products of `sin` and `cos` of
/// different arguments as sums, or rational functions of `sin u` and `cos u` with `{$t = tan(u / 2)$}`.
pub(super) fn integrate_rewritten(
    integrator: &mut Integrator,
    f: &Expr,
    x: Symbol,
) -> Option<Expr> {
    if let Some(rewritten) = hyperbolic_as_exp(f, x) {
        return integrator.integrate(&rewritten, x);
    }
    if let Some(rewritten) = product_to_sum(f) {
        return integrator.integrate(&rewritten, x);
    }
    weierstrass(integrator, f, x)
}

/// `f` with its hyperbolic functions of `x` written with `exp`, if it has any.
pub(super) fn hyperbolic_as_exp(f: &Expr, x: Symbol) -> Option<Expr> {
    let rewritten = map_tree(f, &|t| {
        let (ident, u) = unary(t)?;
        if !depends(u, x) {
            return None;
        }
        let exp = |v: Expr| fun(Context::EXP, v);
        match ident {
            Context::SINH => Some((exp(u.clone()) - exp(-u)) / value(Rational::from(2))),
            Context::COSH => Some((exp(u.clone()) + exp(-u)) / value(Rational::from(2))),
            Context::TANH => {
                let e = exp(value(Rational::from(2)) * u);
                Some((&e - &Term::one(R)) / (e + Term::one(R)))
            }
            _ => None,
        }
    });
    (rewritten != *f).then_some(rewritten)
}

/// A product with two factors `sin` or `cos` of different arguments, written as a sum.
fn product_to_sum(f: &Expr) -> Option<Expr> {
    let factors = factors(f);
    for (i, first) in factors.iter().enumerate() {
        for (j, second) in factors.iter().enumerate().skip(i + 1) {
            let (Some((f1, a)), Some((f2, b))) = (unary(first), unary(second)) else {
                continue;
            };
            if a == b {
                continue;
            }
            let (sin, cos) = (
                |v: Expr| fun(Context::SIN, v),
                |v: Expr| fun(Context::COS, v),
            );
            let half = ratio(1, 2);
            let sum = match (f1, f2) {
                // `{$sin a sin b = (cos(a - b) - cos(a + b)) / 2$}`
                (Context::SIN, Context::SIN) => half * (cos(a - b) - cos(a + b)),
                // `{$cos a cos b = (cos(a - b) + cos(a + b)) / 2$}`
                (Context::COS, Context::COS) => half * (cos(a - b) + cos(a + b)),
                // `{$sin a cos b = (sin(a + b) + sin(a - b)) / 2$}`
                (Context::SIN, Context::COS) => half * (sin(a + b) + sin(a - b)),
                (Context::COS, Context::SIN) => half * (sin(a + b) + sin(b - a)),
                _ => continue,
            };
            let rest = factors
                .iter()
                .enumerate()
                .filter(|(k, _)| *k != i && *k != j)
                .fold(sum, |res, (_, factor)| res * factor);
            return Some(rest.expand());
        }
    }
    None
}

/// The argument of the trigonometric functions of `f`, if they all have the same.
fn trig_argument(f: &Expr, x: Symbol, argument: &mut Option<Expr>) -> bool {
    if let Some((Context::SIN | Context::COS | Context::TAN, u)) = unary(f)
        && depends(u, x)
    {
        if argument.as_ref().is_some_and(|argument| argument != u) {
            return false;
        }
        *argument = Some(u.clone());
        return true;
    }
    match f {
        Term::Value(_) | Term::Symbol(_) => true,
        Term::Add(add) => add.iter().all(|t| trig_argument(t, x, argument)),
        Term::Mul(mul) => mul.iter().all(|t| trig_argument(t, x, argument)),
        Term::Pow(pow) => {
            trig_argument(&pow.base, x, argument) && trig_argument(&pow.exponant, x, argument)
        }
        Term::Fun(fun) => fun
            .get_args::<crate::field::real::R<Rational>>()
            .is_some_and(|args| args.iter().all(|t| trig_argument(t, x, argument))),
    }
}

/// `{$integral f$}` for a rational function of `sin u`, `cos u` and `tan u`, with `u` linear in `x`, substituting
/// `{$t = tan(u / 2)$}`: `{$sin u = 2t / (1 + t^2)$}`, `{$cos u = (1 - t^2) / (1 + t^2)$}` and
/// `{$dif u = 2 / (1 + t^2) dif t$}`.
fn weierstrass(integrator: &mut Integrator, f: &Expr, x: Symbol) -> Option<Expr> {
    let mut argument = None;
    if !trig_argument(f, x, &mut argument) {
        return None;
    }
    let u = argument?;
    let a = linear(&u, x)?;
    let t_symbol = integrator.fresh_symbol();
    let t = variable(t_symbol);
    let one = Term::one(R);
    let two = value(Rational::from(2));
    let t2 = &t * &t;
    let g = map_tree(f, &|term| match unary(term) {
        Some((Context::SIN, v)) if *v == u => Some(&two * &t / (&one + &t2)),
        Some((Context::COS, v)) if *v == u => Some((&one - &t2) / (&one + &t2)),
        Some((Context::TAN, v)) if *v == u => Some(&two * &t / (&one - &t2)),
        _ => None,
    }) * &two
        / (&one + &t2);
    if depends(&g, x) {
        return None;
    }
    let (num, den) = poly::rational_function(&g, t_symbol)?;
    let res = super::rational::integrate(&num, &den, t_symbol)?;
    Some(replace_symbol(&res, t_symbol, &fun(Context::TAN, u / two)) / a)
}
