//! Integrals of trigonometric and hyperbolic expressions.

use crate::field::real::expr::{
    Expr, depends, fun, one, ratio, size, sqrt, unary, value, variable, zero,
};
use malachite::{Rational, base::num::arithmetic::traits::Abs};

use crate::{
    context::{Context, Symbol},
    term::{Expand, Term},
};

use super::{Integrator, factors, linear, map_tree, poly, replace_symbol, table};

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
    let one = one();
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
        crate::field::real::expr::hyperbolic_as_exp(ident, u)
    });
    (rewritten != *f).then_some(rewritten)
}

/// A product with two factors `sin` or `cos` of different arguments, written as a sum, the rewrite being repeated
/// on its terms (`{$sin a sin b cos c$}` has a single `sin` or `cos` per term). When the product has a factor which
/// isn't trigonometric, like `{$e^x$}`, factors of the same argument are merged too (`{$sin u cos u = sin(2u) / 2$}`),
/// and powers are reduced (`{$sin^2 u = (1 - cos 2u) / 2$}`), so that the product becomes a sum of terms with a
/// single `sin` or `cos`.
fn product_to_sum(f: &Expr) -> Option<Expr> {
    let is_trig = |factor: &Expr| {
        let base = match factor {
            Term::Pow(pow) => &*pow.base,
            _ => factor,
        };
        matches!(unary(base), Some((Context::SIN | Context::COS, _)))
    };
    let linearize = factors(f).iter().any(|factor| !is_trig(factor));
    let mut res = product_to_sum_once(f, linearize)?;
    // Each rewrite lowers the number of trigonometric factors of a term, this only bounds the size of the result
    for _ in 0..8 {
        let terms = match &res {
            Term::Add(add) => add.iter().cloned().collect(),
            _ => vec![res.clone()],
        };
        let mut changed = false;
        let rewritten = terms.into_iter().fold(zero(), |sum, term| {
            sum + product_to_sum_once(&term, linearize)
                .inspect(|_| changed = true)
                .unwrap_or(term)
        });
        if !changed {
            break;
        }
        res = rewritten;
    }
    Some(res)
}

/// One step of [`product_to_sum`], merging factors of the same argument and reducing powers when `linearize`.
fn product_to_sum_once(f: &Expr, linearize: bool) -> Option<Expr> {
    let factors = factors(f);
    let (sin, cos) = (
        |v: Expr| fun(Context::SIN, v),
        |v: Expr| fun(Context::COS, v),
    );
    let half = ratio(1, 2);
    let rest = |skip: &[usize], res: Expr| {
        factors
            .iter()
            .enumerate()
            .filter(|(k, _)| !skip.contains(k))
            .fold(res, |res, (_, factor)| res * factor)
            .expand()
    };
    for (i, first) in factors.iter().enumerate() {
        for (j, second) in factors.iter().enumerate().skip(i + 1) {
            let (Some((f1, a)), Some((f2, b))) = (unary(first), unary(second)) else {
                continue;
            };
            if a == b && !linearize {
                continue;
            }
            let sum = match (f1, f2) {
                // `{$sin a sin b = (cos(a - b) - cos(a + b)) / 2$}`
                (Context::SIN, Context::SIN) => &half * &(cos(a - b) - cos(a + b)),
                // `{$cos a cos b = (cos(a - b) + cos(a + b)) / 2$}`
                (Context::COS, Context::COS) => &half * &(cos(a - b) + cos(a + b)),
                // `{$sin a cos b = (sin(a + b) + sin(a - b)) / 2$}`
                (Context::SIN, Context::COS) => &half * &(sin(a + b) + sin(a - b)),
                (Context::COS, Context::SIN) => &half * &(sin(a + b) + sin(b - a)),
                _ => continue,
            };
            return Some(rest(&[i, j], sum));
        }
    }
    if !linearize {
        return None;
    }
    // `{$sin^n u = sin^(n - 2) u (1 - cos 2u) / 2$}`, `{$cos^n u = cos^(n - 2) u (1 + cos 2u) / 2$}`
    for (i, factor) in factors.iter().enumerate() {
        let Term::Pow(pow) = factor else {
            continue;
        };
        let (Some((ident @ (Context::SIN | Context::COS), u)), Some(n)) =
            (unary(&pow.base), pow.exponant.to_i64())
        else {
            continue;
        };
        if n < 2 {
            continue;
        }
        let cos_2u = cos(value(Rational::from(2)) * u);
        let reduced = if ident == Context::SIN {
            &half * &(one() - cos_2u)
        } else {
            &half * &(one() + cos_2u)
        };
        return Some(rest(
            &[i],
            pow.base.pow(&value(Rational::from(n - 2))) * reduced,
        ));
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
fn weierstrass(integrator: &Integrator, f: &Expr, x: Symbol) -> Option<Expr> {
    let mut argument = None;
    if !trig_argument(f, x, &mut argument) {
        return None;
    }
    let u = argument?;
    let a = linear(&u, x)?;
    let t_symbol = integrator.fresh_symbol();
    let t = variable(t_symbol);
    let one = one();
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

/// The base `q` of the half-integer powers of `f` depending on `x`, like `{$x^2 - 4$}` in
/// `{$1 / (x^2 sqrt(x^2 - 4))$}`, if they all have the same and `f` has no function of `x`.
fn radicand(f: &Expr, x: Symbol) -> Option<Expr> {
    fn collect(f: &Expr, x: Symbol, res: &mut Option<Expr>) -> bool {
        if !depends(f, x) {
            return true;
        }
        match f {
            Term::Value(_) | Term::Symbol(_) => true,
            Term::Add(add) => add.iter().all(|t| collect(t, x, res)),
            Term::Mul(mul) => mul.iter().all(|t| collect(t, x, res)),
            Term::Pow(pow) => match &**pow.exponant {
                Term::Value(e) if e.value.denominator_ref() == &2u32 => {
                    if res.as_ref().is_some_and(|q| *q != *pow.base) {
                        return false;
                    }
                    *res = Some((*pow.base).clone());
                    true
                }
                Term::Value(_) => collect(&pow.base, x, res),
                _ => false,
            },
            Term::Fun(_) => false,
        }
    }
    let mut res = None;
    collect(f, x, &mut res).then_some(res)?
}

/// `{$integral f$}` for a rational function of `x` and `{$sqrt(q)$}`, `q` being quadratic with rational
/// coefficients, written `{$a u^2 + k$}` with `{$u = x + h$}` and `{$r = sqrt(|k / a|)$}`, by a trigonometric
/// substitution:
/// - `{$u = r sin t$}` when `{$a < 0 < k$}`, `{$sqrt(q) = sqrt(k) cos t$}`, back with `{$t = arcsin(u / r)$}`,
/// - `{$u = r / cos t$}` when `{$k < 0 < a$}`, `{$sqrt(q) = sqrt(-k) tan t$}`, back with `{$t = arccos(r / u)$}`
///   (for `{$u > r$}`),
/// - `{$u = r tan t$}` when `{$a, k > 0$}`, `{$sqrt(q) = sqrt(k) / cos t$}`, back with `{$t = arctan(u / r)$}`.
///
/// The integral in `t` is a rational function of `{$sin t$}` and `{$cos t$}`, whose `sin t`, `cos t`, `tan t` and
/// `{$tan(t / 2) = sin t / (1 + cos t)$}` are written back with `{$sqrt(q)$}`, after expanding multiple angles.
pub(super) fn substitute(integrator: &mut Integrator, f: &Expr, x: Symbol) -> Option<Expr> {
    let q = radicand(f, x)?;
    let (a, h, k) = table::quadratic(&q, x)?;
    // `{$r = 0$}`: the substitution is degenerate (see `algebraic::integrate` for `{$q = a u^2$}`)
    if k == 0 {
        return None;
    }
    let t_symbol = integrator.fresh_symbol();
    let t = variable(t_symbol);
    let (sin_t, cos_t) = (fun(Context::SIN, t.clone()), fun(Context::COS, t.clone()));
    let one = one();
    let r = sqrt(&value((&k / &a).abs()));
    let sqrt_k = sqrt(&value(k.clone().abs()));
    let u = variable(x) + value(h.clone());
    let root = sqrt(&q);
    // `(u(t), sqrt(q)(t), du/dt)` and `(sin t, cos t, t)` in `x`
    let ((u_t, root_t, du), (sin_x, cos_x, t_x)) = match (a > 0, k > 0) {
        (false, true) => (
            (&r * &sin_t, &sqrt_k * &cos_t, &r * &cos_t),
            (&u / &r, &root / &sqrt_k, fun(Context::ASIN, &u / &r)),
        ),
        (true, false) => (
            (
                &r / &cos_t,
                &sqrt_k * &sin_t / &cos_t,
                &r * &sin_t / &(&cos_t * &cos_t),
            ),
            (
                &root * &r / (&sqrt_k * &u),
                &r / &u,
                fun(Context::ACOS, &r / &u),
            ),
        ),
        (true, true) => (
            (
                &r * &sin_t / &cos_t,
                &sqrt_k / &cos_t,
                &r / &(&cos_t * &cos_t),
            ),
            (
                &u * &sqrt_k / (&r * &root),
                &sqrt_k / &root,
                fun(Context::ATAN, &u / &r),
            ),
        ),
        (false, false) => return None,
    };
    let g = map_tree(f, &|term| match term {
        Term::Pow(pow) if *pow.base == q => match &**pow.exponant {
            Term::Value(e) => Some(root_t.pow(&value(&e.value * Rational::from(2)))),
            _ => None,
        },
        _ => None,
    });
    let g = replace_symbol(&g, x, &(&u_t - &value(h))) * du;
    if depends(&g, x) {
        return None;
    }
    let res = integrator.integrate(&g, t_symbol)?;
    // `{$sin(n t)$}` and `{$cos(n t)$}` in `x` for the small `n` of the result, by the addition formulas (only
    // those needed, since expanding products of radicals is slow)
    let largest = std::cell::Cell::new(0);
    map_tree(&res, &|term| {
        if let Some((Context::SIN | Context::COS | Context::TAN, v)) = unary(term)
            && let Some(n) = (1..=MAX_MULTIPLE).find(|n| *v == value(Rational::from(*n)) * &t)
        {
            largest.set(largest.get().max(n));
        }
        None
    });
    let multiples: Vec<_> = (1..=largest.get())
        .scan((sin_x.clone(), cos_x.clone()), |(sin, cos), n| {
            let res = (n, sin.clone(), cos.clone());
            (*sin, *cos) = (
                (&*sin * &cos_x + &*cos * &sin_x).expand(),
                (&*cos * &cos_x - &*sin * &sin_x).expand(),
            );
            Some(res)
        })
        .collect();
    let half_t = &t / &value(Rational::from(2));
    let res = map_tree(&res, &|term| {
        let (ident, v) = unary(term)?;
        if ident == Context::TAN && *v == half_t {
            return Some(&sin_x / &(&one + &cos_x));
        }
        let (_, sin, cos) = multiples
            .iter()
            .find(|(n, _, _)| *v == value(Rational::from(*n)) * &t)?;
        match ident {
            Context::SIN => Some(sin.clone()),
            Context::COS => Some(cos.clone()),
            Context::TAN => Some(sin / cos),
            _ => None,
        }
    });
    let res = replace_symbol(&res, t_symbol, &t_x);
    // Results written back from rational functions of `{$sin t$}` can be huge
    (size(&res) <= MAX_SIZE_RATIO * size(f) + MAX_SIZE_EXTRA).then_some(res)
}

/// Largest size of the result of a trigonometric substitution, `MAX_SIZE_RATIO` times the size of the integrand
/// plus `MAX_SIZE_EXTRA`.
const MAX_SIZE_RATIO: usize = 6;
/// See [`MAX_SIZE_RATIO`].
const MAX_SIZE_EXTRA: usize = 20;

/// Largest multiple `{$n t$}` of the angle of a trigonometric substitution written back in `x`.
const MAX_MULTIPLE: i64 = 8;
