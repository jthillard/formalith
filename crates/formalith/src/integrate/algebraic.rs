//! Integrals of algebraic functions which a substitution makes rational.
//!
//! - Rational functions of `x` and of powers `{$y^(p_i / q_i)$}` of a single Möbius function
//!   `{$y = (a x + b) / (c x + d)$}` (`{$a d - b c != 0$}`): with `{$t = y^(1 / L)$}`, `L` being the least common
//!   multiple of the `{$q_i$}`, `{$x = (d t^L - b) / (a - c t^L)$}` and `{$y^(p / q) = t^(p L / q)$}`, so the
//!   integrand becomes a rational function of `t`. When some `{$q_i$}` is even, `y` is non-negative where the
//!   integrand is real, and when they are all odd, so is `L` and real odd roots of negative values are fine.
//! - Rational functions of `x` and `{$sqrt(q)$}` with `{$q = A x^2 + B x + C$}` (Euler's substitutions), `t` being
//!   defined from `{$sqrt(q)$}` so that no sign is assumed: `{$t = sqrt(q) / (x - alpha)$}` for a rational root
//!   `alpha` of `q`, `{$t = sqrt(q) + sqrt(A) x$}` when `A` is the square of a rational, `{$t = (sqrt(q) - sqrt(C)) / x$}`
//!   when `C` is, and otherwise `{$t = sqrt(q / A) + x$}` for `{$A > 0$}`. A quadratic `{$A (x + h)^2$}` with a
//!   double root has `{$sqrt(q) = sqrt(A) |x + h|$}` instead.
//!
//! ```
//! use formalith::{field::real::R, parse};
//!
//! assert_eq!(
//!     parse!("integrate(sqrt(1/x - 1), x)", R),
//!     parse!("x*sqrt(1/x - 1) - atan(sqrt(1/x - 1))", R)
//! );
//! ```

use malachite::{
    Natural, Rational,
    base::num::arithmetic::traits::{CheckedSqrt, Lcm},
};

use crate::{
    context::{Context, Symbol},
    field::real::expr::{
        Expr, depends, exp_of_ln, fun, map_tree, size, smallest, sqrt, value, variable,
    },
    term::{Expand, Term},
};

use super::{Integrator, poly::Poly};

/// Largest size of the result, `MAX_SIZE_RATIO` times the size of the integrand plus `MAX_SIZE_EXTRA`.
const MAX_SIZE_RATIO: usize = 8;
/// See [`MAX_SIZE_RATIO`].
const MAX_SIZE_EXTRA: usize = 30;

pub(super) fn integrate(integrator: &mut Integrator, f: &Expr, x: Symbol) -> Option<Expr> {
    let radicals = radicals(f, x)?;
    if radicals.is_empty() {
        return None;
    }
    if let Some(res) = moebius(integrator, f, x, &radicals) {
        return Some(res);
    }
    if let Some(res) = perfect_square(integrator, f, x, &radicals) {
        return Some(res);
    }
    // Square roots of a quadratic polynomial: the smaller of the trigonometric and Euler's substitutions
    let trig = super::trig::substitute(integrator, f, x);
    let euler = euler(integrator, f, x, &radicals);
    match (trig, euler) {
        (Some(trig), Some(euler)) => Some(if size(&euler) < size(&trig) {
            euler
        } else {
            trig
        }),
        (trig, euler) => trig.or(euler),
    }
}

/// The powers `{$b^e$}` of `f` with a base `b` depending on `x` and a non-integer rational exponent `e`, if `f` is
/// a rational function of `x` and of them (no other function of `x`, no nested radicals).
fn radicals(f: &Expr, x: Symbol) -> Option<Vec<(Expr, Rational)>> {
    fn collect(f: &Expr, x: Symbol, res: &mut Vec<(Expr, Rational)>) -> bool {
        if !depends(f, x) {
            return true;
        }
        match f {
            Term::Value(_) | Term::Symbol(_) => true,
            Term::Add(add) => add.iter().all(|t| collect(t, x, res)),
            Term::Mul(mul) => mul.iter().all(|t| collect(t, x, res)),
            Term::Pow(pow) => match &**pow.exponant {
                Term::Value(e) if *e.value.denominator_ref() == 1u32 => collect(&pow.base, x, res),
                Term::Value(e) => {
                    if radicals(&pow.base, x).is_none_or(|inner| !inner.is_empty()) {
                        return false;
                    }
                    let entry = ((*pow.base).clone(), e.value.clone());
                    if !res.contains(&entry) {
                        res.push(entry);
                    }
                    true
                }
                _ => false,
            },
            Term::Fun(_) => false,
        }
    }
    let mut res = vec![];
    collect(f, x, &mut res).then_some(res)
}

/// The integral of `f` after the substitution `{$x = x(t)$}`, where `powers` gives the radicals of `f` in `t` and
/// `t_x` is `t` as an expression of `x`.
fn substitute(
    integrator: &mut Integrator,
    f: &Expr,
    x: Symbol,
    t_symbol: Symbol,
    x_t: &Expr,
    powers: &impl Fn(&Expr, &Rational) -> Option<Expr>,
    t_x: &Expr,
) -> Option<Expr> {
    let g = map_tree(f, &|term| match term {
        Term::Symbol(s) if s.symbol == x => Some(x_t.clone()),
        Term::Pow(pow) if depends(&pow.base, x) => match &**pow.exponant {
            Term::Value(e) if *e.value.denominator_ref() != 1u32 => powers(&pow.base, &e.value),
            _ => None,
        },
        _ => None,
    });
    let g = g * x_t.derivative(t_symbol);
    if depends(&g, x) {
        return None;
    }
    let res = integrator.integrate(&g, t_symbol)?;
    let res = exp_of_ln(&super::replace_symbol(&res, t_symbol, t_x));
    let res = tidy(res);
    (size(&res) <= MAX_SIZE_RATIO * size(f) + MAX_SIZE_EXTRA).then_some(res)
}

/// The smallest of `res`, its simplification and its expansion.
fn tidy(res: Expr) -> Expr {
    let candidates = [res.simplify(), res.expand()];
    smallest(res, candidates)
}

/// `{$integral f$}` for a rational function of `x` and of powers of a single Möbius function `y`, with
/// `{$t = y^(1 / L)$}`.
fn moebius(
    integrator: &mut Integrator,
    f: &Expr,
    x: Symbol,
    radicals: &[(Expr, Rational)],
) -> Option<Expr> {
    let (y, _) = &radicals[0];
    let (num, den) = y.as_fraction(true);
    let ([b, a], [d, c]) = (linear_coefficients(&num, x)?, linear_coefficients(&den, x)?);
    if (&a * &d - &b * &c).expand().is_zero() {
        return None;
    }
    // Other bases are `y` or `1/y`, as rational functions
    let mut signs = vec![];
    for (base, _) in radicals {
        let (n, m) = base.as_fraction(true);
        if (&n * &den - &m * &num).expand().is_zero() {
            signs.push((base.clone(), 1));
        } else if (&n * &num - &m * &den).expand().is_zero() {
            signs.push((base.clone(), -1));
        } else {
            return None;
        }
    }
    let l = radicals
        .iter()
        .fold(Natural::from(1u32), |l, (_, e)| l.lcm(e.denominator_ref()));
    let l = Rational::from(l);
    let t_symbol = integrator.fresh_symbol();
    let t = variable(t_symbol);
    let t_l = t.pow(&value(l.clone()));
    let x_t = (d * &t_l - b) / (a - c * &t_l);
    let powers = |base: &Expr, e: &Rational| {
        let (_, sign) = signs.iter().find(|(b, _)| b == base)?;
        Some(t.pow(&value(e * &l * Rational::from(*sign))))
    };
    let t_x = y.pow(&value(Rational::from(1) / &l));
    substitute(integrator, f, x, t_symbol, &x_t, &powers, &t_x)
}

/// The coefficients `{$[b, a]$}` of a polynomial `{$a x + b$}` of degree at most one in `x`, which may contain other
/// symbols (`{$r / x - 1 = (r - x) / x$}`).
fn linear_coefficients(p: &Expr, x: Symbol) -> Option<[Expr; 2]> {
    let a = p.derivative(x).expand();
    if depends(&a, x) {
        return None;
    }
    let b = (p - &(&a * &variable(x))).expand();
    (!depends(&b, x)).then_some([b, a])
}

/// `{$integral f$}` for a rational function of `x` and `{$sqrt(q)$}`, `q` being a quadratic `{$a (x + h)^2$}`
/// with a double root, which the substitutions don't handle (they degenerate to a constant `x`): for
/// `{$a > 0$}`, `{$q^(n / 2) = a^(n / 2) |x + h|^n$}`, integrated by the search, else by `abs::integrate`. For
/// `{$a < 0$}`, the integrand is only real at `{$x = -h$}`, so `None`.
fn perfect_square(
    integrator: &mut Integrator,
    f: &Expr,
    x: Symbol,
    radicals: &[(Expr, Rational)],
) -> Option<Expr> {
    let q = &radicals[0].0;
    if radicals.iter().any(|(b, _)| b != q) {
        return None;
    }
    let (a, h, k) = super::table::quadratic(q, x)?;
    if k != 0 || a < 0 {
        return None;
    }
    let abs = fun(Context::ABS, variable(x) + value(h));
    let g = map_tree(f, &|term| match term {
        Term::Pow(pow) if *pow.base == *q => match &**pow.exponant {
            Term::Value(e) => {
                let n = value(&e.value * Rational::from(2));
                Some(value(a.clone()).pow(&value(e.value.clone())) * abs.pow(&n))
            }
            _ => None,
        },
        _ => None,
    });
    integrator
        .integrate(&g, x)
        .or_else(|| super::abs::integrate(&g, x).ok())
}

/// `{$integral f$}` for a rational function of `x` and `{$sqrt(q)$}`, `q` being quadratic, by Euler's
/// substitutions.
fn euler(
    integrator: &mut Integrator,
    f: &Expr,
    x: Symbol,
    radicals: &[(Expr, Rational)],
) -> Option<Expr> {
    let q = &radicals[0].0;
    if radicals
        .iter()
        .any(|(b, e)| b != q || *e.denominator_ref() != 2u32)
    {
        return None;
    }
    let p = Poly::from_term(q, x)?;
    if p.degree() != 2 {
        return None;
    }
    let (c0, c1, c2) = (p.coefficient(0), p.coefficient(1), p.coefficient(2));
    let t_symbol = integrator.fresh_symbol();
    let t = variable(t_symbol);
    let xv = variable(x);
    let root = sqrt(q);
    let two = Rational::from(2);
    let discriminant = &c1 * &c1 - Rational::from(4) * &c2 * &c0;
    // `(x(t), sqrt(q)(t), t(x))`
    // A double root, see `perfect_square`
    if discriminant == 0 {
        return None;
    }
    let (x_t, root_t, t_x) = if let Some(s) = (discriminant > 0)
        .then(|| (&discriminant).checked_sqrt())
        .flatten()
    {
        // `{$q = A (x - alpha) (x - beta)$}`, `{$t = sqrt(q) / (x - alpha)$}`, `{$t^2 = A (x - beta) / (x - alpha)$}`
        let alpha = (-&c1 + &s) / (&two * &c2);
        let beta = (-&c1 - &s) / (&two * &c2);
        let t2 = &t * &t;
        let x_t = (value(alpha.clone()) * &t2 - value(&c2 * &beta)) / (&t2 - &value(c2));
        let root_t = (&x_t - &value(alpha.clone())) * &t;
        (x_t, root_t, &root / &(&xv - &value(alpha)))
    } else if let Some(s) = (&c2).checked_sqrt().filter(|s| *s > 0) {
        // `{$t = sqrt(q) + s x$}`: `{$t^2 - 2 s t x = B x + C$}`
        let x_t = (&t * &t - value(c0)) / (value(c1) + value(&two * &s) * &t);
        let root_t = &t - &(value(s.clone()) * &x_t);
        (x_t, root_t, &root + &(value(s) * &xv))
    } else if let Some(r) = (&c0).checked_sqrt().filter(|r| *r > 0) {
        // `{$t = (sqrt(q) - r) / x$}`: `{$x t^2 + 2 r t = A x + B$}`
        let x_t = (value(&two * &r) * &t - value(c1)) / (value(c2) - &t * &t);
        let root_t = &x_t * &t + value(r.clone());
        (x_t, root_t, (&root - &value(r)) / xv)
    } else if c2 > 0 {
        // `{$sqrt(q) = sqrt(A) sqrt(m)$}` with `{$m = x^2 + B' x + C'$}`, `{$t = sqrt(m) + x$}`
        let (b, c) = (&c1 / &c2, &c0 / &c2);
        let x_t = (&t * &t - value(c)) / (value(b) + value(two) * &t);
        let sqrt_a = sqrt(&value(c2));
        let root_t = &sqrt_a * &(&t - &x_t);
        (x_t, root_t, &root / &sqrt_a + xv)
    } else {
        return None;
    };
    let powers =
        |base: &Expr, e: &Rational| (base == q).then(|| root_t.pow(&value(e * Rational::from(2))));
    substitute(integrator, f, x, t_symbol, &x_t, &powers, &t_x)
}
