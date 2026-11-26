//! Real roots of polynomials with rational coefficients, exact even without radicals: `rootof(p, x, k)` is the
//! `k`-th real root of `p`, normalized to a rational, a square root for quadratic factors, or the internal
//! function `@rootof(j, c_0, ..., c_n)` ([`Context::real_root`]) for an irreducible factor of degree 3 or more,
//! whose roots are isolated by Sturm sequences. Powers of such a root `{$alpha$}` are reduced modulo its polynomial,
//! so that polynomials in `{$alpha$}` have a canonical form (`{$alpha^5 - alpha - 1 = 0$}`).

use std::cmp::Ordering;

use malachite::{Integer, Rational, base::num::arithmetic::traits::UnsignedAbs};

use super::{
    R,
    expr::{Expr, half, int, value},
};
use crate::{
    context::{Context, Symbol},
    integrate::{poly::Poly, rational::factor},
    polynom::real_roots::{Isolated, isolate, primitive, square_free_part},
    term::{Fun, Normalize, Term},
};

/// A real root of a polynomial: its irreducible factor, primitive over `{$ZZ$}`, its index among the real roots of
/// the factor and an isolating interval.
struct Root {
    factor: Poly,
    index: usize,
    interval: Isolated,
}

impl Root {
    /// The root as an exact expression.
    fn term(&self) -> Expr {
        let c = |i: usize| value(self.factor.coefficient(i));
        match self.factor.degree() {
            1 => -c(0) / c(1),
            2 => {
                // `{$-b/(2a) minus.plus sqrt(b^2 - 4 a c) / (2 a)$}`, `a` being positive
                let two_a = int(2) * c(2);
                let root = (c(1) * c(1) - int(4) * c(2) * c(0)).pow(&half()) / &two_a;
                let root = if self.index == 0 { -root } else { root };
                root - c(1) / two_a
            }
            _ => real_root(&self.factor, self.index),
        }
    }
}

/// The internal function `@rootof(j, c_0, ..., c_n)` for the `j`-th real root of an irreducible polynomial `q`.
fn real_root(q: &Poly, j: usize) -> Expr {
    let args = std::iter::once(value(Rational::from(j)))
        .chain(q.coefficients().iter().cloned().map(value))
        .collect();
    Term::Fun(Box::new(Fun::new(Context::real_root(), args, R))).normalize()
}

/// The polynomial and index of the arguments of `@rootof(j, c_0, ..., c_n)`.
pub fn parts(args: &[Expr]) -> Option<(Poly, usize)> {
    let [Term::Value(j), coefficients @ ..] = args else {
        return None;
    };
    let coefficients = coefficients
        .iter()
        .map(|c| match c {
            Term::Value(c) => Some(c.value.clone()),
            _ => None,
        })
        .collect::<Option<Vec<_>>>()?;
    Some((Poly::new(coefficients), usize::try_from(&j.value).ok()?))
}

/// The isolating interval of the root `@rootof(j, c_0, ..., c_n)` given by its arguments.
fn interval(args: &[Expr]) -> Option<(Poly, Isolated)> {
    let (q, j) = parts(args)?;
    let interval = isolate(&q).into_iter().nth(j)?;
    Some((q, interval))
}

/// The real roots of `p`, a non-constant polynomial, by increasing order.
fn sorted_roots(p: &Poly) -> Vec<Root> {
    // A placeholder variable for the factorization, like in `quartic_roots`
    let factors = factor(&square_free_part(p), Context::PI);
    let mut roots: Vec<Root> = vec![];
    for q in factors {
        let q = primitive(&q);
        for (index, interval) in isolate(&q).into_iter().enumerate() {
            let mut root = Root {
                factor: q.clone(),
                index,
                interval,
            };
            // Insertion by comparing the isolating intervals, refined until they are disjoint
            let mut position = roots.len();
            while position > 0 {
                let previous = &mut roots[position - 1];
                if previous
                    .interval
                    .compare(&previous.factor, &mut root.interval, &root.factor)
                    == Ordering::Less
                {
                    break;
                }
                position -= 1;
            }
            roots.insert(position, root);
        }
    }
    roots
}

/// The exact real roots of the polynomial `p` with rational coefficients, of degree at least 1, by increasing
/// order: rationals, square roots for quadratic factors, and `rootof` for the others.
pub fn real_roots(p: &Poly) -> Vec<Expr> {
    sorted_roots(p).iter().map(Root::term).collect()
}

/// Evaluate `rootof(p, k)` or `rootof(p, x, k)`, the `k`-th real root of a polynomial with rational coefficients.
/// Returns `None` if `p` isn't such a polynomial or has fewer than `k` real roots.
pub fn eval_rootof(args: &[Expr]) -> Option<Expr> {
    let (p, x, k) = match args {
        [p, k] => {
            let symbols = p.symbols();
            let mut symbols = symbols.iter();
            let (Some(x), None) = (symbols.next(), symbols.next()) else {
                return None;
            };
            (p, *x, k)
        }
        [p, Term::Symbol(x), k] => (p, x.symbol, k),
        _ => return None,
    };
    let Term::Value(k) = k else {
        return None;
    };
    let k = usize::try_from(&k.value).ok()?.checked_sub(1)?;
    let p = Poly::from_term(p, x)?;
    if p.degree() == 0 {
        return None;
    }
    sorted_roots(&p).get(k).map(Root::term)
}

/// The power `{$alpha^n$}` of the root `{$alpha$}` of the irreducible `q` given by the arguments `args` of
/// `@rootof`, reduced modulo `q` when `{$n < 0$}` or `{$n >= deg q$}`.
pub fn reduce_power(alpha: &Expr, args: &[Expr], n: &Rational) -> Option<Expr> {
    let (q, _) = parts(args)?;
    let n = Integer::try_from(n).ok()?;
    if n >= 0 && n < q.degree() {
        return None;
    }
    let base = if n < 0 {
        Poly::x().inverse_mod(&q)
    } else {
        Poly::x()
    };
    let r = power_mod(&base, u64::try_from(&n.unsigned_abs()).ok()?, &q);
    Some(
        r.coefficients()
            .iter()
            .enumerate()
            .fold(Term::zero(R), |res, (i, c)| {
                res + value(c.clone()) * alpha.pow(&value(Rational::from(i)))
            }),
    )
}

/// `{$a^n mod m$}`.
fn power_mod(a: &Poly, mut n: u64, m: &Poly) -> Poly {
    let (mut res, mut a) = (Poly::one(), a.rem(m));
    while n > 0 {
        if n % 2 == 1 {
            res = res.mul(&a).rem(m);
        }
        a = a.mul(&a).rem(m);
        n /= 2;
    }
    res
}

/// The sign of the root `@rootof(j, c_0, ..., c_n)` given by its arguments, never 0.
pub fn sign(args: &[Expr]) -> Option<Ordering> {
    interval(args).map(|(_, interval)| interval.sign())
}

/// An approximation of the root `@rootof(j, c_0, ..., c_n)` given by its arguments, within `{$2^(-"bits")$}`.
pub fn approximate(args: &[Expr], bits: u64) -> Option<Rational> {
    let (q, mut interval) = interval(args)?;
    interval.refine(&q, bits);
    Some((interval.lower + interval.upper) >> 1u64)
}

/// The plain expression `rootof(p, k)` written for `@rootof(j, c_0, ..., c_n)`, with `p` in `x`, so that the
/// printed form is parsed back.
pub fn display(args: &[Expr]) -> Option<Expr> {
    let (q, j) = parts(args)?;
    let x = Symbol::new("x");
    let p = q.to_term(x);
    let k = value(Rational::from(j + 1));
    Some(Term::Fun(Box::new(Fun::new(
        Context::ROOTOF,
        vec![p, k],
        R,
    ))))
}
