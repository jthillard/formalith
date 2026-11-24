//! Integration of rational functions with rational coefficients.
//!
//! After removing the polynomial part, the Hermite reduction gives the rational part of the integral and a
//! remaining `{$A / D$}` with `D` square-free, whose integral is a sum of logarithms. `D` is factored over
//! `{$QQ$}`: for each irreducible factor `q`, the residues of `{$A / D$}` at the roots `r` of `q` are
//! `{$p(r)$}` with `{$p = A D'^(-1) mod q$}`. They are all equal to `c` when `p` is a constant, giving
//! `{$c ln|q|$}`. Otherwise, the roots of `q` are computed with radicals in `{$CC$}`: a real root gives
//! `{$p(r) ln|x - r|$}`, and a pair of conjugate roots `{$u plus.minus i v$}` with `{$p(u + i v) = alpha + i beta$}`
//! gives `{$alpha ln((x - u)^2 + v^2) - 2 beta arctan((x - u) / v)$}`.

use crate::field::real::expr::{Expr, constant_sign, fun, value, variable, zero};
use std::cmp::Ordering;

use malachite::{
    Rational,
    base::num::basic::traits::{One, Zero},
};

use crate::{
    context::{Context, Symbol},
    field::{
        TryExprFrom,
        complex::{C, exact_parts},
        real::R,
    },
    solve::polynomial::{PolynomialRoots, split_complex},
    term::{Expand, Normalize, Term},
};

use super::{
    ln_abs,
    poly::{Poly, TermCoefficient},
};

type Complex = C<R<Rational>>;

/// The integral of `{$num / den$}`, `den` being monic, or `None` if the roots of an irreducible factor of the
/// denominator can't be computed.
pub(super) fn integrate(num: &Poly, den: &Poly, x: Symbol) -> Option<Expr> {
    let (quo, rem) = num.div_rem(den);
    let mut res = quo.antiderivative().to_term(x);
    if rem.is_zero() {
        return Some(res);
    }
    let (rational, a, d) = hermite_reduce(rem, den, x);
    res += rational;
    if a.is_zero() {
        return Some(res);
    }
    // `{$A / D$}` stays proper after the reduction
    let d_prime = d.derivative();
    for q in factor(&d, x) {
        let p = a.mul(&d_prime.inverse_mod(&q)).rem(&q);
        res += if p.degree() == 0 {
            value(p.leading()) * ln_abs(&q.to_term(x), x)
        } else {
            log_part(&q, &p, x)?
        };
    }
    Some(res)
}

/// The Hermite reduction of `{$A / D$}` (quadratic version), returning `{$(g, A', D')$}` with
/// `{$integral A / D = g + integral A' / D'$}` and `D'` square-free.
fn hermite_reduce(mut a: Poly, d: &Poly, x: Symbol) -> (Expr, Poly, Poly) {
    let mut g = zero();
    let mut d = d.clone();
    let factors = d.square_free();
    for (i, v) in factors.iter().enumerate().skip(1) {
        if v.degree() == 0 {
            continue;
        }
        let i = i + 1;
        let u = d.exact_div(&v.pow(i));
        let uv = u.mul(&v.derivative());
        for j in (1..i).rev() {
            let j_rational = Rational::from(j);
            // `{$B U V' + C V = -A / j$}`
            let (b, c) = uv.diophantine(v, &a.scale(&-(Rational::ONE / &j_rational)));
            g += b.to_term(x) / v.to_term(x).pow(&value(j_rational.clone()));
            a = c.scale(&-j_rational).sub(&u.mul(&b.derivative()));
        }
        d = u.mul(v);
    }
    (g, a, d)
}

/// The monic irreducible factors over `{$QQ$}` (or `{$QQ(i)$}`) of a square-free polynomial.
pub fn factor<F: TermCoefficient>(d: &Poly<F>, x: Symbol) -> Vec<Poly<F>> {
    if d.degree() <= 1 {
        return vec![d.monic()];
    }
    let factored = F::factor_term(&d.to_term(x));
    let factors = match &factored {
        Term::Mul(mul) => mul.iter().cloned().collect(),
        _ => vec![factored],
    };
    let res: Option<Vec<_>> = factors
        .iter()
        .filter(|factor| !matches!(factor, Term::Value(_)))
        .map(|factor| Poly::from_term_over(factor, x).map(|p| p.monic()))
        .collect();
    // Factors are polynomials of the variable, fall back to the whole polynomial otherwise
    res.filter(|factors| factors.iter().map(Poly::degree).sum::<usize>() == d.degree())
        .unwrap_or_else(|| vec![d.monic()])
}

/// `{$sum_(q(r) = 0) p(r) ln(x - r)$}` written with real functions, for an irreducible `q`.
fn log_part(q: &Poly, p: &Poly, x: Symbol) -> Option<Expr> {
    let complex = |c: &Rational| Term::constant([c.clone(), Rational::ZERO], C);
    let coefficients: Vec<_> = q.coefficients().iter().map(complex).collect();
    let roots = <Complex as PolynomialRoots>::roots(&coefficients)?;
    if roots.len() != q.degree() {
        return None;
    }
    let mut res = zero();
    for root in &roots {
        let (u, v) = split(root)?;
        let residue = p
            .coefficients()
            .iter()
            .rev()
            .fold(Term::zero(C), |res, c| res * root + complex(c));
        let (alpha, beta) = split(&residue)?;
        match constant_sign(&v)? {
            Ordering::Less => {}
            Ordering::Equal => res += alpha * ln_abs(&(variable(x) - u), x),
            Ordering::Greater => {
                let shifted = variable(x) - &u;
                let mut modulus = (&u * &u + &v * &v).expand();
                // Roots with trigonometric parts, like `{$cos((2 pi) / 7) + i sin((2 pi) / 7)$}`
                if split_complex(root).is_none() {
                    modulus = fun(Context::SIMPLIFY, modulus);
                }
                let norm = (variable(x) * (variable(x) - value(Rational::from(2)) * &u) + modulus)
                    .expand();
                res += alpha * fun(Context::LN, norm)
                    - value(Rational::from(2)) * beta * fun(Context::ATAN, shifted / v);
            }
        }
    }
    Some(res)
}

/// The real and imaginary parts of a complex constant, made of real radicals or of real functions like
/// `{$cos((2 pi) / 7)$}`.
pub fn split(t: &Term<Complex>) -> Option<(Expr, Expr)> {
    let real = |t: Term<Complex>| {
        TryExprFrom::<Complex>::try_from_expr(&R, t)
            .ok()
            .map(|t| t.normalize())
    };
    split_complex(t)
        .and_then(|(re, im)| Some((real(re)?, real(im)?)))
        .or_else(|| exact_parts(t))
}

/// The distinct rational roots of a non-zero polynomial, and whether it is a product of linear factors.
pub fn rational_roots(p: &Poly, x: Symbol) -> (Vec<Rational>, bool) {
    let mut roots = vec![];
    let mut split = true;
    for square_free in p.square_free() {
        if square_free.degree() == 0 {
            continue;
        }
        for q in factor(&square_free, x) {
            if q.degree() == 1 {
                roots.push(-q.coefficient(0) / q.coefficient(1));
            } else {
                split = false;
            }
        }
    }
    (roots, split)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{parse, symbol};

    #[test]
    fn hermite_and_logs() {
        let x = symbol!("x");
        let integrate = |f: &str| {
            let (num, den) = super::super::poly::rational_function(&parse!(f, R), x).unwrap();
            integrate(&num, &den, x).unwrap()
        };
        assert_eq!(integrate("1/x^2"), parse!("-1/x", R));
        assert_eq!(integrate("2*x/(x^2+1)"), parse!("ln(x^2+1)", R));
        assert_eq!(integrate("1/(x^2+1)"), parse!("atan(x)", R));
    }
}
