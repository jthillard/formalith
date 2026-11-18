//! Integration of rational functions with rational coefficients.
//!
//! After removing the polynomial part, the Hermite reduction gives the rational part of the integral and a
//! remaining `{$A / D$}` with `D` square-free, whose integral is a sum of logarithms. `D` is factored over
//! `{$QQ$}`: for each irreducible factor `q`, the residues of `{$A / D$}` at the roots `r` of `q` are
//! `{$p(r)$}` with `{$p = A D'^(-1) mod q$}`. They are all equal to `c` when `p` is a constant, giving
//! `{$c ln|q|$}`. Otherwise, the roots of `q` are computed with radicals in `{$CC$}`: a real root gives
//! `{$p(r) ln|x - r|$}`, and a pair of conjugate roots `{$u plus.minus i v$}` with `{$p(u + i v) = alpha + i beta$}`
//! gives `{$alpha ln((x - u)^2 + v^2) - 2 beta arctan((x - u) / v)$}`.

use std::cmp::Ordering;

use malachite::{
    Rational,
    base::num::basic::traits::{One, Zero},
};

use crate::{
    context::{Context, Symbol},
    field::{TryExprFrom, complex::C, real::R},
    limit::{fun, value, variable},
    solve::polynomial::{PolynomialRoots, split_complex},
    term::{Expand, Normalize, Term},
};

use super::{Expr, constant_sign, ln_abs, poly::Poly};

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
    let mut g = Term::zero(R);
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

/// The monic irreducible factors over `{$QQ$}` of a square-free polynomial.
pub(super) fn factor(d: &Poly, x: Symbol) -> Vec<Poly> {
    if d.degree() <= 1 {
        return vec![d.monic()];
    }
    let factored = d.to_term(x).factor();
    let factors = match &factored {
        Term::Mul(mul) => mul.iter().cloned().collect(),
        _ => vec![factored],
    };
    let res: Option<Vec<_>> = factors
        .iter()
        .filter(|factor| !matches!(factor, Term::Value(_)))
        .map(|factor| Poly::from_term(factor, x).map(|p| p.monic()))
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
    let mut res = Term::zero(R);
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
                let shifted = variable(x) - u;
                let norm = (&shifted * &shifted + &v * &v).expand();
                res += alpha * fun(Context::LN, norm)
                    - value(Rational::from(2)) * beta * fun(Context::ATAN, shifted / v);
            }
        }
    }
    Some(res)
}

/// The real and imaginary parts of a complex expression made of real radicals.
fn split(t: &Term<Complex>) -> Option<(Expr, Expr)> {
    let real = |t: Term<Complex>| {
        TryExprFrom::<Complex>::try_from_expr(&R, t)
            .ok()
            .map(|t| t.normalize())
    };
    let (re, im) = split_complex(t)?;
    Some((real(re)?, real(im)?))
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
