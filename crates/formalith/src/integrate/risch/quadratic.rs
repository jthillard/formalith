//! Residues of the Rothstein-Trager resultant at the roots `{$alpha$}` of an irreducible quadratic factor
//! `{$z^2 + p z + q$}` over `{$QQ$}`.
//!
//! The logarithms `{$alpha ln S(alpha, t)$}` need `{$S = gcd(d, a - alpha D d)$}`, a gcd in `{$K(alpha)[t]$}`,
//! where `{$K(alpha) = K[z] / (z^2 + p z + q)$}` stays a field since `K` is a transcendental extension of `{$QQ$}`.
//! It is written `{$S(alpha, t) = s_0 + alpha s_1$}` with `{$s_0, s_1 in K[t]$}`, and the sum over both roots is
//! made real:
//! - for real roots, `{$alpha ln|s_0 + alpha s_1|$}` with square roots,
//! - for complex roots `{$u plus.minus i v$}`, with `{$A = s_0 + u s_1$}` and `{$B = v s_1$}`,
//!   `{$u ln(A^2 + B^2) + v i ln((A + i B) / (A - i B))$}`, the second term being written with arctangents of
//!   elements of `{$K(t)$}` by Rioboo's algorithm, so the antiderivative has no jumps where `A` vanishes. Since
//!   `{$v^2$}` is rational, every step stays in `{$K[t]$}`, `B` being kept as `{$v tilde(B)$}`.

use malachite::Rational;

use crate::{
    context::{Context, Symbol},
    field::real::expr::{Expr, fun, sqrt, value, zero},
};

use super::{super::ln_abs, EPoly, Elem, tower::Tower};
use crate::polynom::dense::Coefficient;

/// The field `{$K(alpha)$}`, `{$alpha$}` being a root of `{$z^2 + p z + q$}`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct Quadratic {
    pub p: Rational,
    pub q: Rational,
}

/// `{$a + b alpha$}`.
#[derive(Clone, Debug)]
struct QElem {
    a: Elem,
    b: Elem,
}

impl QElem {
    fn is_zero(&self) -> bool {
        self.a.is_zero() && self.b.is_zero()
    }

    fn minus(&self, other: &Self) -> Self {
        Self {
            a: self.a.minus(&other.a),
            b: self.b.minus(&other.b),
        }
    }
}

impl Quadratic {
    fn elem(r: &Rational) -> Elem {
        Elem::rational(r.clone())
    }

    /// The discriminant `{$p^2 - 4 q$}`.
    pub(super) fn discriminant(&self) -> Rational {
        &self.p * &self.p - Rational::from(4) * &self.q
    }

    fn times(&self, x: &QElem, y: &QElem) -> QElem {
        // `{$alpha^2 = -p alpha - q$}`
        let bb = x.b.times(&y.b);
        QElem {
            a: x.a.times(&y.a).minus(&bb.times(&Self::elem(&self.q))),
            b: x.a
                .times(&y.b)
                .plus(&x.b.times(&y.a))
                .minus(&bb.times(&Self::elem(&self.p))),
        }
    }

    /// The conjugate `{$a + b overline(alpha) = a - p b - b alpha$}`.
    fn conj(&self, x: &QElem) -> QElem {
        QElem {
            a: x.a.minus(&x.b.times(&Self::elem(&self.p))),
            b: x.b.negate(),
        }
    }

    /// The norm `{$(a + b alpha) (a + b overline(alpha)) = a^2 - p a b + q b^2$}`.
    fn norm(&self, x: &QElem) -> Elem {
        x.a.times(&x.a)
            .minus(&Self::elem(&self.p).times(&x.a).times(&x.b))
            .plus(&Self::elem(&self.q).times(&x.b).times(&x.b))
    }

    fn inverse(&self, x: &QElem) -> QElem {
        let conj = self.conj(x);
        let norm = self.norm(x).inverse();
        QElem {
            a: conj.a.times(&norm),
            b: conj.b.times(&norm),
        }
    }

    /// The remainder of `r` by `b`, polynomials by increasing degree without trailing zeros, `b` non-zero.
    fn rem(&self, mut r: Vec<QElem>, b: &[QElem]) -> Vec<QElem> {
        let lead = self.inverse(b.last().expect("Non-zero divisor"));
        while r.len() >= b.len() {
            let shift = r.len() - b.len();
            let c = self.times(r.last().expect("Non-empty"), &lead);
            for (i, coefficient) in b.iter().enumerate() {
                r[shift + i] = r[shift + i].minus(&self.times(&c, coefficient));
            }
            r.pop();
            trim(&mut r);
        }
        r
    }

    /// The monic `{$S = gcd(d, a - alpha b)$}` in `{$K(alpha)[t]$}`, as `{$(s_0, s_1)$}` with
    /// `{$S = s_0 + alpha s_1$}`.
    pub(super) fn gcd(&self, d: &EPoly, a: &EPoly, b: &EPoly) -> (EPoly, EPoly) {
        let mut r0: Vec<QElem> = d
            .coefficients()
            .iter()
            .map(|c| QElem {
                a: c.clone(),
                b: Elem::zero(),
            })
            .collect();
        let n = a.coefficients().len().max(b.coefficients().len());
        let mut r1: Vec<QElem> = (0..n)
            .map(|i| QElem {
                a: a.coefficient(i),
                b: b.coefficient(i).negate(),
            })
            .collect();
        trim(&mut r1);
        while !r1.is_empty() {
            let r = self.rem(r0, &r1);
            (r0, r1) = (r1, r);
        }
        let lead = self.inverse(r0.last().expect("Non-zero gcd"));
        let monic: Vec<_> = r0.iter().map(|c| self.times(c, &lead)).collect();
        (
            EPoly::new(monic.iter().map(|c| c.a.clone()).collect()),
            EPoly::new(monic.iter().map(|c| c.b.clone()).collect()),
        )
    }

    /// `{$sum_alpha alpha D S(alpha) / S(alpha)$}` over both roots, an element of `{$K(t)$}`: the trace of
    /// `{$alpha D S overline(S) / N(S)$}`.
    pub(super) fn trace_log_derivative(
        &self,
        tower: &Tower,
        s0: &EPoly,
        s1: &EPoly,
        level: usize,
    ) -> Elem {
        let (s0, s1) = (Elem::from_poly(level, s0), Elem::from_poly(level, s1));
        let (ds0, ds1) = (tower.derivative(&s0), tower.derivative(&s1));
        let s = QElem { a: s0, b: s1 };
        // `{$alpha (D s_0 + alpha D s_1) = -q D s_1 + alpha (D s_0 - p D s_1)$}`
        let x = QElem {
            a: ds1.times(&Self::elem(&-&self.q)),
            b: ds0.minus(&ds1.times(&Self::elem(&self.p))),
        };
        let y = self.times(&x, &self.conj(&s));
        // `{$"Tr"(a + b alpha) = 2 a - p b$}`
        let trace =
            y.a.times(&Elem::integer(2))
                .minus(&y.b.times(&Self::elem(&self.p)));
        trace.divide(&self.norm(&s))
    }

    /// `{$sum_alpha alpha ln S(alpha, t)$}` over both roots, written with real functions.
    pub(super) fn logs(
        &self,
        tower: &Tower,
        s0: &EPoly,
        s1: &EPoly,
        level: usize,
        x: Symbol,
    ) -> Expr {
        let term = |p: &EPoly| tower.poly_to_term(p, level);
        let u = -&self.p / Rational::from(2);
        if s1.is_zero() {
            // `{$(alpha + overline(alpha)) ln|s_0|$}`
            return value(-&self.p) * ln_abs(&term(s0), x);
        }
        let discriminant = self.discriminant();
        if discriminant > 0 {
            let root = sqrt(&value(discriminant)) / value(Rational::from(2));
            return [1, -1].into_iter().fold(zero(), |res, sign| {
                let alpha = value(u.clone()) + value(Rational::from(sign)) * &root;
                res + alpha.clone() * ln_abs(&(term(s0) + alpha * term(s1)), x)
            });
        }
        // `{$alpha = u plus.minus i v$}`, `{$v^2 = w$}`
        let w = &self.q - &u * &u;
        let a = s0.add(&s1.scale(&Self::elem(&u)));
        let norm = a.mul(&a).add(&s1.mul(s1).scale(&Self::elem(&w)));
        let v = sqrt(&value(w.clone()));
        value(u) * fun(Context::LN, term(&norm))
            + v.clone() * log_to_atan(tower, &a, s1, &w, &v, level)
    }
}

/// `{$i ln((A + i B) / (A - i B))$}` up to a constant, for `{$B = v tilde(B)$}` with `{$v^2 = w$}`, as a sum of
/// `{$2 atan$}` of elements of `{$K(t)$}` without poles where `{$A^2 + B^2$}` doesn't vanish (Rioboo).
fn log_to_atan(tower: &Tower, a: &EPoly, b: &EPoly, w: &Rational, v: &Expr, level: usize) -> Expr {
    let two = value(Rational::from(2));
    let atan = |num: &EPoly, den: &EPoly| {
        two.clone()
            * fun(
                Context::ATAN,
                tower.to_term(&Elem::from_fraction(level, num, den)) / v,
            )
    };
    let (quo, rem) = a.div_rem(b);
    if rem.is_zero() {
        return atan(&quo, &EPoly::one());
    }
    if a.degree() < b.degree() {
        // `{$(-B, A) = (-w tilde(B), v A) / v$}`
        return log_to_atan(tower, &b.scale(&Elem::rational(-w)), a, w, v, level);
    }
    // `{$s tilde(B) + t A = G$}`, so `{$B D - A C = G$}` with `{$D = s / v$}`, `{$C = -t$}`, and
    // `{$(A D + B C) / G = (A s - w tilde(B) t) / (v G)$}`, then `{$(D, C)$}` is proportional to `{$(s, -v t)$}`
    let (s, t, g) = b.extended_gcd(a);
    let c = t.neg();
    let num = a.mul(&s).add(&b.mul(&c).scale(&Elem::rational(w.clone())));
    atan(&num, &g) + log_to_atan(tower, &s, &c, w, v, level)
}

fn trim(p: &mut Vec<QElem>) {
    while p.last().is_some_and(QElem::is_zero) {
        p.pop();
    }
}
