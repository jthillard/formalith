//! The Risch algorithm for transcendental elementary functions (Bronstein, *Symbolic Integration I*).
//!
//! The integrand is written as an element `f` of a tower `{$K_n = QQ(x, t_2, ..., t_n)$}` of exponentials and
//! logarithms (see [`tower`]), then integrated in `{$K_(n - 1)(t_n)$}`:
//! 1. the Hermite reduction gives the rational part and a remaining `{$h = a / d$}` with `d` square-free and
//!    normal, plus a polynomial `r` in `{$t_n$}` (and `{$1 / t_n$}` for an exponential),
//! 2. the residues of `h` are the roots of `{$R(z) = "res"_t(d, a - z D d)$}`: when one isn't a constant, `f` has
//!    no elementary integral, otherwise each rational residue `{$alpha$}` gives `{$alpha ln gcd(d, a - alpha D d)$}`,
//! 3. the remaining polynomial `{$p = sum p_i t^i$}` is integrated coefficient by coefficient: for
//!    `{$t = ln u$}`, `{$integral p_m$}` must be in `{$K_(n - 1)$}` up to a constant times `t` (limited
//!    integration), for `{$t = e^a$}`, `{$p_i t^i$}` is the derivative of `{$y t^i$}` with `{$D y + i D a y = p_i$}`
//!    (Risch differential equation, see [`rde`]), and `{$p_0$}` is integrated recursively in `{$K_(n - 1)$}`.
//!
//! Steps that the implementation doesn't decide (irrational residues outside of `{$QQ(x)$}`, cancellation cases
//! of the differential equation) make it fail with [`RischError::Unsupported`], so
//! [`RischError::NonElementary`] is a proof.

mod field;
mod rde;
mod tower;

use malachite::{Rational, base::num::basic::traits::Zero};

use crate::{
    context::Symbol,
    field::real::expr::{value, zero},
    term::Normalize,
};

use super::{
    Expr, ln_abs,
    poly::{Coefficient, Poly},
    rational, trig,
};

use field::{EPoly, Elem};
use tower::{Kind, Tower};

/// Maximum degree of the denominators whose residues are computed.
const MAX_DEGREE: usize = 12;

/// Why the Risch algorithm doesn't give an antiderivative.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum RischError {
    /// The integral is proved not to be elementary.
    NonElementary,
    /// The integrand is not in a supported tower, or a step isn't implemented.
    Unsupported,
}

pub(super) type RischResult<T> = Result<T, RischError>;

/// An antiderivative of `f` with respect to `x`.
///
/// # Errors
/// See [`RischError`].
pub(super) fn integrate(f: &Expr, x: Symbol) -> RischResult<Expr> {
    let f = trig::hyperbolic_as_exp(f, x).unwrap_or_else(|| f.clone());
    let (tower, e) = Tower::build(x, &f)?;
    let integral = Risch { tower: &tower }.integrate(&e)?;
    Ok((tower.to_term(&integral.part) + integral.logs).normalize())
}

/// `f` written canonically as an element of its tower, with the level of that element (0 for a rational number, 1
/// for a rational function of `x`), `None` when `f` doesn't fit in a tower.
pub(super) fn canonical(f: &Expr, x: Symbol) -> Option<(Expr, usize)> {
    let f = trig::hyperbolic_as_exp(f, x).unwrap_or_else(|| f.clone());
    let (tower, e) = Tower::build(x, &f).ok()?;
    Some((tower.to_term(&e).normalize(), e.level()))
}

/// An integral `{$g + L$}`, `g` being an element of the tower and `L` an expression, a sum of logarithms (and
/// arctangents) of elements of the tower.
struct Integral {
    part: Elem,
    logs: Expr,
}

struct Risch<'a> {
    tower: &'a Tower,
}

impl Risch<'_> {
    fn d(&self, f: &Elem) -> Elem {
        self.tower.derivative(f)
    }

    fn d_poly(&self, p: &EPoly, level: usize) -> EPoly {
        self.tower.derivative_poly(p, level)
    }

    /// The integral of `f` in the field of its level.
    fn integrate(&self, f: &Elem) -> RischResult<Integral> {
        match f.level() {
            0 => Ok(Integral {
                part: f.times(&Elem::generator(1)),
                logs: zero(),
            }),
            1 => self.integrate_rational(f),
            level => self.integrate_transcendental(f, level),
        }
    }

    /// The integral of a rational function of `x`, the logarithmic part being computed by
    /// [`rational::integrate`].
    fn integrate_rational(&self, f: &Elem) -> RischResult<Integral> {
        let (a, d) = f.fraction(1);
        let (g, h, r) = self.hermite(&a, &d, 1);
        let r = to_rational_poly(&r.fraction(1).0).antiderivative();
        let part = g.plus(&Elem::from_poly(1, from_rational_poly(&r)));
        let logs = if h.is_zero() {
            zero()
        } else {
            let (num, den) = h.fraction(1);
            rational::integrate(
                &to_rational_poly(&num),
                &to_rational_poly(&den),
                self.tower.x(),
            )
            .ok_or(RischError::Unsupported)?
        };
        Ok(Integral { part, logs })
    }

    /// The integral of `f` of level at least 2.
    fn integrate_transcendental(&self, f: &Elem, level: usize) -> RischResult<Integral> {
        let (a, d) = f.fraction(level);
        let (g, h, r) = self.hermite(&a, &d, level);
        let mut part = g;
        let mut logs = zero();
        // `{$p = h - sum alpha D S / S + r$}`
        let mut p = h.plus(&r);
        for (alpha, s) in self.residue_reduce(&h, level)? {
            let s = Elem::from_poly(level, s);
            let alpha_elem = Elem::rational(alpha.clone());
            p = p.minus(&alpha_elem.times(&self.d(&s).divide(&s)));
            logs = logs + value(alpha) * ln_abs(&self.tower.to_term(&s), self.tower.x());
        }
        let (num, den) = p.fraction(level);
        let rest = match self.tower.kind(level) {
            Kind::Ln(_) => {
                if !den.is_one() {
                    return Err(RischError::Unsupported);
                }
                let (q, rest) = self.primitive_polynomial(num, level)?;
                part = part.plus(&q);
                rest
            }
            Kind::Exp(_) => {
                let shift = den.degree();
                if den != EPoly::monomial(Elem::one(), shift) {
                    return Err(RischError::Unsupported);
                }
                let t = Elem::generator(level);
                let eta = self.tower.eta(level);
                let mut rest = Elem::zero();
                for (j, c) in num.coefficients().iter().enumerate() {
                    if c.is_zero() {
                        continue;
                    }
                    let i =
                        i64::try_from(j).unwrap_or(i64::MAX) - i64::try_from(shift).unwrap_or(0);
                    if i == 0 {
                        rest = c.clone();
                        continue;
                    }
                    // `{$D(y t^i) = (D y + i D a y) t^i$}`
                    let y = self
                        .rde(&eta.times(&Elem::integer(i)), c, level - 1)?
                        .ok_or(RischError::NonElementary)?;
                    part = part.plus(&y.times(&t.pow(i)));
                }
                rest
            }
            Kind::X => unreachable!("x is the level 1"),
        };
        let sub = self.integrate(&rest)?;
        Ok(Integral {
            part: part.plus(&sub.part),
            logs: logs + sub.logs,
        })
    }

    /// The Hermite reduction of `{$a / d$}` (Mack's linear version), `d` monic: `{$(g, h, r)$}` with
    /// `{$a / d = D g + h + r$}`, `h` proper with a square-free normal denominator, and `r` a polynomial in `t`
    /// (and `{$1 / t$}` for an exponential).
    fn hermite(&self, input: &EPoly, d: &EPoly, level: usize) -> (Elem, Elem, Elem) {
        let (q, rem) = input.div_rem(d);
        let (dn, ds) = self.tower.split_factor(d, level);
        // `{$rem / d = b / d_s + c / d_n$}`
        let (b, mut a) = if ds.degree() == 0 {
            (EPoly::zero(), rem)
        } else {
            dn.diophantine(&ds, &rem)
        };
        let special = Elem::from_fraction(level, &b, &ds);
        let mut g = Elem::zero();
        let mut dm = dn.gcd(&self.d_poly(&dn, level));
        let d_star = dn.exact_div(&dm);
        while dm.degree() > 0 {
            let ddm = self.d_poly(&dm, level);
            let dm2 = dm.gcd(&ddm);
            let dms = dm.exact_div(&dm2);
            let e = d_star.mul(&ddm).exact_div(&dm);
            let (b, c) = e.neg().diophantine(&dms, &a);
            a = c.sub(&self.d_poly(&b, level).mul(&d_star.exact_div(&dms)));
            g = g.plus(&Elem::from_fraction(level, &b, &dm));
            dm = dm2;
        }
        let (q2, r) = a.div_rem(&d_star);
        let h = Elem::from_fraction(level, &r, &d_star);
        let r = Elem::from_poly(level, q.add(&q2)).plus(&special);
        debug_assert_eq!(
            self.d(&g).plus(&h).plus(&r),
            Elem::from_fraction(level, input, d),
            "Hermite reduction"
        );
        (g, h, r)
    }

    /// The rational residues `{$alpha$}` of `h` with `{$S = gcd(d, a - alpha D d)$}`, for `{$h = a / d$}` with
    /// `d` square-free and normal.
    ///
    /// # Errors
    /// [`RischError::NonElementary`] when a residue isn't a constant, [`RischError::Unsupported`] when one is
    /// irrational.
    fn residue_reduce(&self, h: &Elem, level: usize) -> RischResult<Vec<(Rational, EPoly)>> {
        if h.is_zero() {
            return Ok(vec![]);
        }
        let (a, d) = h.fraction(level);
        if d.degree() > MAX_DEGREE {
            return Err(RischError::Unsupported);
        }
        let dd = self.d_poly(&d, level);
        let r = self.resultant_in_z(&d, &a, &dd);
        let r = r.monic();
        let r: Option<Vec<_>> = r
            .coefficients()
            .iter()
            .map(|c| c.as_rational().cloned())
            .collect();
        let r = Poly::new(r.ok_or(RischError::NonElementary)?);
        let (roots, split) = rational_roots(&r, self.tower.x());
        if !split {
            return Err(RischError::Unsupported);
        }
        Ok(roots
            .into_iter()
            .map(|alpha| {
                let s = d.gcd(&a.sub(&dd.scale(&Elem::rational(alpha.clone()))));
                (alpha, s)
            })
            .collect())
    }

    /// `{$R(z) = "res"_t(d, a - z b)$}`, interpolated from its values at `{$z = 0, ..., deg d$}`.
    fn resultant_in_z(&self, d: &EPoly, a: &EPoly, b: &EPoly) -> EPoly {
        let points: Vec<_> = (0..=d.degree()).map(|z| Rational::from(z)).collect();
        let values: Vec<_> = points
            .iter()
            .map(|z| d.resultant(&a.sub(&b.scale(&Elem::rational(z.clone())))))
            .collect();
        interpolate(&points, &values)
    }

    /// `{$(q, p_0)$}` with `{$p = D q + p_0$}`, `{$p_0$}` of a lower level, for a polynomial `p` in
    /// `{$t = ln u$}`.
    fn primitive_polynomial(&self, mut p: EPoly, level: usize) -> RischResult<(Elem, Elem)> {
        let t = Elem::generator(level);
        let eta = self.tower.eta(level);
        let mut q = Elem::zero();
        while p.degree() > 0 {
            let m = p.degree();
            let (b, c) = self.limited_integrate(&p.leading(), &eta, level - 1)?;
            let m_elem = i64::try_from(m).map_err(|_| RischError::Unsupported)?;
            // `{$q_0 = c t^(m + 1) / (m + 1) + b t^m$}`
            let q0 = Elem::rational(c / Rational::from(m_elem + 1))
                .times(&t.pow(m_elem + 1))
                .plus(&b.times(&t.pow(m_elem)));
            q = q.plus(&q0);
            let (num, den) = Elem::from_poly(level, p)
                .minus(&self.d(&q0))
                .fraction(level);
            if !den.is_one() || (!num.is_zero() && num.degree() >= m) {
                return Err(RischError::Unsupported);
            }
            p = num;
        }
        Ok((q, p.coefficient(0)))
    }

    /// `{$(b, c)$}` with `{$a = D b + c eta$}`, `b` in `{$K_k$}` and `c` constant, `{$eta = D t$}` being the
    /// derivative of a logarithm `t` over `{$K_k$}`.
    ///
    /// # Errors
    /// [`RischError::NonElementary`] when there are none.
    fn limited_integrate(
        &self,
        a: &Elem,
        eta: &Elem,
        level: usize,
    ) -> RischResult<(Elem, Rational)> {
        let integral = self.integrate(a)?;
        let c = a.minus(&self.d(&integral.part)).divide(eta);
        match c.as_rational() {
            Some(c) => Ok((integral.part, c.clone())),
            // In `{$QQ(x)$}`, the derivative of `{$b - g$}` would have simple poles, so it is 0
            None if level == 1 => Err(RischError::NonElementary),
            None => Err(RischError::Unsupported),
        }
    }
}

/// The polynomial of `{$QQ[x]$}` with the given coefficients of level 0.
fn to_rational_poly(p: &EPoly) -> Poly {
    p.map(|c| c.as_rational().cloned().unwrap_or(Rational::ZERO))
}

fn from_rational_poly(p: &Poly) -> EPoly {
    p.map(|c| Elem::rational(c.clone()))
}

/// The polynomial taking the given values at the given distinct points (Lagrange interpolation).
fn interpolate(points: &[Rational], values: &[Elem]) -> EPoly {
    let mut res = EPoly::zero();
    for (j, (zj, vj)) in points.iter().zip(values).enumerate() {
        if vj.is_zero() {
            continue;
        }
        let mut basis = Poly::<Rational>::one();
        for (k, zk) in points.iter().enumerate() {
            if k != j {
                let factor = Poly::new(vec![-zk.clone(), Rational::from(1)]);
                basis = basis.mul(&factor).scale(&(Rational::from(1) / (zj - zk)));
            }
        }
        res = res.add(&from_rational_poly(&basis).scale(vj));
    }
    res
}

/// The distinct rational roots of a non-zero polynomial, and whether it is a product of linear factors.
fn rational_roots(p: &Poly, x: Symbol) -> (Vec<Rational>, bool) {
    let mut roots = vec![];
    let mut split = true;
    for factor in p.square_free() {
        if factor.degree() == 0 {
            continue;
        }
        for q in rational::factor(&factor, x) {
            if q.degree() == 1 {
                roots.push(-q.coefficient(0) / q.coefficient(1));
            } else {
                split = false;
            }
        }
    }
    (roots, split)
}
