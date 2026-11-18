//! The Risch differential equation `{$D y + f y = g$}`, for `f`, `g` and `y` in `{$K_k = K_(k - 1)(t)$}`
//! (Bronstein, chapter 6).
//!
//! The denominator of `y` is bounded (weak normalization, normal and special denominators), then its numerator
//! is a polynomial of bounded degree, found by the SPDE reduction and the non-cancellation cases. Cancellation
//! cases are solved by recursion on the coefficients, but their failure isn't a proof, like a few degree bounds
//! relying on unimplemented structure theorems: such undecided cases are [`RischError::Unsupported`].

use malachite::Rational;

use super::{
    Kind, Risch, RischError, RischResult,
    field::{EPoly, Elem},
    rational_roots,
    tower::sample_points,
};
use crate::polynom::dense::{Coefficient, Poly};

/// Maximum degree bound of a polynomial solution.
const MAX_BOUND: i64 = 40;
/// The degree of the zero polynomial.
const ZERO_DEGREE: i64 = i64::MIN / 4;

/// The degree of `p`, [`ZERO_DEGREE`] for 0.
fn degree(p: &EPoly) -> i64 {
    if p.is_zero() {
        ZERO_DEGREE
    } else {
        i64::try_from(p.degree()).unwrap_or(i64::MAX)
    }
}

fn to_usize(n: i64) -> usize {
    usize::try_from(n).unwrap_or(0)
}

/// The integer `r`, if it is one.
fn integer(r: &Rational) -> Option<i64> {
    i64::try_from(r).ok()
}

impl Risch<'_> {
    /// A solution in `{$K_k$}` of `{$D y + f y = g$}`, `None` if there is none.
    ///
    /// # Errors
    /// [`RischError::Unsupported`] when it can't be decided.
    pub(super) fn rde(&self, f: &Elem, g: &Elem, level: usize) -> RischResult<Option<Elem>> {
        if g.is_zero() {
            return Ok(Some(Elem::zero()));
        }
        if level == 0 {
            return Ok((!f.is_zero()).then(|| g.divide(f)));
        }
        let mut sure = true;
        match self.solve_rde(f, g, level, &mut sure)? {
            Some(y) if self.d(&y).plus(&f.times(&y)) == *g => Ok(Some(y)),
            Some(_) => Err(RischError::Unsupported),
            None if sure => Ok(None),
            None => Err(RischError::Unsupported),
        }
    }

    /// A solution of `{$D y + f y = g$}`, `sure` being set to `false` when `None` isn't a proof.
    fn solve_rde(
        &self,
        f: &Elem,
        g: &Elem,
        level: usize,
        sure: &mut bool,
    ) -> RischResult<Option<Elem>> {
        // `{$z = q y$}` with `{$D z + (f - D q / q) z = q g$}`
        let q = self.weak_normalizer(f, level)?;
        let q_elem = Elem::from_poly(level, q.clone());
        let f = f.minus(&self.d(&q_elem).divide(&q_elem));
        let g = g.times(&q_elem);
        let Some((a, b, c, h)) = self.normal_denominator(&f, &g, level) else {
            return Ok(None);
        };
        let (a, b, c, hs) = self.special_denominator(&a, &b, &c, level, sure)?;
        let n = self.bound_degree(&a, &b, &c, level, sure)?;
        let Some((b, c, n, alpha, beta)) = self.spde(a, b, c, n, level) else {
            return Ok(None);
        };
        let y = if c.is_zero() {
            EPoly::zero()
        } else {
            match self.solve_polynomial(&b, &c, n, level, sure)? {
                Some(y) => y,
                None => return Ok(None),
            }
        };
        let num = alpha.mul(&y).add(&beta);
        Ok(Some(Elem::from_fraction(level, &num, &h.mul(&hs).mul(&q))))
    }

    /// A polynomial `q` such that `{$f - D q / q$}` is weakly normalized: its simple normal poles have no
    /// positive integer residue.
    fn weak_normalizer(&self, f: &Elem, level: usize) -> RischResult<EPoly> {
        let (a, d) = f.fraction(level);
        let (dn, _) = self.tower.split_factor(&d, level);
        let g = dn.gcd(&dn.derivative());
        let d_star = dn.exact_div(&g);
        let d1 = d_star.exact_div(&d_star.gcd(&g));
        if d1.degree() == 0 {
            return Ok(EPoly::one());
        }
        // `{$f = a_1 / d_1 + ...$}`, the residues at the roots of `{$d_1$}` being the roots of `r`
        let (a1, _) = d.exact_div(&d1).diophantine(&d1, &a);
        let dd1 = self.d_poly(&d1, level);
        let r = self.resultant_in_z(&d1, &a1, &dd1);
        let mut q = EPoly::one();
        for n in self.positive_integer_roots(&r)? {
            q = q.mul(&d1.gcd(&a1.sub(&dd1.scale(&Elem::rational(n)))));
        }
        Ok(q)
    }

    /// The positive integer roots of a non-zero polynomial with coefficients in the tower.
    fn positive_integer_roots(&self, r: &EPoly) -> RischResult<Vec<Rational>> {
        if r.is_zero() {
            return Err(RischError::Unsupported);
        }
        let r = r.monic();
        let positive = |n: &Rational| *n > 0 && n.denominator_ref() == &1u32;
        let x = self.tower.x();
        if let Some(q) = r
            .coefficients()
            .iter()
            .map(|c| c.as_rational().cloned())
            .collect::<Option<Vec<_>>>()
        {
            return Ok(rational_roots(&Poly::new(q), x)
                .0
                .into_iter()
                .filter(positive)
                .collect());
        }
        // The constant roots of `r` are roots of `r` evaluated at a point
        for point in sample_points(self.tower.height()).take(8) {
            let Some(values) = r
                .coefficients()
                .iter()
                .map(|c| c.eval(&point))
                .collect::<Option<Vec<_>>>()
            else {
                continue;
            };
            let values = Poly::new(values);
            if values.is_zero() {
                continue;
            }
            return Ok(rational_roots(&values, x)
                .0
                .into_iter()
                .filter(|n| positive(n) && r.eval(&Elem::rational(n.clone())).is_zero())
                .collect());
        }
        Err(RischError::Unsupported)
    }

    /// `{$(a, b, c, h)$}` such that the solutions are `{$y = z / h$}` with `{$a D z + b z = c$}`, `a` being a
    /// polynomial, and `b`, `c` having special denominators, or `None` when there is no solution.
    fn normal_denominator(
        &self,
        f: &Elem,
        g: &Elem,
        level: usize,
    ) -> Option<(EPoly, Elem, Elem, EPoly)> {
        let (_, fd) = f.fraction(level);
        let (_, gd) = g.fraction(level);
        let (dn, _) = self.tower.split_factor(&fd, level);
        let (en, _) = self.tower.split_factor(&gd, level);
        let p = dn.gcd(&en);
        let h = en.gcd(&en.derivative()).div_rem(&p.gcd(&p.derivative())).0;
        if !dn.mul(&h).mul(&h).divisible_by(&en) {
            return None;
        }
        let a = dn.mul(&h);
        let b = Elem::from_poly(level, a.clone())
            .times(f)
            .minus(&Elem::from_poly(level, dn.mul(&self.d_poly(&h, level))));
        let c = Elem::from_poly(level, a.mul(&h)).times(g);
        Some((a, b, c, h))
    }

    /// `{$(A, B, C, h)$}` with polynomials such that the solutions of `{$a D z + b z = c$}` are `{$z = q / h$}`
    /// with `{$A D q + B q = C$}`: a bound on the power of `t` in the denominator for `{$t = e^a$}`.
    fn special_denominator(
        &self,
        a: &EPoly,
        b: &Elem,
        c: &Elem,
        level: usize,
        sure: &mut bool,
    ) -> RischResult<(EPoly, EPoly, EPoly, EPoly)> {
        let poly = |e: &Elem| {
            let (num, den) = e.fraction(level);
            if den.is_one() {
                Ok(num)
            } else {
                Err(RischError::Unsupported)
            }
        };
        if !matches!(self.tower.kind(level), Kind::Exp(_)) {
            return Ok((a.clone(), poly(b)?, poly(c)?, EPoly::one()));
        }
        let order = |e: &Elem| {
            if e.is_zero() {
                return -ZERO_DEGREE;
            }
            let (num, den) = e.fraction(level);
            i64::try_from(num.order_at_zero()).unwrap_or(0)
                - i64::try_from(den.order_at_zero()).unwrap_or(0)
        };
        let (nb, nc) = (order(b), order(c));
        let mut n = 0.min(nc - 0.min(nb));
        let eta = self.tower.eta(level);
        if nb == 0 {
            // `{$alpha = -b(0) / a(0) = D z / z + m eta$}` allows `{$t^(-m)$}` in the denominator
            let alpha = b
                .fraction(level)
                .0
                .coefficient(0)
                .divide(&a.coefficient(0))
                .negate();
            if let Some(m) = log_derivative_multiple(&alpha, &eta, sure) {
                n = n.min(m);
            }
        }
        let big_n = 0.max(-nb).max(n - nc);
        let t = Elem::generator(level);
        let a_elem = Elem::from_poly(level, a.clone());
        let tn = t.pow(big_n);
        let big_a = a.mul(&EPoly::monomial(Elem::one(), to_usize(big_n)));
        let big_b = b
            .plus(&Elem::integer(n).times(&a_elem).times(&eta))
            .times(&tn);
        let big_c = c.times(&t.pow(big_n - n));
        let h = EPoly::monomial(Elem::one(), to_usize(-n));
        Ok((big_a, poly(&big_b)?, poly(&big_c)?, h))
    }

    /// A bound on the degree of the polynomial solutions of `{$a D q + b q = c$}`.
    fn bound_degree(
        &self,
        a: &EPoly,
        b: &EPoly,
        c: &EPoly,
        level: usize,
        sure: &mut bool,
    ) -> RischResult<i64> {
        let (da, db, dc) = (degree(a), degree(b), degree(c));
        let alpha = || b.leading().divide(&a.leading()).negate();
        let eta = self.tower.eta(level);
        let n = match self.tower.kind(level) {
            Kind::X => {
                let mut n = 0.max(dc - db.max(da - 1));
                if db == da - 1
                    && let Some(m) = alpha().as_rational().and_then(integer)
                {
                    n = n.max(m).max(dc - db);
                }
                n
            }
            Kind::Ln(_) => {
                let mut n = if db > da {
                    0.max(dc - db)
                } else {
                    0.max(dc - da + 1)
                };
                if db == da - 1 {
                    // `{$alpha = m D t + D z$}`, `z` in the field below
                    match self.limited_integrate(&alpha(), &eta, level - 1) {
                        Ok((_, m)) => {
                            if let Some(m) = integer(&m) {
                                n = n.max(m);
                            }
                        }
                        Err(RischError::NonElementary) => {}
                        Err(RischError::Unsupported) => *sure = false,
                    }
                } else if db == da {
                    *sure = false;
                }
                n
            }
            Kind::Exp(_) => {
                let mut n = 0.max(dc - db.max(da));
                if da == db
                    && let Some(m) = log_derivative_multiple(&alpha(), &eta, sure)
                {
                    n = n.max(m);
                }
                n
            }
        };
        if n > MAX_BOUND {
            return Err(RischError::Unsupported);
        }
        Ok(n)
    }

    /// The SPDE reduction of `{$a D q + b q = c$}` with `{$deg q <= n$}` to `{$D r + b' r = c'$}` with
    /// `{$deg r <= n'$}` and `{$q = alpha r + beta$}`, as `{$(b', c', n', alpha, beta)$}`, or `None` when there is
    /// no solution.
    #[allow(clippy::type_complexity)]
    fn spde(
        &self,
        mut a: EPoly,
        mut b: EPoly,
        mut c: EPoly,
        mut n: i64,
        level: usize,
    ) -> Option<(EPoly, EPoly, i64, EPoly, EPoly)> {
        let mut alpha = EPoly::one();
        let mut beta = EPoly::zero();
        loop {
            if c.is_zero() {
                return Some((EPoly::zero(), EPoly::zero(), 0, EPoly::zero(), beta));
            }
            if n < 0 {
                return None;
            }
            let g = a.gcd(&b);
            if !c.divisible_by(&g) {
                return None;
            }
            (a, b, c) = (a.exact_div(&g), b.exact_div(&g), c.exact_div(&g));
            if a.degree() == 0 {
                let inverse = a.leading().inverse();
                return Some((b.scale(&inverse), c.scale(&inverse), n, alpha, beta));
            }
            // `{$r b + z a = c$}`
            let (r, z) = b.diophantine(&a, &c);
            b = b.add(&self.d_poly(&a, level));
            c = z.sub(&self.d_poly(&r, level));
            n -= degree(&a);
            beta = beta.add(&alpha.mul(&r));
            alpha = alpha.mul(&a);
        }
    }

    /// A polynomial solution of `{$D q + b q = c$}` with `{$deg q <= n$}`.
    fn solve_polynomial(
        &self,
        b: &EPoly,
        c: &EPoly,
        n: i64,
        level: usize,
        sure: &mut bool,
    ) -> RischResult<Option<EPoly>> {
        let kind = self.tower.kind(level);
        if !b.is_zero() && (matches!(kind, Kind::X) || b.degree() > 0) {
            return Ok(self.no_cancellation(b, c.clone(), n, level));
        }
        match kind {
            Kind::X => {
                // `{$D q = c$}`
                let q = c.antiderivative();
                Ok((degree(&q) <= n).then_some(q))
            }
            _ if b.is_zero() => self.derivative_of_polynomial(c, n, level, sure),
            Kind::Ln(_) => self.cancel_primitive(b, c.clone(), n, level, sure),
            Kind::Exp(_) => self.cancel_exp(b, c.clone(), n, level, sure),
        }
    }

    /// `{$D q + b q = c$}` when the degree of `b q` is larger than the one of `{$D q$}`.
    fn no_cancellation(&self, b: &EPoly, mut c: EPoly, mut n: i64, level: usize) -> Option<EPoly> {
        let mut q = EPoly::zero();
        while !c.is_zero() {
            let m = degree(&c) - degree(b);
            if m < 0 || m > n {
                return None;
            }
            let p = EPoly::monomial(c.leading().divide(&b.leading()), to_usize(m));
            c = c.sub(&self.d_poly(&p, level)).sub(&b.mul(&p));
            q = q.add(&p);
            n = m - 1;
        }
        Some(q)
    }

    /// A polynomial `q` with `{$D q = c$}` and `{$deg q <= n$}`, found by integrating `c`.
    fn derivative_of_polynomial(
        &self,
        c: &EPoly,
        n: i64,
        level: usize,
        sure: &mut bool,
    ) -> RischResult<Option<EPoly>> {
        let c = Elem::from_poly(level, c.clone());
        let integral = match self.integrate(&c) {
            Ok(integral) => integral,
            Err(RischError::NonElementary) => return Ok(None),
            Err(RischError::Unsupported) => return Err(RischError::Unsupported),
        };
        // The logarithms may be `{$c t$}` for `{$t = ln u$}`, or `{$c a$}` for `{$t = e^a$}`
        let w = c.minus(&self.d(&integral.part));
        let y = if w.is_zero() {
            integral.part
        } else {
            let eta = self.tower.eta(level);
            let Some(k) = w.divide(&eta).as_rational().cloned() else {
                *sure = false;
                return Ok(None);
            };
            let k = Elem::rational(k);
            match self.tower.kind(level) {
                Kind::Ln(_) => integral.part.plus(&k.times(&Elem::generator(level))),
                Kind::Exp(a) => integral.part.plus(&k.times(a)),
                Kind::X => unreachable!("Solved directly"),
            }
        };
        let (num, den) = y.fraction(level);
        Ok((den.is_one() && degree(&num) <= n).then_some(num))
    }

    /// `{$D q + b q = c$}` for `{$t = ln u$}` and `b` of a lower level, solving for each coefficient of `q`
    /// `{$D s + b s = c_m$}` in the field below.
    fn cancel_primitive(
        &self,
        b: &EPoly,
        mut c: EPoly,
        mut n: i64,
        level: usize,
        sure: &mut bool,
    ) -> RischResult<Option<EPoly>> {
        let b0 = b.coefficient(0);
        let mut q = EPoly::zero();
        while !c.is_zero() {
            let m = degree(&c);
            // Not a proof when `b` is a logarithmic derivative
            if n < m {
                *sure = false;
                return Ok(None);
            }
            let Some(s) = self.rde(&b0, &c.leading(), level - 1)? else {
                *sure = false;
                return Ok(None);
            };
            let p = EPoly::monomial(s, to_usize(m));
            c = c.sub(&b.mul(&p)).sub(&self.d_poly(&p, level));
            q = q.add(&p);
            n = m - 1;
        }
        Ok(Some(q))
    }

    /// `{$D q + b q = c$}` for `{$t = e^a$}` and `b` of a lower level, solving for each coefficient of `q`
    /// `{$D s + (b + m D a) s = c_m$}` in the field below.
    fn cancel_exp(
        &self,
        b: &EPoly,
        mut c: EPoly,
        mut n: i64,
        level: usize,
        sure: &mut bool,
    ) -> RischResult<Option<EPoly>> {
        let b0 = b.coefficient(0);
        let eta = self.tower.eta(level);
        // A proof when `{$b = r eta$}` with a non-integer `r`, as `b` can't be `{$D z / z + m eta$}`
        let mut proof = true;
        let proved = !matches!(log_derivative_multiple(&b0, &eta, &mut proof), Some(_)) && proof;
        let mut q = EPoly::zero();
        while !c.is_zero() {
            let m = degree(&c);
            if n < m {
                *sure &= proved;
                return Ok(None);
            }
            let f = b0.plus(&Elem::integer(m).times(&eta));
            let Some(s) = self.rde(&f, &c.leading(), level - 1)? else {
                *sure &= proved;
                return Ok(None);
            };
            let p = EPoly::monomial(s, to_usize(m));
            c = c.sub(&b.mul(&p)).sub(&self.d_poly(&p, level));
            q = q.add(&p);
            n = m - 1;
        }
        Ok(Some(q))
    }
}

/// The integer `m` with `{$alpha = D z / z + m eta$}` for `{$eta = D a$}`, `{$t = e^a$}` being a monomial and `z`
/// in the field below: only `{$z = 1$}` is detected, `sure` being set to `false` when another `z` could exist.
fn log_derivative_multiple(alpha: &Elem, eta: &Elem, sure: &mut bool) -> Option<i64> {
    match alpha.divide(eta).as_rational() {
        // `{$(r - m) eta = D z / z$}` would make `{$t^(r - m)$}` algebraic
        Some(r) => integer(r),
        None => {
            *sure = false;
            None
        }
    }
}

#[cfg(test)]
mod tests {
    use super::super::tower::Tower;
    use super::*;
    use crate::{field::real::R, parse, symbol};

    #[test]
    fn base_case() {
        let mut tower = Tower::new(symbol!("x"));
        let mut elem = |s: &str| tower.elem(&parse!(s, R)).unwrap();
        let (two_x, one, two_x2_1, inv_x) = (elem("2*x"), elem("1"), elem("2*x^2+1"), elem("1/x"));
        let risch = Risch { tower: &tower };
        // `{$y' + 2 x y = 2 x^2 + 1$}` is solved by `x`, `{$y' + 2 x y = 1$}` and `{$y' + y = 1 / x$}` have no
        // rational solution
        assert_eq!(
            risch.rde(&two_x, &two_x2_1, 1),
            Ok(Some(Elem::generator(1)))
        );
        assert_eq!(risch.rde(&two_x, &one, 1), Ok(None));
        assert_eq!(risch.rde(&one, &inv_x, 1), Ok(None));
    }
}
