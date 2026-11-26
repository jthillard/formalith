//! Recurrences of the Taylor coefficients of D-finite functions, and proofs of two-term recurrences.
//!
//! A differential equation `{$sum_(i, j) a_(i j) w^j partial^i f = 0$}` gives, for the coefficient of `{$w^n$}`,
//! `{$sum_(i, j) a_(i j) (n - j + 1) ... (n - j + i) c_(n - j + i) = 0$}` for every `{$n >= 0$}` (`c` being 0
//! at negative indices), a recurrence `{$sum_(s = 0)^r P_s(n) c_(n + s) = 0$}`. The coefficients are then
//! determined by finitely many initial values, at the first indices and where the leading coefficient vanishes.

// Indices and orders are small
#![allow(clippy::cast_possible_wrap, clippy::cast_possible_truncation)]

use std::collections::BTreeSet;

use crate::polynom::{
    dense::Coefficient,
    fraction::{EPoly, Elem},
};

use super::{
    ore::{Kind, Operator, annihilator},
    ratfun::{RatFun, natural_roots},
};

/// A recurrence `{$sum_(s = 0)^r P_s(n) c_(n + s) = 0$}` holding for `{$n >= n_0$}`.
pub struct Recurrence {
    pub(crate) operator: Operator,
    pub(crate) start: usize,
}

impl Recurrence {
    /// The recurrence of the coefficients of the power series annihilated by `op`, a differential operator in
    /// `w` with polynomial coefficients.
    pub(crate) fn from_differential(op: &Operator) -> Option<Self> {
        debug_assert_eq!(op.kind, Kind::Differential);
        // Terms `{$(s, P)$}`, the shift `{$s = i - j$}` and its coefficient in `n`
        let mut terms: Vec<(i64, EPoly)> = vec![];
        for (i, a) in op.coefficients.iter().enumerate() {
            if !a.den.is_constant() {
                return None;
            }
            let scale = a.den.leading().inverse();
            for (j, c) in a.num.coefficients().iter().enumerate() {
                if c.is_zero() {
                    continue;
                }
                // `{$c (n - j + 1) ... (n - j + i)$}`
                let factor = (1..=i).fold(EPoly::constant(c.times(&scale)), |p, l| {
                    p.mul(&EPoly::new(vec![
                        Elem::integer(l as i64 - j as i64),
                        Elem::one(),
                    ]))
                });
                let s = i as i64 - j as i64;
                match terms.iter_mut().find(|(t, _)| *t == s) {
                    Some((_, p)) => *p = p.add(&factor),
                    None => terms.push((s, factor)),
                }
            }
        }
        terms.retain(|(_, p)| !p.is_zero());
        let s_min = terms.iter().map(|(s, _)| *s).min()?;
        let s_max = terms.iter().map(|(s, _)| *s).max()?;
        // `{$n' = n + s_min$}`, so `{$c_(n - j + i) = c_(n' + s - s_min)$}`
        let r = usize::try_from(s_max - s_min).ok()?;
        let mut coefficients = vec![RatFun::zero(); r + 1];
        for (s, p) in terms {
            let p = RatFun::poly(p).shifted_by(-s_min);
            coefficients[usize::try_from(s - s_min).ok()?] = p;
        }
        let operator = Operator::new(Kind::Shift, coefficients)?;
        if operator.order() == 0 {
            return None;
        }
        Some(Self {
            operator,
            start: usize::try_from(s_min.max(0)).ok()?,
        })
    }

    /// The order `r`.
    pub(crate) const fn order(&self) -> usize {
        self.operator.order()
    }

    /// The leading coefficient `{$P_r$}`, a polynomial.
    fn leading(&self) -> &EPoly {
        &self.operator.coefficients[self.order()].num
    }

    /// The indices of the coefficients which the recurrence doesn't determine: the first `{$n_0 + r$}`, and
    /// `{$n + r$}` for the natural roots `{$n >= n_0$}` of `{$P_r$}`. `None` if they can't be found.
    pub(crate) fn initial_indices(&self) -> Option<Vec<usize>> {
        let r = self.order();
        let mut indices: BTreeSet<usize> = (0..self.start + r).collect();
        for root in natural_roots(self.leading())? {
            let root = usize::try_from(root).ok()?;
            if root >= self.start {
                indices.insert(root + r);
            }
        }
        Some(indices.into_iter().collect())
    }

    /// The coefficients `{$c_0, ..., c_(count - 1)$}`, with the initial values at [`Self::initial_indices`].
    pub(crate) fn coefficients(
        &self,
        initial: &[(usize, Elem)],
        count: usize,
    ) -> Option<Vec<Elem>> {
        let r = self.order();
        let mut c: Vec<Elem> = vec![];
        for index in 0..count {
            if let Some((_, value)) = initial.iter().find(|(i, _)| *i == index) {
                c.push(value.clone());
                continue;
            }
            // `{$c_(n + r) = -sum_(s < r) P_s(n) c_(n + s) / P_r(n)$}`, `{$n = index - r$}`
            let n = index.checked_sub(r)?;
            let at = Elem::integer(n as i64);
            let lead = self.operator.coefficients[r].eval(&at)?;
            if lead.is_zero() || n < self.start {
                return None;
            }
            let sum = (0..r).try_fold(Elem::zero(), |sum, s| {
                Some(sum.plus(&self.operator.coefficients[s].eval(&at)?.times(&c[n + s])))
            })?;
            c.push(sum.negate().divide(&lead));
        }
        Some(c)
    }

    /// Whether `{$P(n) c_(n + m) = Q(n) c_n$}` holds for every `{$n >= s$}`, `c` being the coefficients
    /// computed by [`Self::coefficients`] (at least those given in `c`, more being computed from `initial`).
    ///
    /// `{$d_n = P(n) c_(n + m) - Q(n) c_n$}` satisfies a recurrence of order `k` (found by reducing its shifts
    /// with this recurrence), which holds from some `{$n_1$}`: if `d` vanishes from `s` to `{$n_1 + k$}`, it
    /// vanishes everywhere.
    pub(crate) fn proves(
        &self,
        initial: &[(usize, Elem)],
        p: &EPoly,
        q: &EPoly,
        m: usize,
        s: usize,
    ) -> bool {
        let r = self.order();
        let reductions = self.operator.reductions(m.max(r));
        // `{$d$}` in the basis `{$c_n, ..., c_(n + r - 1)$}`
        let (p, q) = (RatFun::poly(p.clone()), RatFun::poly(q.clone()));
        let d0: Vec<RatFun> = (0..r)
            .map(|t| {
                p.times(&reductions[m][t])
                    .minus(&q.times(&reductions[0][t]))
            })
            .collect();
        let mut shifts = vec![d0];
        let Some(op) = annihilator(Kind::Shift, r, |i| {
            while shifts.len() <= i {
                let next = self.operator.step(&shifts[shifts.len() - 1]);
                shifts.push(next);
            }
            shifts[i].clone()
        }) else {
            return false;
        };
        let k = op.order();
        // Where the reductions or the recurrence of `d` don't hold: roots of `{$P_r(n + j)$}` and of the
        // denominators of the coefficients of `op`
        let Some(lead_roots) = natural_roots(self.leading()) else {
            return false;
        };
        let mut bad: Vec<u64> = vec![];
        for root in lead_roots {
            for j in 0..=(m + k + r) as u64 {
                if let Some(n) = root.checked_sub(j) {
                    bad.push(n);
                }
            }
        }
        for c in &op.coefficients {
            let Some(roots) = natural_roots(&c.den) else {
                return false;
            };
            bad.extend(roots);
        }
        let n1 = bad
            .into_iter()
            .map(|n| n as usize + 1)
            .chain([self.start, s])
            .max()
            .unwrap_or(0);
        // `{$d_n = 0$}` for `{$s <= n < n_1 + k$}`
        let count = n1 + k + m + 1;
        let Some(c) = self.coefficients(initial, count) else {
            return false;
        };
        (s..n1 + k).all(|n| {
            let at = Elem::integer(n as i64);
            p.eval(&at)
                .zip(q.eval(&at))
                .is_some_and(|(pn, qn)| pn.times(&c[n + m]) == qn.times(&c[n]))
        })
    }
}

/// The coefficients `{$c_0, ..., c_(count - 1)$}` of the power series solution of `{$L f = 0$}` with the first
/// coefficients `initial` (`{$c_i = f^((i))(0) / i!$}`, as many as the order `r` of `L`), `L` being a differential
/// operator in `w` with polynomial coefficients whose leading one doesn't vanish at 0 (an ordinary point).
///
/// The coefficient of `{$w^n$}` in `{$L f$}` is `{$sum_(i, j) a_(i j) (n - j + 1) ... (n - j + i) c_(n - j + i)$}`,
/// whose highest index is `{$n + r$}`, from `{$a_(r 0) != 0$}`: it gives `{$c_(n + r)$}` for every `{$n >= 0$}`.
/// `None` if the point isn't ordinary.
pub fn power_series(op: &Operator, initial: &[Elem], count: usize) -> Option<Vec<Elem>> {
    debug_assert_eq!(op.kind, Kind::Differential);
    let r = op.order();
    if initial.len() != r {
        return None;
    }
    // `{$a_(i j)$}`, the denominators being constants
    let a: Vec<Vec<Elem>> = op
        .coefficients
        .iter()
        .map(|c| {
            c.den.is_constant().then(|| {
                let scale = c.den.leading().inverse();
                c.num
                    .coefficients()
                    .iter()
                    .map(|a| a.times(&scale))
                    .collect()
            })
        })
        .collect::<Option<_>>()?;
    let lead = a[r].first().filter(|c| !c.is_zero())?.clone();
    let mut c = initial.to_vec();
    let mut n: i64 = 0;
    while c.len() < count {
        let mut sum = Elem::zero();
        for (i, row) in a.iter().enumerate() {
            for (j, a_ij) in row.iter().enumerate() {
                let Ok(index) = usize::try_from(n + i as i64 - j as i64) else {
                    continue;
                };
                if a_ij.is_zero() || (i == r && j == 0) {
                    continue;
                }
                // `{$(n - j + 1) ... (n - j + i)$}`
                let factor = (1..=i as i64).fold(Elem::one(), |p, l| {
                    p.times(&Elem::integer(n - j as i64 + l))
                });
                sum = sum.plus(&a_ij.times(&factor).times(&c[index]));
            }
        }
        let factor = (1..=r as i64).fold(lead.clone(), |p, l| p.times(&Elem::integer(n + l)));
        c.push(sum.negate().divide(&factor));
        n += 1;
    }
    Some(c)
}
