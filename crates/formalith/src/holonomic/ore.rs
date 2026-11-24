//! Linear operators `{$L = sum_i a_i partial^i$}` with rational function coefficients: differential operators
//! (`{$partial = d/(d t)$}`, `{$partial a = a partial + a'$}`) and recurrence operators (the shift
//! `{$S c(n) = c(n + 1)$}`, `{$S a = a(n + 1) S$}`).
//!
//! Closure properties are linear algebra: the derivatives (or shifts) of an element are written in the basis of
//! the derivatives of lower order of the functions it is made of, reduced with their operators, until one of them
//! depends linearly on the previous ones, which gives its operator.

use crate::polynom::{dense::Coefficient, fraction::solve_linear};

use super::ratfun::RatFun;

/// Largest order of the operators computed.
pub const MAX_ORDER: usize = 8;

/// The kind of an operator.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Kind {
    /// `{$partial = d/(d t)$}`.
    Differential,
    /// `{$S c(n) = c(n + 1)$}`.
    Shift,
}

/// `{$sum_i a_i partial^i$}` (or `{$S^i$}`), its leading coefficient non-zero.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Operator {
    pub(crate) kind: Kind,
    pub(crate) coefficients: Vec<RatFun>,
}

impl Operator {
    /// The operator with the given coefficients, by increasing order, `None` if they are all zero.
    pub(crate) fn new(kind: Kind, mut coefficients: Vec<RatFun>) -> Option<Self> {
        while coefficients.last().is_some_and(RatFun::is_zero) {
            coefficients.pop();
        }
        (!coefficients.is_empty()).then_some(Self { kind, coefficients })
    }

    /// The order.
    pub(crate) const fn order(&self) -> usize {
        self.coefficients.len() - 1
    }

    /// The operator of order 1 `{$partial - rho$}` (or `{$S - rho$}`).
    pub(crate) fn first_order(kind: Kind, rho: &RatFun) -> Self {
        Self {
            kind,
            coefficients: vec![rho.negate(), RatFun::one()],
        }
    }

    /// `{$L partial$}` (or `{$L S$}`).
    pub(crate) fn times_generator(&self) -> Self {
        // `{$a_i partial^i partial = a_i partial^(i + 1)$}`
        let mut coefficients = vec![RatFun::zero()];
        coefficients.extend(self.coefficients.iter().cloned());
        Self {
            kind: self.kind,
            coefficients,
        }
    }

    /// One more application of the generator to `{$sum_j v_j partial^j f$}`, reduced in the basis
    /// `{$f, ..., partial^(r - 1) f$}` with `{$L f = 0$}`.
    pub(crate) fn step(&self, v: &[RatFun]) -> Vec<RatFun> {
        let r = self.order();
        let mut res = vec![RatFun::zero(); r + 1];
        for (j, c) in v.iter().enumerate() {
            match self.kind {
                // `{$partial (c partial^j f) = c' partial^j f + c partial^(j + 1) f$}`
                Kind::Differential => {
                    res[j] = res[j].plus(&c.derivative());
                    res[j + 1] = res[j + 1].plus(c);
                }
                // `{$S (c S^j f) = c(n + 1) S^(j + 1) f$}`
                Kind::Shift => res[j + 1] = res[j + 1].plus(&c.shifted()),
            }
        }
        // `{$partial^r f = -sum_(j < r) a_j / a_r partial^j f$}`
        let top = res.pop().expect("Order r + 1 vector");
        if !top.is_zero() {
            let lead = self.coefficients[r].inverse();
            for (j, a) in self.coefficients[..r].iter().enumerate() {
                res[j] = res[j].minus(&top.times(a).times(&lead));
            }
        }
        res
    }

    /// The vectors of `{$f, partial f, ..., partial^k f$}` in the basis `{$f, ..., partial^(r - 1) f$}`.
    pub(crate) fn reductions(&self, k: usize) -> Vec<Vec<RatFun>> {
        let r = self.order();
        let mut res: Vec<Vec<RatFun>> = vec![];
        for i in 0..=k {
            let v = if i < r {
                let mut v = vec![RatFun::zero(); r];
                v[i] = RatFun::one();
                v
            } else {
                self.step(&res[i - 1])
            };
            res.push(v);
        }
        res
    }

    /// The annihilator of `f + g`, the least common left multiple.
    pub(crate) fn lclm(&self, other: &Self) -> Option<Self> {
        let (r, s) = (self.order(), other.order());
        let dim = r + s;
        let (a, b) = (self.reductions(dim), other.reductions(dim));
        annihilator(self.kind, dim, |i| {
            a[i].iter().chain(&b[i]).cloned().collect()
        })
    }

    /// The annihilator of `f g`, the symmetric product, for differential operators.
    pub(crate) fn symmetric_product(&self, other: &Self) -> Option<Self> {
        debug_assert_eq!(self.kind, Kind::Differential);
        let (r, s) = (self.order(), other.order());
        let dim = r * s;
        let (a, b) = (self.reductions(dim), other.reductions(dim));
        // `{$partial^i (f g) = sum_j binom(i, j) partial^j f partial^(i - j) g$}`, in the basis
        // `{$partial^p f partial^q g$}`
        annihilator(self.kind, dim, |i| {
            let mut v = vec![RatFun::zero(); dim];
            let mut binomial = malachite::Rational::from(1);
            for j in 0..=i {
                let c = RatFun::from_rational(binomial.clone());
                for (p, x) in a[j].iter().enumerate() {
                    if x.is_zero() {
                        continue;
                    }
                    for (q, y) in b[i - j].iter().enumerate() {
                        if !y.is_zero() {
                            v[p * s + q] = v[p * s + q].plus(&c.times(x).times(y));
                        }
                    }
                }
                binomial =
                    binomial * malachite::Rational::from(i - j) / malachite::Rational::from(j + 1);
            }
            v
        })
    }

    /// The operator with polynomial coefficients, multiplied by the lcm of the denominators.
    pub(crate) fn clear_denominators(&self) -> Self {
        let lcm = self.coefficients.iter().fold(RatFun::one().den, |l, c| {
            let g = l.gcd(&c.den);
            l.mul(&c.den).exact_div(&g)
        });
        let lcm = RatFun::poly(lcm);
        Self {
            kind: self.kind,
            coefficients: self.coefficients.iter().map(|c| c.times(&lcm)).collect(),
        }
    }
}

/// The operator `{$partial^i - sum_(j < i) alpha_j partial^j$}` for the first `i` such that `vector(i)` depends
/// linearly on `vector(0), ..., vector(i - 1)`, vectors of dimension `dim`, `None` above [`MAX_ORDER`].
pub fn annihilator(
    kind: Kind,
    dim: usize,
    mut vector: impl FnMut(usize) -> Vec<RatFun>,
) -> Option<Operator> {
    let mut vectors: Vec<Vec<RatFun>> = vec![];
    for i in 0..=dim.min(MAX_ORDER) {
        let v = vector(i);
        // `{$sum_j alpha_j v_j = v_i$}`
        let rows = (0..dim)
            .map(|row| {
                let mut r: Vec<RatFun> = vectors.iter().map(|u| u[row].clone()).collect();
                r.push(v[row].clone());
                r
            })
            .collect();
        if let Some(alpha) = solve_linear(rows, i) {
            let mut coefficients: Vec<RatFun> = alpha.iter().map(RatFun::negate).collect();
            coefficients.push(RatFun::one());
            return Operator::new(kind, coefficients);
        }
        vectors.push(v);
    }
    None
}
