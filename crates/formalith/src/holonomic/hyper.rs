//! Hypergeometric solutions of linear recurrences with polynomial coefficients, by Petkovšek's algorithm *Hyper*
//! (*A = B*, chapter 8), over `{$QQ$}` and the Gaussian rationals `{$QQ(i)$}`.
//!
//! A solution `h` of `{$sum_(s = 0)^r P_s(n) h(n + s) = 0$}` with `{$h(n + 1) / h(n) = Z A(n) / B(n) C(n + 1) / C(n)$}`
//! has `A` dividing `{$P_0(n)$}`, `B` dividing `{$P_r(n - r + 1)$}`, `Z` a root of the polynomial of the leading
//! coefficients of `{$sum_s Z^s P_s(n) product_(j < s) A(n + j) product_(j >= s) B(n + j)$}`, and `C` a polynomial
//! solution of `{$sum_s Z^s P_s(n) product_(j < s) A(n + j) product_(j >= s) B(n + j) C(n + s) = 0$}`. Only `A` and `B`
//! with rational roots are tried, and `Z` rational or Gaussian, so some solutions may be missed, but those found are
//! right.

use malachite::{Rational, base::num::basic::traits::Zero};

use crate::{
    context::Symbol,
    integrate::rational,
    polynom::{
        dense::{Coefficient, Poly},
        fraction::solve_linear,
    },
};

use super::recurrence::Recurrence;

/// A Gaussian rational `{$a + b i$}`.
pub type Gaussian = [Rational; 2];

/// Largest degree of the polynomial `C` of a solution.
const MAX_C_DEGREE: usize = 6;
/// Largest number of linear factors of `{$P_0$}` and `{$P_r$}` whose products are tried as `A` and `B`.
const MAX_FACTORS: usize = 6;

/// A hypergeometric solution `{$h(n) = Z^n C(n) product_(m = n_0)^(n - 1) A(m) / B(m)$}` (up to a constant).
#[derive(Clone, Debug)]
pub struct Solution {
    /// The ratio `Z`.
    pub z: Gaussian,
    /// The polynomial `C`.
    pub c: Poly<Gaussian>,
    /// The monic polynomial `A`, with rational roots.
    pub a: Poly<Rational>,
    /// The monic polynomial `B`, with rational roots.
    pub b: Poly<Rational>,
}

impl Solution {
    /// `{$h(n) / h(n_0)$}` times `{$Z^(n_0) C(n_0)$}`: `{$Z^n C(n) product_(m = n_0)^(n - 1) A(m) / B(m)$}`, for
    /// `{$n >= n_0$}`, `None` when `B` vanishes on the way.
    pub fn eval(&self, n0: usize, n: usize) -> Option<Gaussian> {
        let lift = |r: Rational| Gaussian::from_rational(r);
        let mut res = power(&self.z, n).times(&self.c.eval(&lift(Rational::from(n))));
        for m in n0..n {
            let m = Rational::from(m);
            let b = self.b.eval(&m);
            if b == 0u32 {
                return None;
            }
            res = res.times(&lift(self.a.eval(&m) / b));
        }
        Some(res)
    }

    /// The ratio `{$h(n + 1) / h(n)$}` as the pair of polynomials `{$(Z A(n) C(n + 1), B(n) C(n))$}`.
    fn ratio(&self) -> (Poly<Gaussian>, Poly<Gaussian>) {
        let lift = |p: &Poly<Rational>| p.map(|c| Gaussian::from_rational(c.clone()));
        (
            lift(&self.a)
                .mul(&self.c.shift(&Gaussian::one()))
                .scale(&self.z),
            lift(&self.b).mul(&self.c),
        )
    }

    /// Whether `self` and `other` have the same ratio, so they are proportional.
    fn same_ratio(&self, other: &Self) -> bool {
        let ((p, q), (r, s)) = (self.ratio(), other.ratio());
        p.mul(&s) == r.mul(&q)
    }
}

/// `{$z^n$}`.
fn power(z: &Gaussian, n: usize) -> Gaussian {
    (0..n).fold(Gaussian::one(), |res, _| res.times(z))
}

/// The hypergeometric solutions found of the recurrence, pairwise non-proportional. Empty when its coefficients
/// aren't rational.
pub fn solutions(recurrence: &Recurrence) -> Vec<Solution> {
    let Some(p) = rational_coefficients(recurrence) else {
        return vec![];
    };
    let r = p.len() - 1;
    if r == 0 {
        return vec![];
    }
    let x = Symbol::new("@hn");
    // `{$P_r(n - r + 1)$}`
    let shift = Rational::from(1) - Rational::from(r);
    let (Some(a_roots), Some(b_roots)) = (
        linear_factors(&p[0], x),
        linear_factors(&p[r].shift(&shift), x),
    ) else {
        return vec![];
    };
    let mut found: Vec<Solution> = vec![];
    for a in products(&a_roots) {
        for b in products(&b_roots) {
            for solution in with_factors(&p, &a, &b, x) {
                if !found.iter().any(|other| other.same_ratio(&solution)) {
                    found.push(solution);
                }
            }
        }
    }
    found
}

/// The coefficients `{$P_s$}` of the recurrence as polynomials over `{$QQ$}`, `None` if they aren't.
fn rational_coefficients(recurrence: &Recurrence) -> Option<Vec<Poly<Rational>>> {
    let rational = |p: &crate::polynom::fraction::EPoly| {
        p.coefficients()
            .iter()
            .map(|c| c.as_rational().cloned())
            .collect::<Option<Vec<_>>>()
            .map(Poly::new)
    };
    recurrence
        .operator
        .coefficients
        .iter()
        .map(|c| {
            let (num, den) = (rational(&c.num)?, rational(&c.den)?);
            (den.degree() == 0).then(|| num.scale(&den.coefficient(0).inverse()))
        })
        .collect()
}

/// The rational roots of `p` with multiplicities, `None` for a zero polynomial or too many of them. Non-linear
/// factors over `{$QQ$}` are left out (no solution with them is found).
fn linear_factors(p: &Poly<Rational>, x: Symbol) -> Option<Vec<Rational>> {
    if p.coefficients().iter().all(|c| *c == 0u32) {
        return None;
    }
    let mut roots = vec![];
    let (distinct, _) = rational::rational_roots(p, x);
    for root in distinct {
        let factor = Poly::new(vec![-root.clone(), Rational::from(1)]);
        let mut rest = p.clone();
        while rest.degree() > 0 && rest.divisible_by(&factor) {
            rest = rest.exact_div(&factor);
            roots.push(root.clone());
        }
    }
    (roots.len() <= MAX_FACTORS).then_some(roots)
}

/// The distinct monic products of sub-multisets of the linear factors `{$x - "root"$}`.
fn products(roots: &[Rational]) -> Vec<Poly<Rational>> {
    let mut res: Vec<Poly<Rational>> = vec![Poly::one()];
    for root in roots {
        let factor = Poly::new(vec![-root.clone(), Rational::from(1)]);
        let more: Vec<_> = res.iter().map(|p| p.mul(&factor)).collect();
        for p in more {
            if !res.contains(&p) {
                res.push(p);
            }
        }
    }
    res
}

/// The solutions with the factors `A` and `B`.
fn with_factors(
    p: &[Poly<Rational>],
    a: &Poly<Rational>,
    b: &Poly<Rational>,
    x: Symbol,
) -> Vec<Solution> {
    let r = p.len() - 1;
    // `{$T_s(n) = P_s(n) product_(j < s) A(n + j) product_(j >= s) B(n + j)$}`
    let terms: Vec<Poly<Rational>> = (0..=r)
        .map(|s| {
            let mut t = p[s].clone();
            for j in 0..s {
                t = t.mul(&a.shift(&Rational::from(j)));
            }
            for j in s..r {
                t = t.mul(&b.shift(&Rational::from(j)));
            }
            t
        })
        .collect();
    let degree = terms.iter().map(Poly::degree).max().unwrap_or(0);
    let leading = Poly::new(
        terms
            .iter()
            .map(|t| {
                if t.degree() == degree {
                    t.coefficient(degree)
                } else {
                    Rational::ZERO
                }
            })
            .collect(),
    );
    let mut res = vec![];
    for z in roots(&leading, x) {
        if let Some(c) = polynomial_solution(&terms, &z) {
            res.push(Solution {
                z,
                c,
                a: a.clone(),
                b: b.clone(),
            });
        }
    }
    res
}

/// The non-zero roots of `p` in `{$QQ(i)$}`: rational roots and the Gaussian roots of quadratic factors.
fn roots(p: &Poly<Rational>, x: Symbol) -> Vec<Gaussian> {
    if p.degree() == 0 {
        return vec![];
    }
    let mut res = vec![];
    for square_free in p.square_free() {
        if square_free.degree() == 0 {
            continue;
        }
        for q in rational::factor(&square_free, x) {
            match q.degree() {
                1 => {
                    let root = -q.coefficient(0) / q.coefficient(1);
                    if root != 0u32 {
                        res.push(Gaussian::from_rational(root));
                    }
                }
                2 => {
                    // `{$(-b plus.minus sqrt(b^2 - 4 a c)) / (2 a)$}` with a negative square discriminant
                    let (c0, c1, c2) = (q.coefficient(0), q.coefficient(1), q.coefficient(2));
                    let discriminant = &c1 * &c1 - Rational::from(4) * &c0 * &c2;
                    if let Some(root) = rational_sqrt(&-discriminant) {
                        let (u, v) = (
                            -c1 / (Rational::from(2) * &c2),
                            root / (Rational::from(2) * &c2),
                        );
                        res.push([u.clone(), v.clone()]);
                        res.push([u, -v]);
                    }
                }
                _ => {}
            }
        }
    }
    res
}

/// The square root of a positive rational which is a square.
fn rational_sqrt(r: &Rational) -> Option<Rational> {
    use malachite::base::num::arithmetic::traits::CheckedSqrt;
    if *r <= 0u32 {
        return None;
    }
    r.checked_sqrt()
}

/// A non-zero polynomial `C` of degree at most [`MAX_C_DEGREE`] with `{$sum_s Z^s T_s(n) C(n + s) = 0$}`, of least
/// degree, monic.
fn polynomial_solution(terms: &[Poly<Rational>], z: &Gaussian) -> Option<Poly<Gaussian>> {
    let lift = |p: &Poly<Rational>| p.map(|c| Gaussian::from_rational(c.clone()));
    let terms: Vec<Poly<Gaussian>> = terms.iter().map(lift).collect();
    // The image of `{$n^i$}`
    let column = |i: usize| {
        terms
            .iter()
            .enumerate()
            .fold(Poly::<Gaussian>::new(vec![]), |res, (s, t)| {
                let shifted = Poly::<Gaussian>::monomial(Gaussian::one(), i)
                    .shift(&Gaussian::from_rational(Rational::from(s)));
                res.add(&t.mul(&shifted).scale(&power(z, s)))
            })
    };
    for degree in 0..=MAX_C_DEGREE {
        let columns: Vec<Poly<Gaussian>> = (0..=degree).map(column).collect();
        let rows = columns.iter().map(Poly::degree).max().unwrap_or(0) + 1;
        // `{$sum_(i < d) c_i col_i = -col_d$}`, `C` monic
        let equations: Vec<Vec<Gaussian>> = (0..rows)
            .map(|t| {
                let mut row: Vec<Gaussian> =
                    columns[..degree].iter().map(|c| c.coefficient(t)).collect();
                row.push(columns[degree].coefficient(t).negate());
                row
            })
            .collect();
        if let Some(mut c) = solve_linear(equations, degree) {
            c.push(Gaussian::one());
            return Some(Poly::new(c));
        }
    }
    None
}
