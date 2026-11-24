//! Isolation of the real roots of univariate polynomials with rational coefficients, by Sturm sequences, and their
//! refinement by bisection.

use std::cmp::Ordering;

use malachite::{
    Natural, Rational,
    base::num::{
        arithmetic::traits::{Abs, Gcd, Lcm, Sign},
        basic::traits::{One, Zero},
    },
};

use super::dense::Poly;

/// An interval `{$[a, b]$}` containing a single root of a polynomial: either `{$a = b$}`, the root being rational,
/// or `{$a < b$}` with `{$p(a) p(b) < 0$}`. The interval doesn't contain 0, except for the root 0 itself.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Isolated {
    /// The lower end.
    pub lower: Rational,
    /// The upper end.
    pub upper: Rational,
}

impl Isolated {
    /// Whether the root is the rational `lower = upper`.
    pub(crate) fn is_exact(&self) -> bool {
        self.lower == self.upper
    }

    /// The sign of the root.
    pub(crate) fn sign(&self) -> Ordering {
        if self.lower > 0 {
            Ordering::Greater
        } else if self.upper < 0 {
            Ordering::Less
        } else if self.is_exact() {
            Ordering::Equal
        } else if self.lower == 0 {
            // The root isn't 0, an end of the interval
            Ordering::Greater
        } else {
            Ordering::Less
        }
    }

    /// The width `{$b - a$}`.
    fn width(&self) -> Rational {
        &self.upper - &self.lower
    }

    /// Halve the interval around the root of `p`, which it isolates.
    fn bisect(&mut self, p: &Poly) {
        if self.is_exact() {
            return;
        }
        let middle = (&self.lower + &self.upper) >> 1u64;
        match p.eval(&middle).sign() {
            Ordering::Equal => {
                self.lower = middle.clone();
                self.upper = middle;
            }
            sign if sign == p.eval(&self.lower).sign() => self.lower = middle,
            _ => self.upper = middle,
        }
    }

    /// Bisect the interval until its width is at most `{$2^(-"bits")$}`.
    pub(crate) fn refine(&mut self, p: &Poly, bits: u64) {
        let bound = Rational::ONE >> bits;
        while self.width() > bound {
            self.bisect(p);
        }
    }

    /// The order of the roots of `p` and `q` isolated by `self` and `other`, which must be distinct roots, refining
    /// both intervals until they are disjoint.
    pub(crate) fn compare(&mut self, p: &Poly, other: &mut Self, q: &Poly) -> Ordering {
        loop {
            if self.upper < other.lower || (self.upper == other.lower && !self.is_exact()) {
                return Ordering::Less;
            }
            if other.upper < self.lower || (other.upper == self.lower && !other.is_exact()) {
                return Ordering::Greater;
            }
            if self.is_exact() && other.is_exact() {
                // Roots aren't distinct
                return Ordering::Equal;
            }
            if self.width() >= other.width() && !self.is_exact() {
                self.bisect(p);
            } else {
                other.bisect(q);
            }
        }
    }
}

/// The Sturm sequence `{$p_0 = p$}`, `{$p_1 = p'$}`, `{$p_(i+1) = -(p_(i-1) mod p_i)$}` of a square-free
/// polynomial.
struct Sturm(Vec<Poly>);

impl Sturm {
    fn new(p: &Poly) -> Self {
        let mut sequence = vec![p.clone(), p.derivative()];
        loop {
            let [.., a, b] = sequence.as_slice() else {
                unreachable!("At least two polynomials")
            };
            if b.is_zero() {
                sequence.pop();
                break;
            }
            let r = a.rem(b).neg();
            if r.is_zero() {
                break;
            }
            sequence.push(r);
        }
        Self(sequence)
    }

    /// The number of sign changes of the sequence at `x`, zeros being skipped.
    fn variations(&self, x: &Rational) -> usize {
        let signs: Vec<_> = self
            .0
            .iter()
            .map(|p| p.eval(x).sign())
            .filter(|sign| *sign != Ordering::Equal)
            .collect();
        signs.windows(2).filter(|w| w[0] != w[1]).count()
    }

    /// The number of distinct roots in `{$(a, b]$}`.
    fn count(&self, a: &Rational, b: &Rational) -> usize {
        self.variations(a) - self.variations(b)
    }
}

/// A power of two larger than the absolute value of every root of `p` (Cauchy's bound
/// `{$1 + max_i |c_i / c_n|$}`).
fn root_bound(p: &Poly) -> Rational {
    let leading = p.leading();
    let bound = p
        .coefficients()
        .iter()
        .map(|c| (c / &leading).abs())
        .max()
        .unwrap_or(Rational::ZERO)
        + Rational::ONE;
    let mut res = Rational::ONE;
    while res <= bound {
        res <<= 1u64;
    }
    res
}

/// The square-free part of `p`, monic.
pub fn square_free_part(p: &Poly) -> Poly {
    p.exact_div(&p.gcd(&p.derivative())).monic()
}

/// Isolating intervals of the distinct real roots of a non-constant polynomial, by increasing order.
pub fn isolate(p: &Poly) -> Vec<Isolated> {
    let p = square_free_part(p);
    if p.degree() == 0 {
        return vec![];
    }
    let sturm = Sturm::new(&p);
    let bound = root_bound(&p);
    let mut res = vec![];
    // Intervals `(a, b]` with their number of roots, the last one being split first
    let mut stack = vec![(-&bound, bound.clone(), sturm.count(&-&bound, &bound))];
    while let Some((a, b, count)) = stack.pop() {
        match count {
            0 => {}
            1 => res.push(single(&p, &sturm, a, b)),
            _ => {
                let middle = (&a + &b) >> 1u64;
                let left = sturm.count(&a, &middle);
                stack.push((middle.clone(), b, count - left));
                stack.push((a, middle, left));
            }
        }
    }
    res
}

/// The isolating interval of the single root of `p` in `{$(a, b]$}`.
fn single(p: &Poly, sturm: &Sturm, mut a: Rational, mut b: Rational) -> Isolated {
    loop {
        if p.eval(&b) == 0 {
            return Isolated {
                lower: b.clone(),
                upper: b,
            };
        }
        // The root is in `(a, b)`: `a` must not be a root, nor have 0 inside
        let zero_inside = a < 0 && b > 0;
        if p.eval(&a) != 0 && !zero_inside {
            return Isolated { lower: a, upper: b };
        }
        let middle = if zero_inside {
            Rational::ZERO
        } else {
            (&a + &b) >> 1u64
        };
        if sturm.count(&a, &middle) == 1 {
            b = middle;
        } else {
            a = middle;
        }
    }
}

/// The primitive polynomial over `{$ZZ$}` with a positive leading coefficient proportional to `p`.
pub fn primitive(p: &Poly) -> Poly {
    let denominators = p
        .coefficients()
        .iter()
        .fold(Natural::ONE, |res, c| res.lcm(c.denominator_ref()));
    let scaled = p.scale(&Rational::from(denominators));
    let content = scaled
        .coefficients()
        .iter()
        .fold(Natural::ZERO, |res, c| res.gcd(c.numerator_ref()));
    let content = if scaled.leading() < 0 {
        -Rational::from(content)
    } else {
        Rational::from(content)
    };
    scaled.scale(&(Rational::ONE / content))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn poly(coefficients: &[i64]) -> Poly {
        Poly::new(coefficients.iter().map(|c| Rational::from(*c)).collect())
    }

    fn check(p: &Poly, count: usize) -> Vec<Isolated> {
        let roots = isolate(p);
        assert_eq!(roots.len(), count);
        for root in &roots {
            if root.is_exact() {
                assert_eq!(p.eval(&root.lower), 0);
            } else {
                assert!(root.lower < root.upper);
                assert_ne!(p.eval(&root.lower).sign(), p.eval(&root.upper).sign());
                assert!(root.lower >= 0 || root.upper <= 0);
            }
        }
        for pair in roots.windows(2) {
            assert!(pair[0].upper <= pair[1].lower);
        }
        roots
    }

    #[test]
    fn counts() {
        // `{$x^5 - x - 1$}`
        let p = poly(&[-1, -1, 0, 0, 0, 1]);
        let mut roots = check(&p, 1);
        roots[0].refine(&p, 60);
        assert!(roots[0].lower > Rational::from_signeds(116_730, 100_000));
        assert!(roots[0].upper < Rational::from_signeds(116_731, 100_000));
        check(&poly(&[1, -5, 0, 0, 0, 1]), 3);
        check(&poly(&[1, 0, 1]), 0);
        check(&poly(&[1, 1, 0, 0, 1]), 0);
        // `{$x (x - 1)^2 (x + 2)$}`
        check(
            &poly(&[0, 1])
                .mul(&poly(&[-1, 1]).pow(2))
                .mul(&poly(&[2, 1])),
            3,
        );
    }

    #[test]
    fn wilkinson() {
        let p = (1..=10).fold(Poly::one(), |p, i| p.mul(&poly(&[-i, 1])));
        let roots = check(&p, 10);
        for (i, root) in roots.iter().enumerate() {
            let value = Rational::from(i + 1);
            assert!(root.lower <= value && value <= root.upper);
        }
    }

    #[test]
    fn primitive_form() {
        let p = Poly::new(vec![
            Rational::from_signeds(-1, 2),
            Rational::from_signeds(-3, 4),
        ]);
        assert_eq!(primitive(&p), poly(&[2, 3]));
    }
}
