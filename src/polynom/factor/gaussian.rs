//! Sparse multivariate polynomials over the Gaussian rationals `{$QQ(i)$}`, used by Trager's factorization algorithm.

use std::collections::BTreeMap;

use malachite::{
    Integer, Natural, Rational,
    base::num::{
        arithmetic::traits::{BinomialCoefficient, Gcd},
        basic::traits::{One, Zero},
    },
};

use super::multivariate::SparsePoly;

/// A Gaussian rational `{$a + b i$}`, stored as `[a, b]`.
pub type Gaussian = [Rational; 2];

/// The Gaussian rational `{$1$}`.
pub const fn gaussian_one() -> Gaussian {
    [Rational::ONE, Rational::ZERO]
}

/// `a * b`
pub fn gmul(a: &Gaussian, b: &Gaussian) -> Gaussian {
    [&a[0] * &b[0] - &a[1] * &b[1], &a[0] * &b[1] + &a[1] * &b[0]]
}

/// `a / b`, `b` must be non-zero.
pub fn gdiv(a: &Gaussian, b: &Gaussian) -> Gaussian {
    let norm = &b[0] * &b[0] + &b[1] * &b[1];
    let [re, im] = gmul(a, &[b[0].clone(), -&b[1]]);
    [re / &norm, im / &norm]
}

/// `a^e`
pub fn gpow(a: &Gaussian, e: u32) -> Gaussian {
    (0..e).fold(gaussian_one(), |acc, _| gmul(&acc, a))
}

/// A sparse polynomial in `n` variables over `{$QQ(i)$}`, written `{$"re" + i "im"$}` with `{$"re", "im" in QQ[x_1, ..., x_n]$}`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GaussianPoly {
    /// Real part of the coefficients.
    pub re: SparsePoly,
    /// Imaginary part of the coefficients.
    pub im: SparsePoly,
}

impl GaussianPoly {
    /// The zero polynomial in `n` variables.
    pub const fn zero(n: usize) -> Self {
        Self {
            re: SparsePoly::zero(n),
            im: SparsePoly::zero(n),
        }
    }
    /// Number of variables.
    pub const fn variable_count(&self) -> usize {
        self.re.variable_count()
    }
    /// Add `c * x^exponents` to the polynomial.
    pub fn add_term(&mut self, exponents: Vec<u32>, c: Gaussian) {
        let [re, im] = c;
        self.re.add_term(exponents.clone(), re);
        self.im.add_term(exponents, im);
    }
    /// Non-zero coefficients, indexed by exponent vectors sorted lexicographically.
    pub fn coefficients(&self) -> BTreeMap<Vec<u32>, Gaussian> {
        let mut res: BTreeMap<Vec<u32>, Gaussian> = BTreeMap::new();
        for (e, c) in self.re.terms() {
            res.entry(e.clone())
                .or_insert_with(|| [Rational::ZERO, Rational::ZERO])[0] = c.clone();
        }
        for (e, c) in self.im.terms() {
            res.entry(e.clone())
                .or_insert_with(|| [Rational::ZERO, Rational::ZERO])[1] = c.clone();
        }
        res
    }
    /// Check if the polynomial is zero.
    pub fn is_zero(&self) -> bool {
        self.re.is_zero() && self.im.is_zero()
    }
    /// Check if the polynomial is a constant.
    pub fn is_constant(&self) -> bool {
        self.re.is_constant() && self.im.is_constant()
    }
    /// Leading coefficient for the lex order.
    pub fn leading_coefficient(&self) -> Gaussian {
        self.coefficients()
            .pop_last()
            .map_or([Rational::ZERO, Rational::ZERO], |(_, c)| c)
    }
    /// Degree in the variable `var`.
    pub fn degree_in(&self, var: usize) -> u32 {
        self.re.degree_in(var).max(self.im.degree_in(var))
    }
    /// Total degree.
    pub fn total_degree(&self) -> u32 {
        self.re.total_degree().max(self.im.total_degree())
    }
    /// `c * self`
    #[must_use]
    pub fn scale(&self, c: &Gaussian) -> Self {
        Self {
            re: self.re.scale(&c[0]).sub(&self.im.scale(&c[1])),
            im: self.re.scale(&c[1]).add(&self.im.scale(&c[0])),
        }
    }
    /// The norm `{$f overline(f)$}`, where the conjugation applies to coefficients. It has rational coefficients.
    pub fn norm(&self) -> SparsePoly {
        self.re.mul(&self.re).add(&self.im.mul(&self.im))
    }
    /// Substitute `{$"var" = "var" + s i$}`.
    #[must_use]
    pub fn shift_imaginary(&self, var: usize, s: &Integer) -> Self {
        if *s == 0u32 {
            return self.clone();
        }
        let value = [Rational::ZERO, Rational::from(s)];
        let mut res = Self::zero(self.variable_count());
        for (e, c) in self.coefficients() {
            let d = e[var];
            for j in 0..=d {
                let mut e = e.clone();
                e[var] = j;
                let binomial = Rational::from(Natural::binomial_coefficient(
                    Natural::from(d),
                    Natural::from(j),
                ));
                let power = gpow(&value, d - j);
                let coefficient = gmul(&c, &[&power[0] * &binomial, &power[1] * &binomial]);
                res.add_term(e, coefficient);
            }
        }
        res
    }
    /// The associate of the polynomial with coprime Gaussian integer coefficients and a positive integer leading coefficient.
    ///
    /// On polynomials with rational coefficients, this is the primitive part over `{$ZZ$}` with a positive leading coefficient.
    #[must_use]
    pub fn normalized(&self) -> Self {
        if self.is_zero() {
            return self.clone();
        }
        let monic = self.scale(&gdiv(&gaussian_one(), &self.leading_coefficient()));
        let coefficients = || monic.re.terms().chain(monic.im.terms()).map(|(_, c)| c);
        let denominator = super::univariate::lcm_denominators(coefficients());
        let numerator = coefficients().fold(Natural::ZERO, |acc, c| {
            acc.gcd(c.numerator_ref() * &denominator / c.denominator_ref())
        });
        monic.scale(&[
            Rational::from(denominator) / Rational::from(numerator),
            Rational::ZERO,
        ])
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// `{$x^2 + 1$}` in one variable.
    fn x2_plus_1() -> GaussianPoly {
        let mut p = GaussianPoly::zero(1);
        p.add_term(vec![2], gaussian_one());
        p.add_term(vec![0], gaussian_one());
        p
    }

    #[test]
    fn shift_round_trip() {
        let p = x2_plus_1();
        let shifted = p.shift_imaginary(0, &Integer::from(2));
        // (x + 2i)^2 + 1 = x^2 + 4ix - 3
        let mut expected = GaussianPoly::zero(1);
        expected.add_term(vec![2], gaussian_one());
        expected.add_term(vec![1], [Rational::ZERO, Rational::from(4)]);
        expected.add_term(vec![0], [Rational::from(-3), Rational::ZERO]);
        assert_eq!(shifted, expected);
        assert_eq!(shifted.shift_imaginary(0, &Integer::from(-2)), p);
    }

    #[test]
    fn norm() {
        // (x + i)(x - i) = x^2 + 1
        let mut p = GaussianPoly::zero(1);
        p.add_term(vec![1], gaussian_one());
        p.add_term(vec![0], [Rational::ZERO, Rational::ONE]);
        assert_eq!(p.norm(), x2_plus_1().re);
    }

    #[test]
    fn normalized() {
        // (2 + 2i) x + (1 - i) / 2 = 2(1 + i) (x - i/4), associate to 4x - i
        let mut p = GaussianPoly::zero(1);
        p.add_term(vec![1], [Rational::from(2), Rational::from(2)]);
        p.add_term(
            vec![0],
            [Rational::from_signeds(1, 2), Rational::from_signeds(-1, 2)],
        );
        let mut expected = GaussianPoly::zero(1);
        expected.add_term(vec![1], [Rational::from(4), Rational::ZERO]);
        expected.add_term(vec![0], [Rational::ZERO, Rational::from(-1)]);
        assert_eq!(p.normalized(), expected);
    }
}
