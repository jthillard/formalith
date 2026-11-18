//! Complete factorization of polynomials with rational or Gaussian rational coefficients.
//!
//! Univariate polynomials are factored with the Zassenhaus algorithm (factorization modulo a prime, Hensel lifting and recombination), multivariate ones with Wang's algorithm (factorization of a univariate image and multivariate Hensel lifting).
//! Over `{$QQ(i)$}`, Trager's algorithm reduces the factorization to the one of a norm over `{$QQ$}`.

mod gaussian;
pub(crate) mod modular;
mod multivariate;
mod univariate;

use std::{collections::HashMap, fmt::Debug};

use malachite::{Integer, Rational, base::num::arithmetic::traits::Pow};

use crate::{
    field::{Ring, Set, TryElementFrom, complex::C, integer::Z, real::R},
    polynom::{Monomial, MultivariatePolynomial},
    term::{Term, TermSet},
};

use gaussian::{Gaussian, GaussianPoly, gaussian_one, gdiv, gpow};
use multivariate::{SparsePoly, WangResult};

/// Sets whose elements can be rational numbers, allowing factorization algorithms over `{$QQ$}`.
///
/// Auto implemented, returning `None` for sets without rational numbers.
pub trait RationalSet: Set {
    /// Convert an element to a rational number, if it is one.
    fn to_rational(&self, element: &Self::Element) -> Option<Rational>;
    /// Convert a rational number to an element, if it belongs to the set.
    fn from_rational(&self, value: Rational) -> Option<Self::Element>;
}

impl<T: Set> RationalSet for T {
    default fn to_rational(&self, _element: &Self::Element) -> Option<Rational> {
        None
    }
    default fn from_rational(&self, _value: Rational) -> Option<Self::Element> {
        None
    }
}

impl RationalSet for R<Rational> {
    fn to_rational(&self, element: &Self::Element) -> Option<Rational> {
        Some(element.clone())
    }
    fn from_rational(&self, value: Rational) -> Option<Self::Element> {
        Some(value)
    }
}

impl RationalSet for C<R<Rational>> {
    fn to_rational(&self, element: &Self::Element) -> Option<Rational> {
        (element[1] == 0).then(|| element[0].clone())
    }
    fn from_rational(&self, value: Rational) -> Option<Self::Element> {
        Some([value, Rational::from(0)])
    }
}

impl RationalSet for Z<Integer> {
    fn to_rational(&self, element: &Self::Element) -> Option<Rational> {
        Some(Rational::from(element))
    }
    fn from_rational(&self, value: Rational) -> Option<Self::Element> {
        Integer::try_from(value).ok()
    }
}

impl<T: Set> RationalSet for TermSet<T> {
    fn to_rational(&self, element: &Self::Element) -> Option<Rational> {
        match element {
            Term::Value(value) => self.get_set().to_rational(&value.value),
            _ => None,
        }
    }
    fn from_rational(&self, value: Rational) -> Option<Self::Element> {
        let set = *self.get_set();
        Some(Term::constant(set.from_rational(value)?, set))
    }
}

/// Sets whose elements can be Gaussian rationals `{$a + b i$}`, allowing factorization over `{$QQ(i)$}`.
///
/// Auto implemented, returning `None` for sets without Gaussian rationals.
pub trait GaussianSet: Set {
    /// Convert an element to a Gaussian rational `[re, im]`, if it is one.
    fn to_gaussian(&self, element: &Self::Element) -> Option<[Rational; 2]>;
    /// Convert a Gaussian rational `[re, im]` to an element, if it belongs to the set.
    fn from_gaussian(&self, value: [Rational; 2]) -> Option<Self::Element>;
}

impl<T: Set> GaussianSet for T {
    default fn to_gaussian(&self, _element: &Self::Element) -> Option<[Rational; 2]> {
        None
    }
    default fn from_gaussian(&self, _value: [Rational; 2]) -> Option<Self::Element> {
        None
    }
}

impl GaussianSet for C<R<Rational>> {
    fn to_gaussian(&self, element: &Self::Element) -> Option<[Rational; 2]> {
        Some(element.clone())
    }
    fn from_gaussian(&self, value: [Rational; 2]) -> Option<Self::Element> {
        Some(value)
    }
}

impl<T: Set> GaussianSet for TermSet<T> {
    fn to_gaussian(&self, element: &Self::Element) -> Option<[Rational; 2]> {
        match element {
            Term::Value(value) => self.get_set().to_gaussian(&value.value),
            _ => None,
        }
    }
    fn from_gaussian(&self, value: [Rational; 2]) -> Option<Self::Element> {
        let set = *self.get_set();
        Some(Term::constant(set.from_gaussian(value)?, set))
    }
}

impl<V: Monomial, T: Ring, U: Ring> MultivariatePolynomial<V, T, U> {
    /// Variables of the polynomial, sorted.
    fn sorted_variables(&self) -> Vec<V> {
        let mut vars: Vec<V> = self.variables().into_iter().cloned().collect();
        vars.sort_by(Monomial::monomial_cmp);
        vars
    }

    /// Convert to a sparse polynomial over `{$QQ$}` in variables `vars`, if coefficients are rational and exponents are non-negative integers.
    fn to_sparse(&self, vars: &[V]) -> Option<SparsePoly> {
        let mut res = SparsePoly::zero(vars.len());
        for (monomial, coeff) in &self.terms {
            res.add_term(
                self.exponents(vars, monomial)?,
                self.set.to_rational(coeff)?,
            );
        }
        Some(res)
    }

    /// Exponents of a monomial in variables `vars`, if they are non-negative integers.
    fn exponents(&self, vars: &[V], monomial: &[(V, U::Element)]) -> Option<Vec<u32>> {
        let mut exponents = vec![0; vars.len()];
        for (var, e) in monomial {
            let i = vars.iter().position(|v| v == var)?;
            let e = Integer::try_from(self.exponant_set.to_rational(e)?).ok()?;
            exponents[i] += u32::try_from(&e).ok()?;
        }
        Some(exponents)
    }

    /// Monomial with the given exponents in variables `vars`.
    fn monomial(&self, vars: &[V], exponents: &[u32]) -> Option<Vec<(V, U::Element)>> {
        vars.iter()
            .zip(exponents)
            .filter(|(_, e)| **e > 0)
            .map(|(v, e)| {
                Some((
                    v.clone(),
                    self.exponant_set.from_rational(Rational::from(*e))?,
                ))
            })
            .collect()
    }

    /// Convert to a sparse polynomial over `{$QQ(i)$}` in variables `vars`, if coefficients are Gaussian rationals and exponents are non-negative integers.
    fn to_gaussian_sparse(&self, vars: &[V]) -> Option<GaussianPoly> {
        let mut res = GaussianPoly::zero(vars.len());
        for (monomial, coeff) in &self.terms {
            res.add_term(
                self.exponents(vars, monomial)?,
                self.set.to_gaussian(coeff)?,
            );
        }
        Some(res)
    }

    /// Inverse of [`Self::to_gaussian_sparse`], using the sets of `self`.
    fn from_gaussian_sparse(&self, vars: &[V], p: &GaussianPoly) -> Option<Self> {
        let mut map = HashMap::new();
        for (exponents, c) in p.coefficients() {
            map.insert(self.monomial(vars, &exponents)?, self.set.from_gaussian(c)?);
        }
        Some(Self::from_term_map(map, self.set, self.exponant_set))
    }

    /// Inverse of [`Self::to_sparse`], using the sets of `self`.
    fn from_sparse(&self, vars: &[V], p: &SparsePoly) -> Option<Self> {
        let mut map = HashMap::new();
        for (exponents, c) in p.terms() {
            map.insert(
                self.monomial(vars, exponents)?,
                self.set.from_rational(c.clone())?,
            );
        }
        Some(Self::from_term_map(map, self.set, self.exponant_set))
    }

    /// Irreducible factors of a square-free polynomial with rational coefficients, primitive over `{$ZZ$}` with a positive leading coefficient.
    ///
    /// Returns `None` if the polynomial can't be converted or isn't square-free.
    fn irreducible_factors(&self, vars: &[V]) -> Option<Vec<SparsePoly>> {
        let (_, f) = self.to_sparse(vars)?.primitive();
        let n = vars.len();
        let used: Vec<usize> = (0..n).filter(|v| f.degree_in(*v) > 0).collect();
        match used.as_slice() {
            [] => Some(vec![]),
            [var] => {
                let dense = f.to_dense(*var);
                if !univariate::is_square_free(&dense) {
                    return None;
                }
                let (_, primitive) = univariate::to_primitive(&dense);
                Some(
                    univariate::zassenhaus(&primitive)
                        .iter()
                        .map(|g| SparsePoly::from_dense(n, *var, &univariate::to_q(g)))
                        .collect(),
                )
            }
            _ => {
                // The smallest degree gives the cheapest univariate factorization, and degree 1 is irreducible
                let main = *used.iter().min_by_key(|v| f.degree_in(**v))?;
                let var = &vars[main];
                let content = self.content(var);
                if !content.is_constant() {
                    let mut res = content.irreducible_factors(vars)?;
                    res.extend(self.exact_div(&content)?.irreducible_factors(vars)?);
                    return Some(res);
                }
                if f.degree_in(main) == 1 {
                    return Some(vec![f]);
                }

                let order: Vec<usize> = std::iter::once(main)
                    .chain(used.iter().copied().filter(|v| *v != main))
                    .collect();
                let (pieces, complete) = match multivariate::wang(&f.select(&order))? {
                    WangResult::Irreducible => return Some(vec![f]),
                    WangResult::Factors(pieces) => (pieces, true),
                    WangResult::Split(pieces) => (pieces, false),
                };
                let mut res = vec![];
                for piece in pieces {
                    // Remove the factor without the main variable added by lifting
                    let piece = self
                        .from_sparse(vars, &piece.unselect(n, &order))?
                        .primitive_part(var);
                    if complete {
                        res.push(piece.to_sparse(vars)?.primitive().1);
                    } else {
                        res.extend(piece.irreducible_factors(vars)?);
                    }
                }
                Some(res)
            }
        }
    }
}

impl<V, T, U: Ring> MultivariatePolynomial<V, T, U>
where
    T: Ring + TryElementFrom<U>,
    V: Monomial + TryFrom<U::Element>,
    <V as TryFrom<U::Element>>::Error: Debug,
{
    /// Factor the polynomial into irreducible factors, returning them as `(factor, multiplicity)`.
    ///
    /// When coefficients are rational and exponents are integers, the factorization is complete over `{$QQ$}`,
    /// or over `{$QQ(i)$}` when the set of coefficients contains `{$i$}` and coefficients are Gaussian rationals:
    /// - a constant comes first if it isn't one,
    /// - other factors are irreducible, with coprime (Gaussian) integer coefficients and a positive integer leading coefficient,
    /// - factors are sorted by multiplicity, then by degree.
    ///
    /// Otherwise, the square-free factorization is returned.
    pub fn factor(&self) -> Vec<(Self, u32)> {
        self.complete_factorization()
            .unwrap_or_else(|| self.square_free_factorization())
    }

    fn complete_factorization(&self) -> Option<Vec<(Self, u32)>> {
        let i: Gaussian = [Rational::from(0), Rational::from(1)];
        if self.set.from_gaussian(i).is_some() {
            return self.gaussian_factorization();
        }
        let vars = self.sorted_variables();
        let sparse = self.to_sparse(&vars)?;
        if sparse.is_zero() {
            return None;
        }
        // Factors have positive leading coefficients, the constant is the remaining one
        let mut constant = sparse.leading_coefficient();
        let mut factors = vec![];
        for (f, multiplicity) in self.square_free_factorization() {
            if f.to_sparse(&vars)?.is_constant() {
                continue;
            }
            for g in f.irreducible_factors(&vars)? {
                constant /= g.leading_coefficient().pow(u64::from(multiplicity));
                factors.push((g, multiplicity));
            }
        }
        factors.sort_by_key(|(g, multiplicity)| (*multiplicity, g.total_degree()));

        let mut res = vec![];
        if constant != 1u32 {
            let constant = self.set.from_rational(constant)?;
            res.push((Self::constant(constant, self.set, self.exponant_set), 1));
        }
        for (g, multiplicity) in factors {
            res.push((self.from_sparse(&vars, &g)?, multiplicity));
        }
        Some(res)
    }

    /// Complete factorization over `{$QQ(i)$}`, see [`Self::factor`].
    fn gaussian_factorization(&self) -> Option<Vec<(Self, u32)>> {
        let vars = self.sorted_variables();
        let sparse = self.to_gaussian_sparse(&vars)?;
        if sparse.is_zero() {
            return None;
        }
        // Factors have positive integer leading coefficients, the constant is the remaining one
        let mut constant = sparse.leading_coefficient();
        let mut factors = vec![];
        for (f, multiplicity) in self.square_free_factorization() {
            if f.to_gaussian_sparse(&vars)?.is_constant() {
                continue;
            }
            for g in f.gaussian_irreducible_factors(&vars)? {
                constant = gdiv(&constant, &gpow(&g.leading_coefficient(), multiplicity));
                factors.push((g, multiplicity));
            }
        }
        factors.sort_by_key(|(g, multiplicity)| (*multiplicity, g.total_degree()));

        let mut res = vec![];
        if constant != gaussian_one() {
            let constant = self.set.from_gaussian(constant)?;
            res.push((Self::constant(constant, self.set, self.exponant_set), 1));
        }
        for (g, multiplicity) in factors {
            res.push((self.from_gaussian_sparse(&vars, &g)?, multiplicity));
        }
        Some(res)
    }

    /// Irreducible factors over `{$QQ(i)$}` of a square-free polynomial with Gaussian rational coefficients, normalized with [`GaussianPoly::normalized`].
    ///
    /// Uses Trager's algorithm: after a shift `{$x -> x - s i$}` of the main variable making the norm `{$g overline(g)$}` square-free,
    /// the factors are the gcds of `{$g$}` with the irreducible factors of the norm over `{$QQ$}`, shifted back.
    ///
    /// Returns `None` if the polynomial can't be converted or a step fails.
    fn gaussian_irreducible_factors(&self, vars: &[V]) -> Option<Vec<GaussianPoly>> {
        let f = self.to_gaussian_sparse(vars)?;
        let Some(main) = (0..vars.len())
            .filter(|v| f.degree_in(*v) > 0)
            .min_by_key(|v| f.degree_in(*v))
        else {
            return Some(vec![]);
        };
        let var = &vars[main];
        // Every factor must contain the main variable, otherwise the norm is never square-free
        let content = self.content(var);
        if !content.is_constant() {
            let mut res = content.gaussian_irreducible_factors(vars)?;
            res.extend(
                self.exact_div(&content)?
                    .gaussian_irreducible_factors(vars)?,
            );
            return Some(res);
        }
        if f.degree_in(main) == 1 {
            return Some(vec![f.normalized()]);
        }

        // All but finitely many shifts give a square-free norm, try 0, 1, -1, 2, -2, ...
        let bound = i64::from(f.degree_in(main)).pow(2) + 2;
        for s in (0..=bound).flat_map(|s| [s, -s]).skip(1) {
            let s = Integer::from(s);
            let g = f.shift_imaginary(main, &-&s);
            let norm = self.from_sparse(vars, &g.norm())?;
            // Factors of the norm all contain the main variable
            if !norm.gcd(&norm.derivative(var)).is_constant() {
                continue;
            }
            let norm_factors = norm.irreducible_factors(vars)?;
            if norm_factors.len() <= 1 {
                return Some(vec![f.normalized()]);
            }
            let g = self.from_gaussian_sparse(vars, &g)?;
            let mut res = vec![];
            for h in norm_factors {
                let d = g
                    .gcd(&self.from_sparse(vars, &h)?)
                    .to_gaussian_sparse(vars)?;
                if d.is_constant() {
                    return None;
                }
                res.push(d.shift_imaginary(main, &s).normalized());
            }
            // `gcd` returns one when it fails, check that no factor is missing
            let degree: u32 = res.iter().map(GaussianPoly::total_degree).sum();
            return (degree == f.total_degree()).then_some(res);
        }
        None
    }
}
