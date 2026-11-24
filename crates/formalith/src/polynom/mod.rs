//! Polynom implementation

pub(crate) mod dense;
pub mod factor;
pub(crate) mod fraction;
pub(crate) mod real_roots;

use std::{
    cmp::Ordering,
    collections::{HashMap, HashSet},
    fmt::{Debug, Display},
    hash::Hash,
};

use crate::{
    field::{Group, Ring, Set, TryElementFrom},
    iter,
    printer::{PrettyPrint, PrettyPrinter, Print, PrintOptions},
    term::{Term, TermSet},
};

/// Types must implement this trait to be used as variables inside polynomials.
///
/// Auto implemented.
pub trait Monomial: Debug + Clone + PartialEq + Eq + Hash + PartialOrd + PrettyPrint {
    /// Total order used to sort variables, so that polynomials have a canonical form.
    fn monomial_cmp(&self, other: &Self) -> Ordering;
}

impl<T: Debug + Clone + PartialEq + Eq + Hash + PartialOrd + PrettyPrint> Monomial for T {
    default fn monomial_cmp(&self, other: &Self) -> Ordering {
        self.partial_cmp(other).unwrap_or(Ordering::Equal)
    }
}

impl<T: Group> Monomial for Term<T> {
    fn monomial_cmp(&self, other: &Self) -> Ordering {
        // Terms are only partially ordered (distinct symbols are not comparable), use the structural order.
        // Symbol ids depend on the order symbols were created in (nondeterministic across threads), so symbols
        // are compared by name: the leading variable, hence the sign of factors, must not depend on it.
        match (self, other) {
            (Self::Symbol(s1), Self::Symbol(s2)) => s1
                .symbol
                .name()
                .cmp(s2.symbol.name())
                .then_with(|| s1.symbol.cmp(&s2.symbol)),
            _ => self.cmp(other),
        }
    }
}

type Monom<V, U> = (V, <U as Set>::Element);
type PolynomElement<V, U, T> = (Vec<Monom<V, U>>, <T as Set>::Element);

/// A multivariate polynomial, living in `T` with exponant in `U`. Variables can be any type implementing [Monomial], like [`crate::context::Symbol`] or [Term].
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct MultivariatePolynomial<V, T: Set, U: Set> {
    terms: Vec<PolynomElement<V, U, T>>,
    set: T,
    exponant_set: U,
}

impl<V, T: Set, U: Set> MultivariatePolynomial<V, T, U> {
    /// Create a new polynomial from its terms and sets.
    pub const fn new(terms: Vec<PolynomElement<V, U, T>>, set: T, exponant_set: U) -> Self {
        Self {
            terms,
            set,
            exponant_set,
        }
    }
    /// Get the terms of the polynomial, as `(monomial, coefficient)` pairs.
    pub(crate) fn terms(&self) -> &[PolynomElement<V, U, T>] {
        &self.terms
    }

    /// Check if the polynom is a constant.
    pub fn is_constant(&self) -> bool {
        self.terms.len() == 1 && self.terms[0].0.is_empty()
    }

    /// Create a new constant polynomial.
    pub fn constant(coeff: T::Element, set: T, exponant_set: U) -> Self {
        Self {
            terms: vec![(vec![], coeff)],
            set,
            exponant_set,
        }
    }
}

impl<V, T: Group, U: Set> MultivariatePolynomial<V, T, U> {
    /// Check if the polynom is the constant 0
    pub fn is_zero(&self) -> bool {
        self.terms.is_empty() || self.terms.iter().all(|(_, c)| self.set.is_zero(c))
    }

    /// Create a new constant polynomial equal to zero.
    pub fn zero(set: T, exponant_set: U) -> Self {
        Self::constant(set.zero(), set, exponant_set)
    }
}

impl<V, T: Ring, U: Ring> MultivariatePolynomial<V, T, U> {
    /// Create a new monomial containing `var`.
    pub fn variable(var: V, set: T, exponant_set: U) -> Self {
        Self {
            terms: vec![(vec![(var, exponant_set.one())], set.one())],
            set,
            exponant_set,
        }
    }
}

impl<V, T: Ring, U: Set> MultivariatePolynomial<V, T, U> {
    /// Check if the polynom is the constant 1
    pub fn is_one(&self) -> bool {
        self.is_constant() && self.set.is_one(&self.terms[0].1)
    }
    /// Create a new constant polynomial equal to one.
    pub fn one(set: T, exponant_set: U) -> Self {
        Self::constant(set.one(), set, exponant_set)
    }
}

impl<V: Monomial, T: Set, U: Set> MultivariatePolynomial<V, T, U> {
    /// Get the variables appearing in the polynom.
    pub fn variables(&self) -> HashSet<&V> {
        self.terms
            .iter()
            .flat_map(|(vars, _)| vars.iter().map(|(var, _)| var))
            .collect()
    }
}

impl<V: Monomial, T: Set, U: Group> MultivariatePolynomial<V, T, U> {
    fn combine_vars(
        vars1: &[(V, U::Element)],
        vars2: &[(V, U::Element)],
        exponant_set: U,
    ) -> Vec<(V, U::Element)> {
        let mut combined = HashMap::new();

        for (v, e) in vars1.iter().chain(vars2.iter()) {
            *combined.entry(v.clone()).or_insert(exponant_set.zero()) =
                exponant_set.add(combined.get(v).unwrap_or(&exponant_set.zero()), e);
        }

        let mut sorted: Vec<_> = combined.into_iter().collect();

        sorted.sort_by(|a, b| a.0.monomial_cmp(&b.0));
        sorted
    }

    /// Separate the polynom on a variable
    pub fn separate_variable(&self, var: &V) -> (Vec<Self>, Vec<U::Element>) {
        let mut coefficients = Vec::new();
        let mut exponents = Vec::new();

        for (vars, coeff) in &self.terms {
            let mut var_exponents = vars
                .iter()
                .filter(|(v, _)| v == var)
                .map(|(_, e)| e.clone())
                .collect::<Vec<_>>();

            let exp = var_exponents.pop().unwrap_or(self.exponant_set.zero());
            let remaining_vars = vars.iter().filter(|(v, _)| v != var).cloned().collect();

            coefficients.push(Self {
                terms: vec![(remaining_vars, coeff.clone())],
                set: self.set,
                exponant_set: self.exponant_set,
            });
            exponents.push(exp);
        }

        (coefficients, exponents)
    }

    /// Get the leading monomial
    ///
    /// # Panics
    /// Panics if the polynom is empty.
    pub fn leading_term(&self) -> PolynomElement<V, U, T> {
        self.terms.first().cloned().expect("Aucun terme")
    }
}

/// Trait used to convert polynomials to expressions
pub trait ToTerm<Out: Set> {
    /// Convert the polynomial to an expression
    fn to_term(&self) -> Term<Out>;
}

impl<V: Monomial, T: Ring, U: Set> ToTerm<T> for MultivariatePolynomial<V, T, U>
where
    Term<T>: From<V>,
    Term<T::ExponantSet>: From<U::Element>,
{
    fn to_term(&self) -> Term<T> {
        let mut res = Term::zero(self.set);
        for monomial in &self.terms {
            let mut term = Term::one(self.set);
            for (var, exp) in &monomial.0 {
                term *= Term::from(var.clone()).pow(&Term::from(exp.clone()));
            }
            term *= Term::constant(monomial.1.clone(), self.set);
            res += term;
        }
        res
    }
}
impl<T: Ring> ToTerm<T> for MultivariatePolynomial<Term<T>, TermSet<T>, TermSet<T::ExponantSet>> {
    fn to_term(&self) -> Term<T> {
        let mut res = Term::zero(*self.set.get_set());
        for monomial in &self.terms {
            let mut term = Term::one(*self.set.get_set());
            for (var, exp) in &monomial.0 {
                term *= var.clone().pow(&exp.clone());
            }
            term *= monomial.1.clone();
            res += term;
        }
        res
    }
}

impl<V, T, U: Ring> MultivariatePolynomial<V, T, U>
where
    T: Ring + TryElementFrom<U>,
    V: Monomial + TryFrom<U::Element>,
    <V as TryFrom<U::Element>>::Error: Debug,
{
    /// Computes the derivative of self according to `var`
    ///
    /// # Panics
    /// Panics if an exponant is not convertible into `T` or `V`.
    #[must_use]
    pub fn derivative(&self, var: &V) -> Self {
        let mut terms = Vec::new();

        for (vars, coeff) in &self.terms {
            let mut new_vars = vars.clone();

            for (i, (v, exp)) in new_vars.iter_mut().enumerate() {
                if v == var {
                    let new_exp = self.exponant_set.sub(exp, &self.exponant_set.one());
                    let new_coeff = T::try_from_element(exp.clone()).map_or_else(
                        |_| {
                            // Convert exponent to variable
                            terms.push((
                                vec![(
                                    V::try_from(exp.clone())
                                        .expect("Exponent must be convertible to T or V"),
                                    self.exponant_set.one(),
                                )],
                                self.set.one(),
                            ));
                            coeff.clone()
                        },
                        |c| self.set.mul(coeff, &c),
                    );

                    if self.exponant_set.is_zero(&new_exp) {
                        new_vars.remove(i);
                    } else {
                        *exp = new_exp;
                    }

                    terms.push((new_vars, new_coeff));
                    break;
                }
            }
        }

        Self {
            terms,
            set: self.set,
            exponant_set: self.exponant_set,
        }
    }
}

impl<V: Monomial, T: Set, U: Group> MultivariatePolynomial<V, T, U>
where
    U::Element: Ord,
{
    /// Compute the degree of the polynomial.
    pub fn degree(&self) -> U::Element {
        self.terms
            .iter()
            .map(|(vars, _)| {
                vars.iter()
                    .map(|(_, e)| e.clone())
                    .fold(self.exponant_set.zero(), |a, b| {
                        self.exponant_set.add(&a, &b)
                    })
            })
            .max()
            .unwrap_or(self.exponant_set.zero())
    }
}
impl<V: Monomial, T: Ring, U: Ring> MultivariatePolynomial<V, T, U> {
    /// Create a polynom from a hashmap which associate monomial to its coefficient
    fn from_term_map(
        map: HashMap<Vec<(V, U::Element)>, T::Element>,
        set: T,
        exponant_set: U,
    ) -> Self {
        let mut res = Self {
            terms: map.into_iter().collect(),
            set,
            exponant_set,
        };
        Self::normalize(&mut res);
        res
    }
    fn from_term(term: PolynomElement<V, U, T>, set: T, exponant_set: U) -> Self {
        let mut res = Self {
            terms: vec![term],
            set,
            exponant_set,
        };
        Self::normalize(&mut res);
        res
    }

    /// Normalize the polynomial.
    pub fn normalize(&mut self) {
        // Remove monomials
        self.terms.retain(|(_, coeff)| !self.set.is_zero(coeff));
        // Sort variables in monomials
        self.terms.iter_mut().for_each(|monomial| {
            // Remove variables
            monomial.0.retain(|(_, e)| !self.exponant_set.is_zero(e));
            monomial.0.sort_by(|a, b| a.0.monomial_cmp(&b.0));
        });
        // Sort monomials
        self.terms.sort_by(|a, b| {
            iter::cmp_by(
                b.0.iter().map(|(_, e)| e),
                a.0.iter().map(|(_, e)| e),
                |a, b| self.exponant_set.total_cmp(a, b),
            )
            .then_with(|| {
                // Break ties on variables, like `x^2` and `y^2`
                iter::cmp_by(
                    a.0.iter().map(|(v, _)| v),
                    b.0.iter().map(|(v, _)| v),
                    Monomial::monomial_cmp,
                )
            })
        });
    }

    /// Euclidian division of a monomial by another
    fn quot_rem_monomial(
        num_vars: &[(V, U::Element)],
        num_coeff: &T::Element,
        denom_vars: &[(V, U::Element)],
        denom_coeff: &T::Element,
        set: T,
        exponant_set: U,
    ) -> Option<PolynomElement<V, U, T>> {
        let denom_inv = set.try_inv(denom_coeff).unwrap();
        let q_coeff = set.mul(num_coeff, &denom_inv);

        let mut var_map: HashMap<_, _> = num_vars.iter().cloned().collect();
        for (v, e) in denom_vars {
            {
                let current_exp = var_map.get_mut(v)?;
                let difference = exponant_set.sub(current_exp, e);
                let divides = exponant_set.partial_cmp(current_exp, e).map_or_else(
                    // Symbolic exponants, like `x^(2*n)` divided by `x^n`: the difference must be exact and not negative
                    || {
                        exponant_set.element_eq(&exponant_set.add(&difference, e), current_exp)
                            && !exponant_set.is_strictly_negative(&difference)
                    },
                    |ordering| ordering != Ordering::Less,
                );
                if !divides {
                    return None;
                }
                *current_exp = difference;
                if exponant_set.is_zero(current_exp) {
                    var_map.remove(v);
                }
            }
        }

        let mut q_vars: Vec<_> = var_map.into_iter().collect();
        q_vars.sort_unstable_by(|a, b| a.0.monomial_cmp(&b.0));

        Some((q_vars, q_coeff))
    }

    /// Euclidian division, returning quotient and remainder
    pub fn quot_rem(&self, divisor: &Self) -> (Self, Self) {
        let (quotient, remainder, _) = self.quot_rem_checked(divisor);
        (quotient, remainder)
    }

    /// Euclidian division, also returning `false` if some leading terms didn't cancel, which happens with symbolic coefficients.
    fn quot_rem_checked(&self, divisor: &Self) -> (Self, Self, bool) {
        let mut quotient = Self::zero(self.set, self.exponant_set);
        let mut remainder = Self::zero(self.set, self.exponant_set);
        let mut current_dividend = self.clone();
        let mut exact = true;

        while !current_dividend.is_zero() {
            let (lead_vars, lead_coeff) = current_dividend.leading_term();
            let (div_vars, div_coeff) = divisor.leading_term();

            if let Some((q_vars, q_coeff)) = Self::quot_rem_monomial(
                &lead_vars,
                &lead_coeff,
                &div_vars,
                &div_coeff,
                self.set,
                self.exponant_set,
            ) {
                let term_poly = Self::from_term((q_vars, q_coeff), self.set, self.exponant_set);

                quotient = &quotient + &term_poly;

                let to_subtract = &term_poly * divisor;
                current_dividend = &current_dividend - &to_subtract;
                // A symbolic coefficient times its inverse may not simplify, move what is left to the remainder to terminate
                if let Some(i) = current_dividend
                    .terms
                    .iter()
                    .position(|(vars, _)| *vars == lead_vars)
                {
                    let leftover = current_dividend.terms.remove(i);
                    remainder = remainder + &Self::from_term(leftover, self.set, self.exponant_set);
                    exact = false;
                }
            } else {
                let term = Self::from_term((lead_vars, lead_coeff), self.set, self.exponant_set);
                remainder = remainder + &term;
                current_dividend = &current_dividend - &term;
            }
        }

        (quotient, remainder, exact)
    }
    /// Divide the polynomial by its leading coefficient.
    ///
    /// # Panics
    /// Panics if the leading coefficient is not invertible.
    #[must_use]
    pub fn monic(self) -> Self {
        if self.is_zero() {
            return self;
        }
        // Symbolic coefficients times their inverse may not simplify to one
        if self.is_constant() {
            return Self::one(self.set, self.exponant_set);
        }
        let leading_coeff = self.leading_term().1;
        if self.set.is_one(&leading_coeff) {
            return self;
        }
        &self
            * &Self::constant(
                self.set.try_inv(&leading_coeff).unwrap(),
                self.set,
                self.exponant_set,
            )
    }

    /// Compute GCD between self and other, normalized with a leading coefficient equal to one.
    ///
    /// Univariate polynomials use the euclide algorithm, multivariate ones a recursive algorithm on their main variable.
    ///
    /// # Panics
    /// Panics if the leading coefficient is not invertible.
    #[must_use]
    pub fn gcd(&self, other: &Self) -> Self {
        if self.is_zero() {
            return other.clone().monic();
        }
        if other.is_zero() {
            return self.clone().monic();
        }
        if self.is_constant() || other.is_constant() {
            return Self::one(self.set, self.exponant_set);
        }
        if self.variables().union(&other.variables()).count() > 1
            && let Some(var) = self.gcd_variable(other)
        {
            return self.multivariate_gcd(other, &var);
        }

        let (mut a, mut b) = (self.clone(), other.clone());
        let mut previous_quotient_zero = false;
        while !b.is_zero() {
            let (quotient, remainder, exact) = a.quot_rem_checked(&b);
            // Without progress the gcd is unknown, consider polynomials coprime
            if !exact || (quotient.is_zero() && previous_quotient_zero) {
                return Self::one(self.set, self.exponant_set);
            }
            previous_quotient_zero = quotient.is_zero();
            (a, b) = (b, remainder);
        }
        a.monic()
    }

    /// GCD of the contents times the GCD of the primitive parts, computed with pseudo-remainders on `var`.
    fn multivariate_gcd(&self, other: &Self, var: &V) -> Self {
        let (self_content, other_content) = (self.content(var), other.content(var));
        let content = self_content.gcd(&other_content);
        let primitive_gcd = (|| {
            let mut a = self.exact_div(&self_content)?;
            let mut b = other.exact_div(&other_content)?;
            while !b.is_zero() {
                let remainder = a.pseudo_rem(&b, var)?;
                a = b;
                b = if remainder.is_zero() {
                    remainder
                } else {
                    remainder.primitive_part(var)
                };
            }
            Some(a.primitive_part(var))
        })();
        match primitive_gcd {
            Some(primitive_gcd) => (&content * &primitive_gcd).monic(),
            None => content,
        }
    }

    /// Smallest variable appearing in `self` or `other`.
    fn main_variable(&self, other: &Self) -> Option<V> {
        self.variables()
            .union(&other.variables())
            .min_by(|a, b| a.monomial_cmp(b))
            .map(|var| (*var).clone())
    }

    /// Variable of lowest degree in `self` and `other`, the cheapest to compute a gcd on.
    ///
    /// Variables whose degree can't be determined come last, ties are broken by the variable order.
    fn gcd_variable(&self, other: &Self) -> Option<V> {
        let mut vars: Vec<&V> = self
            .variables()
            .union(&other.variables())
            .copied()
            .collect();
        vars.sort_by(|a, b| a.monomial_cmp(b));
        let degree = |var: &V| {
            let (a, b) = (self.degree_in(var)?, other.degree_in(var)?);
            match self.exponant_set.partial_cmp(&a, &b)? {
                Ordering::Less => Some(b),
                _ => Some(a),
            }
        };
        let mut best: Option<(&V, Option<U::Element>)> = None;
        for var in vars {
            let d = degree(var);
            let is_better = match (&best, &d) {
                (None, _) | (Some((_, None)), Some(_)) => true,
                (Some((_, Some(best))), Some(d)) => {
                    self.exponant_set.partial_cmp(d, best) == Some(Ordering::Less)
                }
                _ => false,
            };
            if is_better {
                best = Some((var, d));
            }
        }
        best.map(|(var, _)| var.clone())
    }

    /// Degree in `var`, `None` if exponants can't be compared.
    fn degree_in(&self, var: &V) -> Option<U::Element> {
        let mut degree = self.exponant_set.zero();
        for (vars, _) in &self.terms {
            if let Some((_, e)) = vars.iter().find(|(v, _)| v == var)
                && self.exponant_set.partial_cmp(e, &degree)? == Ordering::Greater
            {
                degree = e.clone();
            }
        }
        Some(degree)
    }

    /// The polynomial `var^exponant`.
    fn var_power(&self, var: &V, exponant: U::Element) -> Self {
        Self::from_term(
            (vec![(var.clone(), exponant)], self.set.one()),
            self.set,
            self.exponant_set,
        )
    }

    /// Coefficients of the polynomial seen as a polynomial in `var`, as `(exponant, coefficient)`, highest exponants first.
    fn coefficients_in(&self, var: &V) -> Vec<(U::Element, Self)> {
        let mut coefficients: Vec<(U::Element, Self)> = vec![];
        for (vars, coeff) in &self.terms {
            let exponant = vars
                .iter()
                .find(|(v, _)| v == var)
                .map_or_else(|| self.exponant_set.zero(), |(_, e)| e.clone());
            let other_vars = vars.iter().filter(|(v, _)| v != var).cloned().collect();
            let term = Self::from_term((other_vars, coeff.clone()), self.set, self.exponant_set);
            if let Some((_, coefficient)) = coefficients
                .iter_mut()
                .find(|(e, _)| self.exponant_set.element_eq(e, &exponant))
            {
                let sum = &*coefficient + &term;
                *coefficient = sum;
            } else {
                coefficients.push((exponant, term));
            }
        }
        coefficients.sort_by(|(a, _), (b, _)| self.exponant_set.total_cmp(b, a));
        coefficients
    }

    /// Degree and leading coefficient in `var`, `None` if the polynomial is zero or its degree can't be determined.
    fn leading_in(&self, var: &V) -> Option<(U::Element, Self)> {
        let mut coefficients = self.coefficients_in(var).into_iter();
        let leading = coefficients.next()?;
        coefficients
            .all(|(e, _)| self.exponant_set.partial_cmp(&leading.0, &e) == Some(Ordering::Greater))
            .then_some(leading)
    }

    /// Compute the LCM of self and other, `{$a b / gcd(a, b)$}` made monic, or 0 if one of them is 0. Returns `None`
    /// when the division by the GCD isn't exact.
    ///
    /// # Panics
    /// Panics if a leading coefficient is not invertible.
    #[must_use]
    pub fn lcm(&self, other: &Self) -> Option<Self> {
        if self.is_zero() || other.is_zero() {
            return Some(Self::zero(self.set, self.exponant_set));
        }
        Some((self.exact_div(&self.gcd(other))? * other.clone()).monic())
    }

    /// Divide the polynomial by `divisor`, returning `None` if the division is not exact.
    #[must_use]
    pub fn exact_div(&self, divisor: &Self) -> Option<Self> {
        if divisor.is_zero() {
            return None;
        }
        if divisor.is_constant() {
            let inverse = self.set.try_inv(&divisor.terms[0].1)?;
            return Some(self * &Self::constant(inverse, self.set, self.exponant_set));
        }
        let var = self.main_variable(divisor)?;
        let (divisor_degree, divisor_leading) = divisor.leading_in(&var)?;

        let mut quotient = Self::zero(self.set, self.exponant_set);
        let mut remainder = self.clone();
        let mut previous_degree = None;
        while !remainder.is_zero() {
            let (degree, leading) = remainder.leading_in(&var)?;
            // The degree must decrease for the division to terminate
            if previous_degree.is_some_and(|previous| {
                self.exponant_set.partial_cmp(&degree, &previous) != Some(Ordering::Less)
            }) || !matches!(
                self.exponant_set.partial_cmp(&divisor_degree, &degree),
                Some(Ordering::Less | Ordering::Equal)
            ) {
                return None;
            }
            // Leading coefficients don't contain `var`, so this recursion has fewer variables
            let term = &leading.exact_div(&divisor_leading)?
                * &self.var_power(&var, self.exponant_set.sub(&degree, &divisor_degree));
            remainder = &remainder - &(&term * divisor);
            quotient = quotient + term;
            previous_degree = Some(degree);
        }
        Some(quotient)
    }

    /// Pseudo-remainder of the division by `divisor`, seen as polynomials in `var`.
    ///
    /// Returns `None` if degrees can't be compared.
    fn pseudo_rem(&self, divisor: &Self, var: &V) -> Option<Self> {
        let (divisor_degree, divisor_leading) = divisor.leading_in(var)?;
        let mut remainder = self.clone();
        let mut previous_degree = None;
        while !remainder.is_zero() {
            let (degree, leading) = remainder.leading_in(var)?;
            if previous_degree.is_some_and(|previous| {
                self.exponant_set.partial_cmp(&degree, &previous) != Some(Ordering::Less)
            }) {
                return None;
            }
            match self.exponant_set.partial_cmp(&degree, &divisor_degree) {
                Some(Ordering::Less) => break,
                None => return None,
                _ => {}
            }
            // Cancel the leading term: lc(d) * r - lc(r) * var^(deg r - deg d) * d
            let shift = self.var_power(var, self.exponant_set.sub(&degree, &divisor_degree));
            remainder = &(&divisor_leading * &remainder) - &(&(&leading * &shift) * divisor);
            previous_degree = Some(degree);
        }
        Some(remainder)
    }

    /// Compute the content of a polynom, the gcd of its coefficients as a polynomial in `var`.
    #[must_use]
    pub fn content(&self, var: &V) -> Self {
        self.coefficients_in(var)
            .into_iter()
            .fold(Self::zero(self.set, self.exponant_set), |acc, (_, x)| {
                acc.gcd(&x)
            })
    }
    /// Primitive part of the polynomial
    #[must_use]
    pub fn primitive_part(&self, var: &V) -> Self {
        self.divide(&self.content(var))
    }
    /// Divide by a factor of the polynomial, falling back to the euclidian division when the exact division fails.
    fn divide(&self, divisor: &Self) -> Self {
        self.exact_div(divisor)
            .unwrap_or_else(|| self.quot_rem(divisor).0)
    }
}

impl<V: Monomial, T: Ring, U: Ring> std::ops::Add for &MultivariatePolynomial<V, T, U> {
    type Output = MultivariatePolynomial<V, T, U>;

    fn add(self, rhs: Self) -> Self::Output {
        // Polynomial must be already normalized
        let mut term_map = HashMap::new();

        for (vars, coeff) in &self.terms {
            *term_map.entry(vars.clone()).or_insert(self.set.zero()) = self
                .set
                .add(term_map.get(vars).unwrap_or(&self.set.zero()), coeff);
        }

        for (vars, coeff) in &rhs.terms {
            *term_map.entry(vars.clone()).or_insert(self.set.zero()) = self
                .set
                .add(term_map.get(vars).unwrap_or(&self.set.zero()), coeff);
        }

        MultivariatePolynomial::from_term_map(term_map, self.set, self.exponant_set)
    }
}

impl<V: Monomial, T: Ring, U: Ring> std::ops::Add for MultivariatePolynomial<V, T, U> {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        &self + &rhs
    }
}

impl<V: Monomial, T: Ring, U: Ring> std::ops::Add<&Self> for MultivariatePolynomial<V, T, U> {
    type Output = Self;

    fn add(self, rhs: &Self) -> Self::Output {
        &self + rhs
    }
}

impl<V: Monomial, T: Ring, U: Ring> std::ops::Mul for &MultivariatePolynomial<V, T, U> {
    type Output = MultivariatePolynomial<V, T, U>;

    fn mul(self, rhs: Self) -> Self::Output {
        let mut term_map = HashMap::new();

        for (vars1, coeff1) in &self.terms {
            for (vars2, coeff2) in &rhs.terms {
                let combined_vars = MultivariatePolynomial::<V, T, U>::combine_vars(
                    vars1,
                    vars2,
                    self.exponant_set,
                );
                let product_coeff = self.set.mul(coeff1, coeff2);

                *term_map.entry(combined_vars).or_insert(self.set.zero()) = self.set.add(
                    term_map.get(&combined_vars).unwrap_or(&self.set.zero()),
                    &product_coeff,
                );
            }
        }

        MultivariatePolynomial::<V, T, U>::from_term_map(term_map, self.set, self.exponant_set)
    }
}

impl<V: Monomial, T: Ring, U: Ring> std::ops::Mul for MultivariatePolynomial<V, T, U> {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self::Output {
        &self * &rhs
    }
}

impl<V: Monomial, T: Ring, U: Ring> std::ops::Mul<&Self> for MultivariatePolynomial<V, T, U> {
    type Output = Self;

    fn mul(self, rhs: &Self) -> Self::Output {
        &self * rhs
    }
}

impl<V: Monomial, T: Ring, U: Ring> std::ops::Sub for &MultivariatePolynomial<V, T, U> {
    type Output = MultivariatePolynomial<V, T, U>;

    fn sub(self, rhs: Self) -> Self::Output {
        let mut term_map = HashMap::new();

        for (vars, coeff) in &self.terms {
            *term_map.entry(vars.clone()).or_insert(self.set.zero()) = self
                .set
                .add(term_map.get(vars).unwrap_or(&self.set.zero()), coeff);
        }

        for (vars, coeff) in &rhs.terms {
            *term_map.entry(vars.clone()).or_insert(self.set.zero()) = self
                .set
                .sub(term_map.get(vars).unwrap_or(&self.set.zero()), coeff);
        }

        MultivariatePolynomial::<V, T, U>::from_term_map(term_map, self.set, self.exponant_set)
    }
}

impl<V, T, U: Ring> MultivariatePolynomial<V, T, U>
where
    T: Ring + TryElementFrom<U>,
    V: Monomial + TryFrom<U::Element>,
    <V as TryFrom<U::Element>>::Error: Debug,
{
    /// Return square free factors as `(factor, multiplicity)`
    pub fn square_free_factorization(&self) -> Vec<(Self, u32)> {
        let mut factors = Vec::new();

        if self.is_constant() {
            return vec![(self.clone(), 1)];
        }

        let main_var = self.choose_main_variable();

        let content = self.content(&main_var);
        let primitive_part = self.primitive_part(&main_var);

        for (factor, power) in content.square_free_factorization() {
            factors.push((factor, power));
        }
        let content_factors = factors.len();

        let derivative = primitive_part.derivative(&main_var);
        let gcd = primitive_part.gcd(&derivative);

        // Factors not containing the main variable are in the content
        let mut current = primitive_part.divide(&gcd);
        let mut current_derivative = derivative.divide(&gcd);
        let mut multiplicity = 1;

        // Multiplicities are bounded by the degree, coefficients that don't cancel could exceed it
        let degree = primitive_part.degree_in(&main_var);
        while !current.is_constant() {
            if degree.as_ref().is_some_and(|degree| {
                self.exponant_set
                    .partial_cmp(&self.exponant_set.nth(multiplicity.into()), degree)
                    == Some(Ordering::Greater)
            }) {
                factors.truncate(content_factors);
                factors.push((primitive_part, 1));
                break;
            }
            let tmp = &current_derivative - &current.derivative(&main_var);
            let g = current.gcd(&tmp);
            current = current.divide(&g);
            current_derivative = tmp.divide(&g);

            if !g.is_one() {
                factors.push((g, multiplicity));
            }

            multiplicity += 1;
        }

        factors.retain(|(elem, _)| !elem.is_one());

        factors
    }

    fn choose_main_variable(&self) -> V {
        let mut var_counts = HashMap::new();
        for (vars, _) in &self.terms {
            for (v, e) in vars {
                if !self.exponant_set.is_zero(e) {
                    *var_counts.entry(v.clone()).or_insert(0) += 1;
                }
            }
        }
        var_counts
            .into_iter()
            // Break ties on the variable order, as the hashmap order is random
            .max_by(|(v1, c1), (v2, c2)| c1.cmp(c2).then_with(|| v2.monomial_cmp(v1)))
            .map(|(v, _)| v)
            .expect("Polynomial must contain at least one variable")
    }
}

impl<V: Monomial, T: Ring, U: Set> Print for MultivariatePolynomial<V, T, U> {
    fn print(&self, options: &PrintOptions, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.terms.is_empty() {
            return self.set.print(&self.set.zero(), options, f);
        }
        for (j, (vars, coeff)) in self.terms.iter().enumerate() {
            let has_coeff = !self.set.is_one(coeff) || vars.is_empty();
            if has_coeff {
                self.set.print(coeff, options, f)?;
            }

            for (i, (var, exponant)) in vars.iter().enumerate() {
                if i == 0 && !has_coeff {
                } else {
                    write!(f, "{}", if options.typst { " " } else { "*" })?;
                }
                var.print(options, f)?;
                write!(f, "^")?;
                self.exponant_set.print(exponant, options, f)?;
            }
            // Negative coefficients already print their sign
            if let Some((_, next_coeff)) = self.terms.get(j + 1)
                && !self.set.is_strictly_negative(next_coeff)
            {
                write!(f, "+")?;
            }
        }
        Ok(())
    }
}
impl<V: Monomial, T: Ring, U: Ring> PrettyPrint for MultivariatePolynomial<V, T, U> {
    fn pretty_print(&self, options: &PrintOptions) -> PrettyPrinter {
        if self.terms.is_empty() {
            return self.set.pretty_print(&self.set.zero(), options);
        }
        let mut res = PrettyPrinter::empty();
        for (j, (vars, coeff)) in self.terms.iter().enumerate() {
            // Print `a - b` instead of `a + -b`
            let negative = j != 0 && self.set.is_strictly_negative(coeff);
            let coeff = &if negative {
                self.set.neg(coeff)
            } else {
                coeff.clone()
            };
            let has_coeff = !self.set.is_one(coeff) || vars.is_empty();
            let mut coeff = if has_coeff {
                self.set.pretty_print(coeff, options)
            } else {
                PrettyPrinter::empty()
            };

            for (i, (var, exponant)) in vars.iter().enumerate() {
                let mut var = var.pretty_print(options);
                if !self.exponant_set.is_one(exponant) {
                    var.pow(&self.exponant_set.pretty_print(exponant, options));
                }
                coeff.concat(if i == 0 && !has_coeff { "" } else { "⋅" }, false, &var);
            }
            res.concat(if negative { "-" } else { "+" }, true, &coeff);
        }
        res
    }
}

impl<V: Monomial, T: Ring, U: Ring> Display for MultivariatePolynomial<V, T, U> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        PrettyPrint::fmt(self, &PrintOptions::default(), f)
    }
}
