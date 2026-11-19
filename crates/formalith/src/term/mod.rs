//! Mathematical expression implementation. An expression is represented as a [Term], which can be of many types.
//!
//! A term lives in a specific set, which can be a group, a ring, a field... Standard operations are defined between terms in [`term_op`].

use std::{
    borrow::BorrowMut,
    cmp::Ordering,
    collections::BTreeSet,
    fmt::{Debug, Display},
};

use malachite::Integer;

use crate::{
    combinatorics::{Combinatorics, CompositionIterator},
    context::{Context, Symbol},
    field::{
        Group, PartiallyOrderedSet, Ring, Set, TryElementFrom,
        matrix::{M, VectorSpaceElement},
    },
    iter,
    matrix::MatrixResult,
    polynom::{MultivariatePolynomial, ToTerm},
    printer::{PrettyPrint, PrettyPrinter, Print, PrintOptions},
};

pub mod term_op;
pub mod term_ring;
pub use term_ring::*;
pub mod value;
pub use value::*;
pub mod symbol;
pub use symbol::*;
pub mod add;
pub use add::*;
pub mod mul;
pub use mul::*;
pub mod pow;
pub use pow::*;
pub mod fun;
pub use fun::*;
pub mod derivative;
pub mod flags;
pub mod relation;
pub mod substitute;
use flags::{Flags, NORMALIZED};

/// A mathematical expression.
#[derive(Clone, PartialEq, Eq, Hash)]
#[cfg_attr(not(feature = "concise-debug"), derive(Debug))]
pub enum Term<T: Set> {
    /// See [Value]
    Value(Value<T>),
    /// See [`SymbolTerm`]
    Symbol(SymbolTerm<T>),
    /// See [Add]
    Add(Add<T>),
    /// See [Mul]
    Mul(Mul<T>),
    /// See [Pow]
    Pow(Pow<T>),
    /// See [Fun]
    Fun(Box<dyn Function<T>>),
}

#[cfg(feature = "concise-debug")]
impl<T: Set + Debug> Debug for Term<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Value(arg0) => Debug::fmt(arg0, f),
            Self::Symbol(arg0) => Debug::fmt(arg0, f),
            Self::Add(arg0) => Debug::fmt(arg0, f),
            Self::Mul(arg0) => Debug::fmt(arg0, f),
            Self::Pow(arg0) => Debug::fmt(arg0, f),
            Self::Fun(arg0) => Debug::fmt(arg0, f),
        }
    }
}

impl<T: PartiallyOrderedSet> std::cmp::PartialOrd for Term<T> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        match (self, other) {
            (Self::Value(Value { value: v1, .. }), Self::Value(Value { value: v2, .. })) => {
                self.get_set().partial_cmp(v1, v2)
            }
            (Self::Symbol(s1), Self::Symbol(s2)) => {
                if s1.symbol == s2.symbol {
                    Some(Ordering::Equal)
                } else {
                    None
                }
            }
            _ => None,
        }
    }
}

impl<T: Group> Term<T> {
    /// Check if the expression is strictly positive
    pub fn is_strictly_positive(&self) -> bool {
        matches!(
            PartialOrd::partial_cmp(self, &Self::zero(self.get_set())),
            Some(Ordering::Greater)
        )
    }
    /// Check if the expression is positive
    pub fn is_positive(&self) -> bool {
        self.is_zero() || self.is_strictly_positive()
    }
    /// Check if the expression is strictly negative
    pub fn is_strictly_negative(&self) -> bool {
        matches!(
            PartialOrd::partial_cmp(self, &Self::zero(self.get_set())),
            Some(Ordering::Less)
        )
    }
    /// Check if the expression is negative
    pub fn is_negative(&self) -> bool {
        self.is_zero() || self.is_strictly_negative()
    }
    /// Return the expression as a machine integer if it is an integer constant
    pub fn to_i64(&self) -> Option<i64> {
        match self {
            Self::Value(value) => value.set.to_i64(&value.value),
            _ => None,
        }
    }
}

impl<T: Set> Flags for Term<T> {
    fn get_flags(&self) -> u8 {
        match self {
            Self::Value(value) => value.get_flags(),
            Self::Symbol(symbol) => symbol.get_flags(),
            Self::Add(add) => add.get_flags(),
            Self::Mul(mul) => mul.get_flags(),
            Self::Pow(pow) => pow.get_flags(),
            Self::Fun(fun) => fun.get_flags(),
        }
    }
    fn get_flags_mut(&mut self) -> &mut u8 {
        match self {
            Self::Value(value) => value.get_flags_mut(),
            Self::Symbol(symbol) => symbol.get_flags_mut(),
            Self::Add(add) => add.get_flags_mut(),
            Self::Mul(mul) => mul.get_flags_mut(),
            Self::Pow(pow) => pow.get_flags_mut(),
            Self::Fun(fun) => fun.get_flags_mut(),
        }
    }
}

impl<T: Set> From<Mul<T>> for Term<T> {
    fn from(value: Mul<T>) -> Self {
        Self::Mul(value)
    }
}

impl<T: Set> From<Add<T>> for Term<T> {
    fn from(value: Add<T>) -> Self {
        Self::Add(value)
    }
}

impl<T: Set> From<Value<T>> for Term<T> {
    fn from(value: Value<T>) -> Self {
        Self::Value(value)
    }
}

impl<T: Set> From<Pow<T>> for Term<T> {
    fn from(value: Pow<T>) -> Self {
        Self::Pow(value)
    }
}
impl<T: Set> From<SymbolTerm<T>> for Term<T> {
    fn from(value: SymbolTerm<T>) -> Self {
        Self::Symbol(value)
    }
}

impl<T: Set> Term<T> {
    /// Get the ring where constants live
    pub fn get_set(&self) -> T {
        match self {
            Self::Value(value) => value.set,
            Self::Symbol(symbol) => symbol.set,
            Self::Add(add) => add.set,
            Self::Mul(mul) => mul.set,
            Self::Pow(pow) => pow.set,
            Self::Fun(fun) => fun.get_set(),
        }
    }
    /// The symbols of the expression, including those in exponents and function arguments.
    ///
    /// ```
    /// use formalith::{field::real::R, parse, symbol};
    ///
    /// let symbols = parse!("x^n + abs(y)", R).symbols();
    /// assert_eq!(symbols.len(), 3);
    /// assert!(symbols.contains(&symbol!("n")) && symbols.contains(&symbol!("y")));
    /// ```
    #[must_use]
    pub fn symbols(&self) -> BTreeSet<Symbol> {
        let mut symbols = BTreeSet::new();
        self.collect_symbols(&mut symbols);
        symbols
    }
    /// Add the symbols of the expression to `symbols`.
    pub(crate) fn collect_symbols(&self, symbols: &mut BTreeSet<Symbol>) {
        match self {
            Self::Value(_) => {}
            Self::Symbol(symbol) => {
                symbols.insert(symbol.symbol);
            }
            Self::Add(add) => add.iter().for_each(|term| term.collect_symbols(symbols)),
            Self::Mul(mul) => mul.iter().for_each(|term| term.collect_symbols(symbols)),
            Self::Pow(pow) => {
                pow.base.collect_symbols(symbols);
                pow.exponant.collect_symbols(symbols);
            }
            Self::Fun(fun) => fun.collect_symbols(symbols),
        }
    }
    /// Return `self` as [Value] if self is a `Value`, None otherwise.
    pub fn as_value(self) -> Option<Value<T>> {
        match self {
            Self::Value(value) => Some(value),
            _ => None,
        }
    }
    /// Create a constant expression
    pub const fn constant(constant: T::Element, set: T) -> Self {
        Self::Value(Value::new(constant, set))
    }
}
impl<T: Group> Term<T> {
    /// Create a zero constant expression
    pub fn zero(set: T) -> Self {
        Self::Value(Value::new(set.zero(), set))
    }
    /// Create the constant `n * 1`
    pub fn nth(n: i64, set: T) -> Self {
        Self::Value(Value::new(set.nth(n), set))
    }
    /// Check if the term is zero
    /// ```
    /// use formalith::{field::real::R, parse, symbol};
    ///
    /// assert!(parse!("0", R).is_zero());
    /// ```
    pub fn is_zero(&self) -> bool {
        match self {
            Self::Value(value) => value.set.is_zero(&value.value),
            Self::Symbol(_) | Self::Add(_) | Self::Mul(_) | Self::Pow(_) | Self::Fun(_) => false, // TODO how can we check if it's really not zero ?
        }
    }
}

impl<T: Group> Term<T> {
    /// Compare two terms
    #[allow(clippy::should_implement_trait)]
    pub fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        match (self, other) {
            (Self::Value(Value { value: v1, .. }), Self::Value(Value { value: v2, .. })) => self
                .get_set()
                .partial_cmp(v1, v2)
                .unwrap_or(Ordering::Equal),
            (Self::Value(_), _) => Ordering::Greater,
            (Self::Symbol(s1), Self::Symbol(s2)) => s1.symbol.cmp(&s2.symbol),
            (Self::Pow(p1), Self::Pow(p2)) => p1
                .base
                .cmp(&p2.base)
                .then_with(|| p1.exponant.cmp(&p2.exponant)),
            (_, Self::Value(_)) | (Self::Pow(_), _) => Ordering::Less,
            (_, Self::Pow(_)) => Ordering::Greater,
            (Self::Mul(m1), Self::Mul(m2)) => m1
                .len()
                .cmp(&m2.len())
                .then_with(|| iter::cmp_by(m1.iter(), m2.iter(), Self::cmp)),
            (Self::Mul(_), _) => Ordering::Less,
            (_, Self::Mul(_)) => Ordering::Greater,
            (Self::Add(a1), Self::Add(a2)) => a1
                .len()
                .cmp(&a2.len())
                .then_with(|| iter::cmp_by(a1.iter(), a2.iter(), Self::cmp)),
            (Self::Add(_), _) => Ordering::Less,
            (_, Self::Add(_)) => Ordering::Greater,
            (Self::Symbol(_), _) => Ordering::Less,
            (_, Self::Symbol(_)) => Ordering::Greater,
            (Self::Fun(f1), Self::Fun(f2)) => f1.cmp_dyn(&**f2),
        }
    }
    /// Compare two terms, putting terms which can be merged side by side, i.e. terms which only differ by their
    /// coefficient
    fn cmp_terms(&self, other: &Self) -> std::cmp::Ordering {
        match (self, other) {
            (Self::Value(_), Self::Value(_)) => Ordering::Equal,
            (Self::Value(_), _) => Ordering::Greater,
            (_, Self::Value(_)) => Ordering::Less,
            _ => {
                let (f1, f2) = (
                    self.non_coefficient_factors(),
                    other.non_coefficient_factors(),
                );
                f1.len()
                    .cmp(&f2.len())
                    .then_with(|| iter::cmp_by(f1.iter(), f2.iter(), Self::cmp_term_factors))
            }
        }
    }
    /// Factors of the term without its coefficient, the term itself if it isn't a product
    fn non_coefficient_factors(&self) -> &[Self] {
        match self {
            Self::Mul(mul) => &mul.factors,
            _ => std::slice::from_ref(self),
        }
    }
    /// Compare factors of the non-coefficient part of two terms, see [`Self::cmp_terms`]
    ///
    /// Factors are ordered by base, symbols first, then by exponant.
    fn cmp_term_factors(&self, other: &Self) -> std::cmp::Ordering {
        fn base<T: Set>(term: &Term<T>) -> &Term<T> {
            match term {
                Term::Pow(pow) => &pow.base,
                _ => term,
            }
        }
        match (base(self), base(other)) {
            (Self::Symbol(s1), Self::Symbol(s2)) => s1.symbol.cmp(&s2.symbol),
            (Self::Symbol(_), _) => Ordering::Less,
            (_, Self::Symbol(_)) => Ordering::Greater,
            (b1, b2) => b1.cmp(b2),
        }
        .then_with(|| match (self, other) {
            (Self::Pow(p1), Self::Pow(p2)) => p1.exponant.cmp(&p2.exponant),
            (Self::Pow(_), _) => Ordering::Greater,
            (_, Self::Pow(_)) => Ordering::Less,
            _ => Ordering::Equal,
        })
    }
    /// Compare two terms, putting factors which can be merged side by side
    fn cmp_factors(&self, other: &Self) -> std::cmp::Ordering {
        match (self, other) {
            (Self::Value(_), Self::Value(_)) => Ordering::Equal,
            (Self::Value(_), _) => Ordering::Greater,
            (_, Self::Value(_)) => Ordering::Less,
            (Self::Symbol(s1), Self::Symbol(s2)) => s1.symbol.cmp(&s2.symbol),
            (Self::Pow(p1), Self::Pow(p2)) => p1.base.cmp(&p2.base),
            (Self::Pow(p), _) => p.base.cmp(other).then(Ordering::Greater),
            (_, Self::Pow(p)) => self.cmp(&p.base).then(Ordering::Less),
            (Self::Add(a1), Self::Add(a2)) => a1
                .len()
                .cmp(&a2.len())
                .then_with(|| iter::cmp_by(a1.iter(), a2.iter(), Self::cmp)),
            (Self::Symbol(_), _) => Ordering::Less,
            (_, Self::Symbol(_)) => Ordering::Greater,
            _ => self.cmp(other),
        }
    }
}

impl<T: Ring> Term<M<TermSet<T>>> {
    /// Compute the determinant of the expression.
    ///
    /// # Errors
    /// This method returns an error if `self` is a matrix which is not square.
    pub fn det(&self) -> MatrixResult<Term<T>> {
        match self {
            Self::Value(value) => match &value.value {
                VectorSpaceElement::Scalar(scalar, _) => Ok(scalar.clone()),
                VectorSpaceElement::Vector(matrix) => Ok(matrix.det()?),
            },
            Self::Add(_) | Self::Mul(_) | Self::Pow(_) | Self::Symbol(_) | Self::Fun(_) => {
                Ok(Term::Fun(Box::new(Fun::new(
                    Context::DET,
                    vec![self.clone()],
                    *self.get_set().scalar_sub_set.get_set(),
                ))))
            }
        }
    }
}

impl<T: Set> Term<T> {
    /// Convert `self` to [Mul], and return a mutable reference to easily edit it.
    fn convert_to_mul(&mut self) -> &mut Mul<T> {
        *self = Self::Mul(Mul::empty(self.get_set()));
        let Self::Mul(n) = self else { unreachable!() };
        n
    }
    /// Convert `self` to [Pow], and return a mutable reference to easily edit it.
    fn convert_to_pow(
        &mut self,
        base: Box<Self>,
        exponant: Box<Term<<T as Set>::ExponantSet>>,
    ) -> &mut Pow<T> {
        *self = Pow::new(base, exponant, self.get_set()).into();
        let Self::Pow(n) = self else { unreachable!() };
        n
    }
}

trait MergeTerms {
    /// Try merging `other` term inside `self`. Return true if there was a merge.
    fn merge_terms(&mut self, other: &Self) -> bool;
}
trait MergeFactors {
    /// Try merging `other` factor inside `self`. Return true if there was a merge.
    fn merge_factors(&mut self, other: &Self) -> bool;
}

impl<T: Set> Term<T> {
    /// Mark a merged constant as approximate if one of the merged terms was (see [`flags::APPROXIMATE`]).
    fn propagate_approximation(&mut self, approximate: bool) {
        if approximate && matches!(self, Self::Value(_) | Self::Mul(_)) {
            self.set_approximate(true);
        }
    }
    /// Whether the term is `{$oo$}`, a power of it or a product `{$c oo$}`. Such terms aren't merged, so that
    /// `{$oo - oo$}` and `{$oo/oo$}` are left to the set's normalization instead of giving 0 and 1.
    pub(crate) fn is_infinity_factor(&self) -> bool {
        match self {
            Self::Symbol(symbol) => symbol.symbol == Context::OO,
            Self::Pow(pow) => pow.base.is_infinity_factor(),
            Self::Mul(mul) => {
                let mut factors = mul.iter();
                factors.next().is_some_and(Self::is_infinity_factor) && factors.next().is_none()
            }
            _ => false,
        }
    }
    /// [`MergeTerms::merge_terms`], the result being approximate if `self` or `other` is.
    pub(crate) fn try_merge_terms(&mut self, other: &Self) -> bool {
        if self.is_infinity_factor() || other.is_infinity_factor() {
            return false;
        }
        let approximate = self.is_approximate() || other.is_approximate();
        let merged = self.merge_terms(other);
        if merged {
            self.propagate_approximation(approximate);
        }
        merged
    }
    /// [`MergeFactors::merge_factors`], the result being approximate if `self` or `other` is.
    pub(crate) fn try_merge_factors(&mut self, other: &Self) -> bool {
        if self.is_infinity_factor() || other.is_infinity_factor() {
            return false;
        }
        let approximate = self.is_approximate() || other.is_approximate();
        let merged = self.merge_factors(other);
        if merged {
            self.propagate_approximation(approximate);
        }
        merged
    }
}
/// Normalization trait.
pub trait Normalize {
    /// Normalize an expression, i.e. sort sums and products, merge expressions that can be merged, remove useless expressions like zero in sums.
    #[must_use]
    fn normalize(&self) -> Self;
}
/// Unification trait.
pub trait Unify {
    /// Return the expression as a rational expression
    #[must_use]
    fn unify(&self) -> Self;
}

/// Expansion trait.
pub trait Expand {
    /// Expand the expression.
    /// ```
    /// use formalith::{field::real::R, parse, symbol, term::Expand};
    ///
    /// assert_eq!(parse!("(x+2)*(x+3)", R).expand(), parse!("x*x+5*x+6", R));
    /// ```
    #[must_use]
    fn expand(&self) -> Self;

    /// Expand the expression without normalizing it
    #[must_use]
    fn expand_without_norm(&self) -> Self;
}

impl<T: Set> MergeTerms for Term<T> {
    default fn merge_terms(&mut self, _other: &Self) -> bool {
        // There is no addition in a set
        false
    }
}

impl<T: Group> MergeTerms for Term<T> {
    default fn merge_terms(&mut self, other: &Self) -> bool {
        if matches!(self, Self::Fun(_)) && self == other {
            // Merge f(x) + f(x)
            let set = self.get_set();
            *self = Self::Mul(Mul::new(
                set.get_coefficient_set().nth(2),
                vec![other.clone()],
                set,
            ))
            .normalize();
            return true;
        }
        match (self.borrow_mut(), other) {
            (Self::Value(Value { value: v1, set, .. }), Self::Value(Value { value: v2, .. })) => {
                set.try_add(v1, v2).is_some_and(|sum| {
                    *v1 = sum;
                    true
                })
            }
            (Self::Symbol(s1), Self::Symbol(s2)) if s1 == s2 => {
                // Merge x + x
                *self = Self::Mul(Mul::new(
                    s1.set.get_coefficient_set().nth(2),
                    vec![Self::Symbol(s1.clone())],
                    s1.set,
                ))
                .normalize();
                true
            }
            (Self::Mul(m1), Self::Mul(m2)) => {
                // Merge 2*x*y + 3*x*y
                let m1_len = m1.len() - usize::from(m1.has_coeff());
                let m2_len = m2.len() - usize::from(m2.has_coeff());
                if m1_len != m2_len {
                    return false;
                }
                // Compare factors
                if m1.factors != m2.factors {
                    return false;
                }

                let set = m1.set;
                let coeff = set
                    .get_coefficient_set()
                    .add(&m1.get_coeff(), &m2.get_coeff());
                if set.get_coefficient_set().is_zero(&coeff) {
                    *self = Self::zero(set);
                } else {
                    m1.set_coeff(coeff);
                    *self = self.normalize();
                }
                true
            }
            (Self::Mul(m1), _) => {
                // Merge 2*x + x
                if m1.len() - usize::from(m1.has_coeff()) != 1 || m1.factors[0] != *other {
                    false
                } else {
                    let set = m1.set;
                    set.get_coefficient_set()
                        .add_assign(m1.get_coeff_mut(), &set.get_coefficient_set().nth(1));
                    if set.get_coefficient_set().is_zero(&m1.get_coeff()) {
                        *self = Self::zero(set);
                    }
                    true
                }
            }
            (_, Self::Mul(m2)) => {
                // Merge x + 2*x
                if m2.len() - usize::from(m2.has_coeff()) != 1 || m2.factors[0] != *self {
                    false
                } else {
                    let set = m2.set;
                    let coeff = set
                        .get_coefficient_set()
                        .add(&m2.get_coeff(), &set.get_coefficient_set().nth(1));
                    if set.get_coefficient_set().is_zero(&coeff) {
                        *self = Value::new(set.zero(), set).into();
                    } else {
                        // Transform self to mul and add one to coeff
                        let mul = self.convert_to_mul();
                        mul.push(m2.factors[0].clone());
                        mul.set_coeff(coeff);
                        *self = self.normalize();
                    }
                    true
                }
            }
            (Self::Pow(p1), Self::Pow(p2)) if p1.base == p2.base && p1.exponant == p2.exponant => {
                // Merge x^2 + x^2
                *self = Self::Mul(Mul::new(
                    p1.set.get_coefficient_set().nth(2),
                    vec![other.clone()],
                    p1.set,
                ))
                .normalize();
                true
            }
            _ => false,
        }
    }
}

impl<T: Set> MergeFactors for Term<T> {
    default fn merge_factors(&mut self, _other: &Self) -> bool {
        // There is no product in a set and in a group
        false
    }
}

impl<T: Ring> Term<T> {
    fn merge_factors_in_ring(&mut self, other: &Self) -> bool {
        match (self.borrow_mut(), other) {
            (
                Self::Value(Value {
                    value: v1,
                    set: set1,
                    ..
                }),
                Self::Value(Value { value: v2, .. }),
            ) => {
                return set1.try_mul(v1, v2).is_some_and(|product| {
                    *v1 = product;
                    true
                });
            }
            (Self::Pow(p1), Self::Pow(p2)) => {
                // Merge x^2 * x^3
                if *p1.base == *p2.base {
                    **p1.exponant = Term::Add(Add::new(
                        vec![(**p1.exponant).clone(), (**p2.exponant).clone()],
                        other.get_set().get_exponant_set(),
                    ));
                    **p1.exponant = (**p1.exponant).normalize();
                    // `{$x^2 x^-2 = x^0 = 1$}`
                    *self = self.normalize();
                    return true;
                }
                return false;
            }
            _ => {}
        }

        if self == other {
            // Merge x * x
            *self = Self::Pow(Pow::new(
                self.clone(),
                Term::nth(2, self.get_set().get_exponant_set()),
                self.get_set(),
            ))
            .normalize();
            return true;
        }
        false
    }
}

impl<T: Ring> MergeFactors for Term<T> {
    default fn merge_factors(&mut self, other: &Self) -> bool {
        self.merge_factors_in_ring(other)
    }
}
impl<T: Ring<ExponantSet: Ring>> MergeFactors for Term<T> {
    fn merge_factors(&mut self, other: &Self) -> bool {
        if self.merge_factors_in_ring(other) {
            true
        } else {
            match (self.borrow_mut(), other) {
                (Self::Pow(p1), _) => {
                    // Merge x^2 * x
                    if *p1.base != *other {
                        false
                    } else if let Term::Value(Value { value, set, .. }) = &mut **p1.exponant {
                        // Add one to m1 coeff
                        set.add_assign(value, &set.one());
                        *self = self.normalize();
                        true
                    } else {
                        **p1.exponant = Term::Add(Add::new(
                            vec![
                                (**p1.exponant).clone(),
                                Value::new(
                                    other.get_set().get_exponant_set().one(),
                                    other.get_set().get_exponant_set(),
                                )
                                .into(),
                            ],
                            other.get_set().get_exponant_set(),
                        ));
                        **p1.exponant = (**p1.exponant).normalize();
                        true
                    }
                }
                (_, Self::Pow(p2)) => {
                    // Merge x * x^2
                    if *self != *p2.base {
                        false
                    } else if let Term::Value(Value { value, set, .. }) = &**p2.exponant {
                        // Transform self to mul and add one to coeff
                        self.convert_to_pow(
                            p2.base.clone(),
                            Term::Value(Value::new(set.add(value, &set.one()), *set)).into(),
                        );
                        *self = self.normalize();
                        true
                    } else {
                        // Add one to the coefficient
                        self.convert_to_pow(
                            p2.base.clone(),
                            Term::Add(Add::new(
                                vec![
                                    (**p2.exponant).clone(),
                                    Value::new(
                                        self.get_set().get_exponant_set().one(),
                                        self.get_set().get_exponant_set(),
                                    )
                                    .into(),
                                ],
                                self.get_set().get_exponant_set(),
                            ))
                            .into(),
                        );
                        *self = self.normalize();
                        true
                    }
                }
                _ => false,
            }
        }
    }
}

impl<T: Ring<ExponantSet: Ring, ProductCoefficientSet = T>> Term<T> {
    /// Convert the expression to a multivariate polynomial.
    ///
    /// Used to use factorization algorithms.
    pub fn to_polynomial(
        &self,
    ) -> MultivariatePolynomial<Self, TermSet<T>, TermSet<T::ExponantSet>> {
        self.to_polynomial_with_constants(&[])
    }

    /// Convert the expression to a multivariate polynomial, whose coefficients may contain the symbols of `constants`.
    ///
    /// ```
    /// use formalith::{field::real::R, parse, symbol};
    ///
    /// assert!(parse!("n^2 + 1", R).to_polynomial_with_constants(&[symbol!("n")]).is_constant());
    /// assert!(!parse!("n^2 + 1", R).to_polynomial().is_constant());
    /// ```
    pub fn to_polynomial_with_constants(
        &self,
        constants: &[Symbol],
    ) -> MultivariatePolynomial<Self, TermSet<T>, TermSet<T::ExponantSet>> {
        self.expand().to_polynomial_impl(constants)
    }

    fn to_polynomial_impl(
        &self,
        constants: &[Symbol],
    ) -> MultivariatePolynomial<Self, TermSet<T>, TermSet<T::ExponantSet>> {
        let set = self.get_set().get_term_set();
        let exponant_set = self.get_set().get_exponant_set().get_term_set();
        let is_constant = |term: &Self| matches!(term, Self::Symbol(symbol) if constants.contains(&symbol.symbol));
        match self {
            Self::Value(_) => MultivariatePolynomial::constant(self.clone(), set, exponant_set),
            Self::Symbol(_) if is_constant(self) => {
                MultivariatePolynomial::constant(self.clone(), set, exponant_set)
            }
            Self::Pow(pow) if is_constant(&pow.base) => {
                MultivariatePolynomial::constant(self.clone(), set, exponant_set)
            }
            Self::Symbol(_) | Self::Fun(_) => {
                MultivariatePolynomial::variable(self.clone(), set, exponant_set)
            }
            Self::Add(add) => add.iter().fold(
                MultivariatePolynomial::zero(set, exponant_set),
                |res, term| res + term.to_polynomial_impl(constants),
            ),
            Self::Mul(mul) => mul.iter().fold(
                MultivariatePolynomial::constant(
                    Self::Value(Value::new(mul.coefficient.clone(), self.get_set())),
                    set,
                    exponant_set,
                ),
                |res, factor| res * factor.to_polynomial_impl(constants),
            ),
            Self::Pow(pow) => MultivariatePolynomial::new(
                vec![(
                    vec![(*pow.base.clone(), (**pow.exponant).clone())],
                    set.one(),
                )],
                set,
                exponant_set,
            ),
        }
    }
}

impl<T: Ring> Expand for Term<T> {
    fn expand(&self) -> Self {
        debug_assert!(!self.needs_normalization());
        let res = self.expand_without_norm();
        let res = res.get_set().expand(res);
        res.normalize()
    }
    fn expand_without_norm(&self) -> Self {
        debug_assert!(!self.needs_normalization());
        match self {
            Self::Value(_) | Self::Symbol(_) => self.clone(),
            Self::Add(add) => {
                Self::Add(Add::new(add.iter().map(Expand::expand).collect(), add.set))
            }
            Self::Mul(mul) => {
                let mut mul = mul.clone();
                let (num, den) = self.as_fraction(false);
                if !den.is_one() {
                    let fraction = num.expand() / den.expand();
                    if let Self::Mul(fraction) = fraction {
                        mul = fraction;
                    } else {
                        return fraction;
                    }
                }
                let mut sums: Vec<Self> = vec![];
                let mut new_sums = vec![];
                for factor in &mul {
                    let expanded = factor.expand();
                    if let Self::Add(add) = expanded {
                        for term in &add {
                            for sum in &sums {
                                if let Self::Mul(mul) = sum {
                                    let mut mul = mul.clone();
                                    mul.push(term.clone());
                                    new_sums.push(Self::Mul(mul));
                                } else {
                                    unreachable!()
                                }
                            }
                            if sums.is_empty() {
                                new_sums.push(Self::Mul(Mul::new(
                                    mul.coefficient.clone(),
                                    vec![term.clone()],
                                    mul.set,
                                )));
                            }
                        }
                        std::mem::swap(&mut sums, &mut new_sums);
                        new_sums.clear();
                    } else if sums.is_empty() {
                        sums.push(Self::Mul(Mul::new(
                            mul.coefficient.clone(),
                            vec![expanded],
                            mul.set,
                        )));
                    } else {
                        for sum in &mut sums {
                            if let Self::Mul(mul) = sum {
                                mul.push(expanded.clone());
                            } else {
                                unreachable!()
                            }
                        }
                    }
                }

                Self::Add(Add::new(sums, mul.set))
            }
            Self::Pow(pow) => {
                let mut res = pow.clone();
                *res.base = (*res.base).expand();
                **res.exponant = (**res.exponant).expand();

                Self::Pow(res)
            }
            Self::Fun(fun) => (**fun).expand(),
        }
    }
}

impl<T: Ring<ExponantSet: Ring, ProductCoefficientSet = T>> Term<T> {
    /// Factor the expression.
    #[must_use]
    pub fn factor(&self) -> Self
    where
        TermSet<T>: TryElementFrom<TermSet<T::ExponantSet>>,
        Self: TryFrom<Term<T::ExponantSet>>,
        <Self as TryFrom<Term<T::ExponantSet>>>::Error: Debug,
    {
        let poly = self.to_polynomial();
        let factors = poly.factor();
        let mut res = Self::one(self.get_set());
        for (factor, multiplicity) in factors {
            res *= factor.to_term().pow(&Term::constant(
                self.get_set().get_exponant_set().nth(multiplicity.into()),
                self.get_set().get_exponant_set(),
            ));
        }
        res.with_opposite_factors_merged()
    }

    /// Write the sum bases of a product with a positive leading term, so that opposite factors like `a - b` and
    /// `b - a` cancel: `{$(a - b)^2 / (b - a) = -(a - b)$}`.
    fn with_opposite_factors_merged(self) -> Self {
        let Self::Mul(mul) = &self else { return self };
        let set = self.get_set();
        let mut res = Self::Value(Value::new(mul.coefficient.clone(), set));
        for factor in mul {
            let (base, exponant) = match factor {
                Self::Pow(pow) => (&*pow.base, Some(&**pow.exponant)),
                _ => (factor, None),
            };
            let negative = matches!(base, Self::Add(add)
                if add.iter().next().is_some_and(|first| set.is_strictly_negative(&Self::coefficients(first).next().unwrap())));
            if !negative {
                res *= factor;
                continue;
            }
            // `{$(-1)^e$}` is a value only for integer exponants
            let sign = exponant.map_or_else(
                || Some(Self::nth(-1, set)),
                |e| {
                    let sign = Self::nth(-1, set).pow(e).normalize();
                    matches!(sign, Self::Value(_)).then_some(sign)
                },
            );
            let flipped = (-base.clone()).expand().normalize();
            let opposite_exists = mul.iter().any(|other| match other {
                Self::Pow(pow) => *pow.base == flipped,
                other => *other == flipped,
            });
            let Some(sign) = sign.filter(|_| opposite_exists) else {
                res *= factor;
                continue;
            };
            res *= sign * exponant.map_or_else(|| flipped.clone(), |e| flipped.pow(e));
        }
        res
    }

    /// Cancel common polynomial factors of the numerator and the denominator of the expression.
    pub(crate) fn cancel_common_factors(&self) -> Self {
        let (num, den) = self.as_fraction(true);
        if den.is_one() {
            return self.clone();
        }
        let (num, den) = (num.to_polynomial(), den.to_polynomial());
        let gcd = num.gcd(&den);
        let (num, den) = if gcd.is_constant() {
            (num.to_term(), den.to_term())
        } else {
            match (num.exact_div(&gcd), den.exact_div(&gcd)) {
                (Some(num), Some(den)) => (num.to_term(), den.to_term()),
                _ => return self.clone(),
            }
        };
        // Cancel the numeric content, `{$(2 x)/(4 x + 2) = x/(2 x + 1)$}`
        let set = self.get_set();
        let mut content = num
            .coefficients()
            .chain(den.coefficients())
            .fold(set.zero(), |gcd, c| set.coefficient_gcd(&gcd, &c));
        // Move the sign to the numerator, `{$1/(-x - 1) = -1/(x + 1)$}`
        if den.coefficients().all(|c| set.is_strictly_negative(&c)) {
            set.neg_assign(&mut content);
        }
        if gcd.is_constant() && set.is_one(&content) {
            return self.clone();
        }
        match set.try_inv(&content) {
            Some(inv) if !set.is_one(&content) => {
                let inv = Self::Value(Value::new(inv, set));
                (num * &inv).expand() / (den * &inv).expand()
            }
            _ => num / den,
        }
    }

    /// Coefficients of the terms of a sum, or of the expression if it isn't a sum
    fn coefficients(&self) -> impl Iterator<Item = T::Element> {
        let coefficient = |term: &Self| match term {
            Self::Value(value) => value.value.clone(),
            Self::Mul(mul) => mul.coefficient.clone(),
            _ => term.get_set().one(),
        };
        match self {
            Self::Add(add) => add.iter().map(coefficient).collect::<Vec<_>>(),
            _ => vec![coefficient(self)],
        }
        .into_iter()
    }
}

impl<T: Ring<ProductCoefficientSet = T>> Term<T> {
    /// Distribute `exponant` over the product `mul`: `{$(c x y)^e = c^e x^e y^e$}`.
    ///
    /// It holds for integer exponants in commutative rings, callers must check other cases.
    pub(crate) fn distribute_pow(mul: &Mul<T>, exponant: &Term<T::ExponantSet>) -> Self {
        mul.iter().fold(
            Self::Value(Value::new(mul.coefficient.clone(), mul.set)).pow(exponant),
            |res, factor| res * factor.pow(exponant),
        )
    }
}

impl<T: Ring> Term<T> {
    /// Expand `add^n` with the multinomial formula. `from_integer` converts the multinomial coefficients to elements of `T`.
    pub(crate) fn expand_sum_power(
        add: &Add<T>,
        n: usize,
        from_integer: impl Fn(Integer) -> T::Element,
    ) -> Self {
        let set = add.set;
        let exponant_set = set.get_exponant_set();
        let mut terms = Self::zero(set);
        let mut iterator = CompositionIterator::new(add.len(), n);
        while let Some(k) = iterator.next_composition() {
            let ik = k.iter().map(|x| Integer::from(*x)).collect::<Vec<_>>();
            let mut result = Self::Value(Value::new(from_integer(Integer::multinom(&ik)), set));
            for (term, k) in add.iter().zip(k) {
                result *= term.pow(&Term::nth(
                    i64::try_from(*k).expect("Exponant is too large"),
                    exponant_set,
                ));
            }
            terms += result;
        }
        terms
    }
}
impl<T: Set> Expand for Term<T> {
    default fn expand(&self) -> Self {
        todo!()
    }
    default fn expand_without_norm(&self) -> Self {
        todo!()
    }
}
impl<T: Set> Normalize for Term<T> {
    default fn normalize(&self) -> Self {
        match self {
            // Atoms are already normalized
            Self::Value(_) | Self::Symbol(_) => self.clone(),
            _ => todo!(),
        }
    }
}
impl<T: Ring> Term<T> {
    fn normalize_in_ring(&self) -> Self {
        let mut res = match self {
            Self::Value(_) | Self::Symbol(_) => self.clone(),
            Self::Add(add) => {
                let mut res = vec![];
                for term in add {
                    let normalized = term.normalize();
                    if normalized.is_zero() {
                        continue;
                    }
                    if let Self::Add(inner_add) = normalized {
                        // terms are already normalized
                        res.extend(inner_add.terms);
                    } else {
                        res.push(normalized);
                    }
                }
                if res.is_empty() {
                    return Self::zero(self.get_set());
                }
                res.sort_by(Self::cmp_terms);
                res.reverse();

                // Merge terms
                let mut terms = vec![];
                let mut current_merge = res.pop().unwrap();
                while let Some(next) = res.pop() {
                    if !current_merge.try_merge_terms(&next) {
                        if !current_merge.is_zero() {
                            terms.push(current_merge);
                        }
                        current_merge = next;
                    }
                }
                if !current_merge.is_zero() {
                    terms.push(current_merge);
                }

                // `{$(x + y) - (x + y) = 0$}`: distribute a product `c (a + b)` when it cancels with other terms
                for j in 0..terms.len() {
                    let Self::Mul(mul) = &terms[j] else { continue };
                    if mul.factors.len() != 1 {
                        continue;
                    }
                    let Self::Add(inner) = &mul.factors[0] else {
                        continue;
                    };
                    let mut candidate: Vec<Self> = terms
                        .iter()
                        .enumerate()
                        .filter(|(k, _)| *k != j)
                        .map(|(_, t)| t.clone())
                        .collect();
                    let others = candidate.len();
                    for part in inner {
                        candidate.push(
                            Self::Mul(Mul::new(
                                mul.coefficient.clone(),
                                vec![part.clone()],
                                self.get_set(),
                            ))
                            .normalize(),
                        );
                    }
                    let expected = others + inner.len();
                    let merged = Self::Add(Add::new(candidate, self.get_set())).normalize();
                    let count = match &merged {
                        Self::Add(add) => add.len(),
                        t if t.is_zero() => 0,
                        _ => 1,
                    };
                    if count < expected {
                        return merged;
                    }
                }

                if terms.is_empty() {
                    Self::zero(self.get_set())
                } else if terms.len() == 1 {
                    terms.pop().unwrap()
                } else {
                    Self::Add(Add::new(terms, self.get_set()))
                }
            }
            Self::Mul(mul) => {
                let mut res = vec![];
                let mut coeff = mul.coefficient.clone();
                let mut approximate = mul.is_approximate();
                for factor in mul {
                    let normalized = factor.normalize();
                    if normalized.is_zero() {
                        return Self::zero_times(self.get_set(), mul.iter());
                    }
                    if normalized.is_one() {
                        continue;
                    }
                    if let Self::Mul(inner_mul) = normalized {
                        // factors are already normalized
                        approximate |= inner_mul.is_approximate();
                        res.extend(inner_mul.factors);
                        mul.set
                            .get_coefficient_set()
                            .mul_assign(&mut coeff, &inner_mul.coefficient);
                    } else {
                        res.push(normalized);
                    }
                }
                if res.is_empty() {
                    if mul.set.get_coefficient_set().is_one(&coeff) {
                        return Self::one(self.get_set());
                    }
                    // Only the coefficient is left, `{$2 x x^-1$}`, which the set may fold into a value
                    res.push(Self::one(self.get_set()));
                }
                res.sort_by(Self::cmp_factors);
                res.reverse();

                // Merge factors
                let mut factors = vec![];
                let mut current_merge = res.pop().unwrap();

                while let Some(next) = res.pop() {
                    if !current_merge.try_merge_factors(&next) {
                        if current_merge.is_zero() {
                            return Self::zero(self.get_set());
                        }
                        factors.push(current_merge);
                        current_merge = next;
                    }
                }
                factors.push(current_merge);
                // Factors merged into one, `{$x^2 x^-2$}`, keeping one when nothing else is left
                if factors.len() > 1 {
                    factors.retain(|factor| !factor.is_one());
                    if factors.is_empty() {
                        factors.push(Self::one(self.get_set()));
                    }
                }

                if mul.set.get_coefficient_set().is_zero(&coeff) {
                    Self::zero(self.get_set())
                } else if factors.len() == 1 && mul.set.get_coefficient_set().is_one(&coeff) {
                    factors.pop().unwrap()
                } else {
                    let mut mul = Self::Mul(Mul::new(coeff.clone(), factors, self.get_set()));
                    mul.set_approximate(approximate);
                    mul
                }
            }
            Self::Pow(pow) => {
                let base = (*pow.base).normalize();
                let exponant = (**pow.exponant).normalize();
                if exponant.is_zero() {
                    // `{$a^0$}` has the shape of `a`, like the identity matrix
                    return match &base {
                        Self::Value(value) => {
                            Self::Value(Value::new(value.set.one_like(&value.value), value.set))
                        }
                        _ => Self::one(self.get_set()),
                    };
                }
                if base.is_one() {
                    return base;
                }
                Self::Pow(Pow::new(Box::new(base), Box::new(exponant), self.get_set()))
            }
            Self::Fun(fun) => (**fun).normalize(),
        };
        res = res.get_set().normalize(res);
        res.set_normalized(true);
        res
    }
}
impl<T: Ring> Term<T> {
    /// The product of zero with `factors`: zero, or `undefined` when a factor is infinite, `{$0 oo$}`.
    fn zero_times<'a>(set: T, mut factors: impl Iterator<Item = &'a Self>) -> Self {
        if factors.any(|f| f.normalize().is_infinity_factor()) {
            Self::Symbol(symbol::SymbolTerm::new(Context::UNDEFINED, set))
        } else {
            Self::zero(set)
        }
    }
}
impl<T: Ring<ExponantSet: Ring>> Term<T> {
    fn normalize_in_ring_with_ring_exponant(&self) -> Self {
        let normalized = self.normalize_in_ring();
        if let Self::Pow(pow) = &normalized
            && pow.exponant.is_one()
        {
            return *pow.base.clone();
        }
        normalized
    }
}

impl<T: Ring> Normalize for Term<T> {
    default fn normalize(&self) -> Self {
        self.normalize_in_ring()
    }
}

impl<T: Ring<ExponantSet: Ring>> Normalize for Term<T> {
    default fn normalize(&self) -> Self {
        self.normalize_in_ring_with_ring_exponant()
    }
}
impl<T: Ring<ExponantSet: Ring, ProductCoefficientSet = T>> Normalize for Term<T> {
    fn normalize(&self) -> Self {
        if let Self::Mul(mut mul) = self.clone() {
            let coefficient_set = mul.set.get_coefficient_set();
            let mut new_coeff = mul.coefficient.clone();
            let mut approximate = mul.is_approximate();
            // Keep values which can't be multiplied with the coefficient, like matrices of incompatible sizes
            mul.factors.retain(|factor| {
                if let Self::Value(Value { value, .. }) = factor
                    && let Some(product) = coefficient_set.try_mul(&new_coeff, value)
                {
                    approximate |= factor.is_approximate();
                    new_coeff = product;
                    false
                } else {
                    true
                }
            });
            // `{$0/0$}` and `{$0 oo$}` are undefined: a power of zero surviving normalization is a division by zero
            if coefficient_set.is_zero(&new_coeff)
                && mul.factors.iter().any(|f| {
                    let f = f.normalize();
                    matches!(&f, Self::Pow(p) if p.base.is_zero()) || f.is_infinity_factor()
                })
            {
                return Self::Symbol(symbol::SymbolTerm::new(
                    crate::context::Context::UNDEFINED,
                    self.get_set(),
                ));
            }
            mul.coefficient = new_coeff;
            mul.set_approximate(approximate);
            if mul.is_empty() {
                let mut value = Self::Value(Value::new(mul.coefficient, self.get_set()));
                value.set_approximate(approximate);
                value
            } else {
                Self::Mul(mul).normalize_in_ring_with_ring_exponant()
            }
        } else {
            self.normalize_in_ring_with_ring_exponant()
        }
    }
}

impl<T: Ring> Term<T> {
    /// Return the expression as a rational expression, (numerator, denominator)
    pub fn as_fraction(&self, unify: bool) -> (Self, Self) {
        debug_assert!(!self.needs_normalization());
        match self {
            Self::Symbol(_) | Self::Fun(_) => (self.clone(), Self::one(self.get_set())),
            Self::Value(value) => {
                let (num, den) = self.get_set().as_fraction(&value.value);
                (
                    Self::constant(num, self.get_set()),
                    Self::constant(den, self.get_set()),
                )
            }
            Self::Mul(mul) => {
                let mut num = Self::one(self.get_set());
                let mut den = Self::one(self.get_set());

                for factor in mul {
                    let (n, d) = factor.as_fraction(unify);
                    num *= n;
                    den *= d;
                }
                let (n, d) = mul.set.get_coefficient_set().as_fraction(&mul.coefficient);
                if let Self::Mul(mul) = &mut num {
                    mul.set
                        .get_coefficient_set()
                        .mul_assign(&mut mul.coefficient, &n);
                } else {
                    num = Self::Mul(Mul::new(n, vec![num], mul.set)).normalize();
                }
                if let Self::Mul(mul) = &mut den {
                    mul.set
                        .get_coefficient_set()
                        .mul_assign(&mut mul.coefficient, &d);
                } else {
                    den = Self::Mul(Mul::new(d, vec![den], mul.set)).normalize();
                }
                (num, den)
            }
            Self::Add(add) => {
                let mut num = Self::zero(self.get_set());
                let mut den = Self::one(self.get_set());

                for term in add {
                    let (n, d) = term.as_fraction(unify);
                    if d == den {
                        num += n;
                    } else {
                        num *= &d;
                        num += n * &den;
                        den *= &d;
                    }
                }
                (num, den)
            }
            Self::Pow(pow) => {
                let mut pow = pow.clone();
                if unify {
                    *pow.base = pow.base.unify();
                    **pow.exponant = pow.exponant.unify();
                }
                if let Some(n) = pow.exponant.to_i64()
                    && n < 0
                {
                    // `{$(n/d)^(-k) = d^k / n^k$}` for an integer `k`
                    let (num, den) = pow.base.as_fraction(unify);
                    let k = Term::nth(-n, pow.exponant.get_set());
                    return (den.pow(&k), num.pow(&k));
                }
                if pow.exponant.is_strictly_negative() {
                    (
                        Self::one(self.get_set()),
                        pow.with_negated_exponant().into(),
                    )
                } else {
                    (pow.into(), Self::one(self.get_set()))
                }
            }
        }
    }
}

impl<T: Set> Unify for Term<T> {
    default fn unify(&self) -> Self {
        self.clone()
    }
}

impl<T: Ring> Unify for Term<T> {
    fn unify(&self) -> Self {
        debug_assert!(!self.needs_normalization());
        let (num, den) = self.as_fraction(true);
        num / den
    }
}

impl<T: Ring> Term<T> {
    /// Simplify the expression by applying other simplification functions ([`Self::unify`], [`Self::expand`])
    #[must_use]
    pub fn simplify(&self) -> Self {
        debug_assert!(!self.needs_normalization());
        let mut res = self.get_set().simplify(self.clone());
        let (num, den) = res.as_fraction(true);
        res = if let Self::Value(_) = den {
            // Distribute a constant denominator, `{$(3 x + 3)/2 = 3/2 x + 3/2$}`
            (num / den).expand()
        } else {
            num.expand() / den.expand() // add set expansion if expand_without_norm and add a value_expand arg ?
        };
        res = res.normalize();

        res
    }
}

impl<T: Ring> Term<T> {
    /// Invert the expression
    #[must_use]
    pub fn inv(&self) -> Self {
        debug_assert!(!self.needs_normalization());
        Self::one(self.get_set()) / self
    }
    /// Return the constant 1
    pub fn one(set: T) -> Self {
        Self::Value(Value::new(set.one(), set))
    }
    /// Check if the term is one
    /// ```
    /// use formalith::{field::real::R, parse, symbol};
    ///
    /// assert!(parse!("1", R).is_one());
    /// ```
    pub fn is_one(&self) -> bool {
        match self {
            Self::Value(value) => value.set.is_one(&value.value),
            Self::Symbol(_) | Self::Add(_) | Self::Mul(_) | Self::Pow(_) | Self::Fun(_) => false,
        }
    }
}

impl<T: Set> Display for Term<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        PrettyPrint::fmt(self, &PrintOptions::default(), f)
    }
}
impl<T: Set> Print for Term<T> {
    fn print(&self, options: &PrintOptions, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Value(value) => Print::print(value, options, f),
            Self::Symbol(symbol) => Print::print(symbol, options, f),
            Self::Add(add) => Print::print(add, options, f),
            Self::Mul(mul) => Print::print(mul, options, f),
            Self::Pow(pow) => Print::print(pow, options, f),
            Self::Fun(fun) => Print::print(&**fun, options, f),
        }
    }
}
impl<T: Set> PrettyPrint for Term<T> {
    fn pretty_print(&self, options: &PrintOptions) -> PrettyPrinter {
        match self {
            Self::Value(value) => PrettyPrint::pretty_print(value, options),
            Self::Symbol(symbol) => PrettyPrint::pretty_print(symbol, options),
            Self::Add(add) => PrettyPrint::pretty_print(add, options),
            Self::Mul(mul) => PrettyPrint::pretty_print(mul, options),
            Self::Pow(pow) => PrettyPrint::pretty_print(pow, options),
            Self::Fun(fun) => PrettyPrint::pretty_print(&**fun, options),
        }
    }
}
