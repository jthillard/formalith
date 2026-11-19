//! Sets specificities implementation.

use std::{cmp::Ordering, fmt, hash::Hash};

use malachite::Integer;

use crate::{
    context::Symbol,
    field::{cartesian::CartesianPower, matrix::M, polynomial::Poly},
    parser::{Parser, ParserError},
    printer::{PrettyPrinter, PrintOptions},
    term::{Add, Mul, Pow, SymbolTerm, Term, TermSet, Value},
    traits::optional_default::OptionalDefault,
};

pub mod commons;
pub use commons::*;

/// A set.
pub trait Set: Clone + Copy + fmt::Debug + PartialEq + Eq + Hash + 'static {
    /// The type of the elements living in this set
    type Element: Clone + fmt::Debug + PartialEq + Eq + Hash;

    /// The set where exponants live. Mostly [`const@integer::Z`], but it can be any group,
    /// like [`const@real::R`] for real numbers since power is not only a notation for `x*x*...*x` but a defined operation.
    type ExponantSet: Group + OptionalDefault;

    /// The set where coefficients in product live. Mostly [`const@integer::Z`], but it can be any ring.
    type ProductCoefficientSet: Ring + OptionalDefault;

    /// Get the exponant set for this set
    fn get_exponant_set(&self) -> Self::ExponantSet;

    /// Get the coefficient set for this set
    fn get_coefficient_set(&self) -> Self::ProductCoefficientSet;

    /// Print an element of this set.
    ///
    /// # Errors
    /// Returns an error if the formatter fails.
    fn print(
        &self,
        elem: &Self::Element,
        options: &PrintOptions,
        f: &mut std::fmt::Formatter<'_>,
    ) -> std::fmt::Result;

    /// Pretty print an element of this set.
    fn pretty_print(&self, elem: &Self::Element, options: &PrintOptions) -> PrettyPrinter;

    /// Print an element of this set which is a numerical approximation, like a decimal number. Defaults to
    /// [`Set::print`].
    ///
    /// # Errors
    /// Returns an error if the formatter fails.
    fn print_approximate(
        &self,
        elem: &Self::Element,
        options: &PrintOptions,
        f: &mut std::fmt::Formatter<'_>,
    ) -> std::fmt::Result {
        self.print(elem, options, f)
    }

    /// Pretty print an element of this set which is a numerical approximation. Defaults to [`Set::pretty_print`].
    fn pretty_print_approximate(
        &self,
        elem: &Self::Element,
        options: &PrintOptions,
    ) -> PrettyPrinter {
        self.pretty_print(elem, options)
    }

    /// Get associated matrix set
    fn get_matrix_set(&self) -> M<Self> {
        M::new(*self)
    }

    /// Get associated term set
    fn get_term_set(&self) -> TermSet<Self> {
        TermSet::new(*self)
    }

    /// Get the ring `{$T[x]$}` of polynomials in `variable` with coefficients in this set
    fn get_polynomial_ring(&self, variable: Symbol) -> Poly<Self> {
        Poly::new(*self, variable)
    }

    /// Get the cartesian power `{$T^K$}` of this set
    fn get_cartesian_power<const K: usize>(&self) -> CartesianPower<Self, K> {
        CartesianPower::new(*self)
    }

    /// Compares two elements of this set and returns true if they are equals.
    fn element_eq(&self, a: &Self::Element, b: &Self::Element) -> bool;

    /// Checks if an element is printed as a single operand. Non atomic elements, like `2*i`, are wrapped in parentheses
    /// when used as an operand of a power or of a product.
    fn is_atomic(&self, _elem: &Self::Element) -> bool {
        true
    }

    /// Checks if an element is printed as a sum, like `1+2*i`, and needs parentheses when used as a product coefficient.
    fn is_sum(&self, _elem: &Self::Element) -> bool {
        false
    }
}

/// A set with a partial ordering.
pub trait PartiallyOrderedSet: Set {
    /// Compares two elements of this set if possible, returns `None` otherwise
    fn partial_cmp(&self, a: &Self::Element, b: &Self::Element) -> Option<Ordering>;
}

/// A group is a set and a binary operation `+` and :
/// - `+` is associative
/// - `+` has an identity element `zero`
/// - Every element has an inverse element
pub trait Group: PartiallyOrderedSet {
    /// Get the zero (aka identity element for `+`) of this group
    fn zero(&self) -> Self::Element;
    /// Check if a number is zero.
    ///
    /// Defaults to an equality check with [`Group::zero`], but it's not always a desired behaviour :
    /// `10` in `Z/5Z` is zero (in its equivalence class)
    fn is_zero(&self, a: &Self::Element) -> bool {
        *a == self.zero()
    }
    /// Get the nth element by computing `n * 1`
    fn nth(&self, nth: i64) -> Self::Element;
    /// Add two elements of this group.
    fn add(&self, a: &Self::Element, b: &Self::Element) -> Self::Element;
    /// Add two elements of this group into the first one.
    fn add_assign(&self, a: &mut Self::Element, b: &Self::Element) {
        *a = self.add(a, b);
    }
    /// Add two elements of this group, returning `None` if they can't be added (like matrices of different sizes).
    fn try_add(&self, a: &Self::Element, b: &Self::Element) -> Option<Self::Element> {
        Some(self.add(a, b))
    }
    /// Computes the symmetric (inverse) element of `a` in this group for `+`
    fn neg(&self, a: &Self::Element) -> Self::Element;
    /// Computes the symmetric (inverse) element of `a` in this group for `+` into `a`
    fn neg_assign(&self, a: &mut Self::Element) {
        *a = self.neg(a);
    }
    /// Subtract two elements of this group.
    fn sub(&self, a: &Self::Element, b: &Self::Element) -> Self::Element {
        self.add(a, &self.neg(b))
    }
    /// Subtract two elements of this group into the first one.
    fn sub_assign(&self, a: &mut Self::Element, b: &Self::Element) {
        *a = self.sub(a, b);
    }

    /// Checks if a is greater or equal than zero in this group.
    fn is_positive(&self, a: &Self::Element) -> bool {
        self.is_zero(a) || self.is_strictly_positive(a)
    }

    /// Checks if a is greater than zero in this group.
    fn is_strictly_positive(&self, a: &Self::Element) -> bool {
        matches!(self.partial_cmp(a, &self.zero()), Some(Ordering::Greater))
    }

    /// Checks if a is less or equal than zero in this group.
    fn is_negative(&self, a: &Self::Element) -> bool {
        self.is_zero(a) || self.is_strictly_negative(a)
    }

    /// Checks if a is less than zero in this group.
    fn is_strictly_negative(&self, a: &Self::Element) -> bool {
        matches!(self.partial_cmp(a, &self.zero()), Some(Ordering::Less))
    }

    /// Return `a` as a machine integer if it is an integer of this group, `None` otherwise or if it's unknown.
    fn to_i64(&self, _a: &Self::Element) -> Option<i64> {
        None
    }
}

/// [Set] trait with additional bounds, limiting exponant set recursion depth.
///
/// Auto implemented.
pub trait SetBound: Set<ExponantSet: Set<ExponantSet = Self::ExponantSet>> {}
impl<T: Set<ExponantSet: Set<ExponantSet = Self::ExponantSet>>> SetBound for T {}

/// Trait to cast an element from a set to another set.
pub trait TryElementFrom<T: Set>: Set {
    /// Try to convert an element of the set T into an element of the set E.
    ///
    /// # Errors
    /// This function should return an `TryCastError` if the cast is impossible.
    fn try_from_element(value: T::Element) -> Result<Self::Element, TryCastError>;
}

// Default implementation
impl<T: Set> TryElementFrom<T> for T {
    fn try_from_element(value: T::Element) -> Result<Self::Element, TryCastError> {
        Ok(value)
    }
}

impl<T: Set, From: Set> TryElementFrom<From> for T {
    default fn try_from_element(_value: From::Element) -> Result<Self::Element, TryCastError> {
        Err(TryCastError("Cast not implemented"))
    }
}

/// A ring is an abelian (commutative) [Group] with a binary operation `*` and :
/// - `*` is associative
/// - `*` has an identity element `one`
/// - `*` is distributive over `+`
pub trait Ring: Group {
    /// Get the one (aka identity element for `*`) of this group
    fn one(&self) -> Self::Element;
    /// Check if a number is one.
    ///
    /// Defaults to an equality check with [`Ring::one`], but it's not always a desired behaviour :
    /// `11`in `Z/5Z` is one (in its equivalence class)
    fn is_one(&self, a: &Self::Element) -> bool {
        *a == self.one()
    }
    /// The one of the same shape as `a`, like the identity matrix of its size: `{$a^0$}`.
    ///
    /// Defaults to [`Ring::one`].
    fn one_like(&self, _a: &Self::Element) -> Self::Element {
        self.one()
    }
    /// Multiply two elements of this ring
    fn mul(&self, a: &Self::Element, b: &Self::Element) -> Self::Element;
    /// Multiply two elements of this ring, returning `None` if they can't be multiplied (like matrices of incompatible sizes).
    fn try_mul(&self, a: &Self::Element, b: &Self::Element) -> Option<Self::Element> {
        Some(self.mul(a, b))
    }
    /// Multiply two elements of this ring into a
    fn mul_assign(&self, a: &mut Self::Element, b: &Self::Element) {
        *a = self.mul(a, b);
    }
    /// Try computing the inverse element of a, returning `None` if it doesn't exist.
    fn try_inv(&self, a: &Self::Element) -> Option<Self::Element>;
    /// Compute `{$"base"^"exponant"$}` by squaring, inverting `base` for negative exponants. Returns `None` when
    /// `base` isn't invertible for a negative exponant, or when the exponant doesn't fit in a `u64`.
    fn pow_integer(&self, base: &Self::Element, exponant: &Integer) -> Option<Self::Element> {
        let mut square = if *exponant < 0 {
            self.try_inv(base)?
        } else {
            base.clone()
        };
        let mut remaining = u64::try_from(exponant.unsigned_abs_ref()).ok()?;
        let mut res = self.one();
        while remaining != 0 {
            if remaining & 1 == 1 {
                res = self.mul(&res, &square);
            }
            remaining >>= 1;
            if remaining != 0 {
                square = self.mul(&square, &square);
            }
        }
        Some(res)
    }

    /// Return the expression as a rational expression, (numerator, denominator)
    fn as_fraction(&self, a: &Self::Element) -> (Self::Element, Self::Element) {
        (a.clone(), self.one())
    }
    /// Greatest common divisor of the numeric content of `a` and `b`, a constant which can be cancelled in a
    /// fraction. `{$gcd(0, b)$}` must be `b` up to a unit.
    ///
    /// Defaults to one, meaning there is nothing to cancel.
    fn coefficient_gcd(&self, _a: &Self::Element, _b: &Self::Element) -> Self::Element {
        self.one()
    }

    /// Normalize a mathematical expression using rules specific to this group. Check [`real::R::normalize`]
    fn normalize(&self, a: Term<Self>) -> Term<Self> {
        a
    }

    /// Expand a mathematical expression using rules specific to this group. Check [`M::expand`]
    fn expand(&self, a: Term<Self>) -> Term<Self> {
        a
    }

    /// Simplify a mathematical expression using rules specific to this group. Check [`M::simplify`]
    fn simplify(&self, a: Term<Self>) -> Term<Self> {
        a
    }
}

/// Parsing methods trait.
pub trait SetParseExpression: Set {
    /// The set in which matrix arguments of functions like `det` are parsed, `M<TermSet<Self>>` for scalar sets.
    ///
    /// It must not build a new set from a matrix set (like `M<TermSet<M<...>>>`), otherwise the parser would
    /// be instantiated over infinitely many sets.
    type MatrixArgumentSet: SetParseExpression;

    /// Get the set in which matrix arguments of functions are parsed.
    fn get_matrix_argument_set(&self) -> Self::MatrixArgumentSet;

    /// Parses a string to an element of this set
    ///
    /// # Errors
    /// This method can return an error if the parsing failed.
    fn parse_literal(&self, parser: &mut Parser<'_>) -> Result<Option<Self::Element>, String>;

    /// Custom parsing function, to parse element specific to this set. Check [`M::parse_expression`] for example.
    ///
    /// # Errors
    /// This method can return an error if the parsing failed.
    fn parse_expression(
        &self,
        _parser: &mut Parser<'_>,
    ) -> Result<Option<Term<Self>>, ParserError> {
        Ok(None)
    }

    /// Check if the identifier `name` is a constant of this set, like `i` in `C`, which can't be defined by
    /// the user.
    fn is_constant(&self, _name: &str) -> bool {
        false
    }
}

/// Trait to cast an expression from a set to another set.
pub trait TryExprFrom<From: Set>: Set {
    /// Try to convert an expression over the set T into an expression over the set E.
    ///
    /// # Errors
    /// This function should return an `TryCastError` if the cast is impossible.
    fn try_from_expr(&self, value: Term<From>) -> Result<Term<Self>, TryCastError>;
}
pub(crate) fn try_from_expr_default<From: Set, To: Set>(
    set: &To,
    value: Term<From>,
) -> Result<Term<To>, TryCastError> {
    match value {
        Term::Value(value) => Ok(Term::Value(Value::new(
            <To as TryElementFrom<From>>::try_from_element(value.value)?,
            *set,
        ))),
        Term::Symbol(symbol_term) => {
            Ok(Term::Symbol(SymbolTerm::new(symbol_term.symbol, *set)))
        }
        Term::Add(add) => Ok(Add::new(
            add.terms
                .into_iter()
                .map(|x| set.try_from_expr(x))
                .collect::<Result<Vec<_>, _>>()?,
            *set,
        )
        .into()),
        Term::Mul(mul) => {
            Ok(
                Mul::new(
                    <To::ProductCoefficientSet as TryElementFrom<
                        From::ProductCoefficientSet,
                    >>::try_from_element(mul.coefficient)?,
                    mul.factors
                        .into_iter()
                        .map(|x| TryExprFrom::<From>::try_from_expr(set, x))
                        .collect::<Result<Vec<_>, _>>()?,
                    *set,
                )
                .into(),
            )
        }
        Term::Pow(pow) => Ok(Pow::new(
            Box::new(TryExprFrom::<From>::try_from_expr(
                set,
                (*pow.base).clone(),
            )?),
            Box::new(TryExprFrom::<From::ExponantSet>::try_from_expr(
                &set.get_exponant_set(),
                (**pow.exponant).clone(),
            )?),
            *set,
        )
        .into()),
        Term::Fun(_) => {
            // Function can't be converted. Maybe with constraints we can check if some conversions are possible,
            // and then use a FunctionWrapper struct implementing Function trait to acheive the "conversion"
            Err(TryCastError("Can't cast function"))
        }
    }
}

impl<From: Set, To: Set> TryExprFrom<From> for To {
    default fn try_from_expr(&self, value: Term<From>) -> Result<Term<Self>, TryCastError> {
        try_from_expr_default(self, value)
    }
}

/// A euclidean ring is a [Ring] with a euclidean division, hence a greatest common divisor.
pub trait EuclideanRing: Ring {
    /// Return the remainder of the euclidean division of a by b.
    fn rem(&self, a: &Self::Element, b: &Self::Element) -> Self::Element;
    /// Compute the euclidean division of a by b, returning (quotient, remainder).
    fn quot_rem(&self, a: &Self::Element, b: &Self::Element) -> (Self::Element, Self::Element);
    /// Compute the greatest common divisor of a and b.
    fn gcd(&self, a: &Self::Element, b: &Self::Element) -> Self::Element;
}

/// A field is a [Ring] where every non-zero element is invertible.
pub trait Field: Ring {
    /// Compute the inverse element of a.
    fn inv(&self, a: &Self::Element) -> Self::Element {
        self.try_inv(a)
            .expect("Each elements should be inversible in a field !")
    }
}

/// A [Ring] whose elements can be differentiated with respect to a symbol.
pub trait Derivable: Ring {
    /// The derivative of the element `expr` with respect to `x`.
    fn derivative(&self, expr: &Self::Element, x: Symbol) -> Self::Element;
}
