//! The ring of integers modulo `n`, `{$ZZ\/n ZZ$}`.

use std::cmp::Ordering;

use malachite::{
    Integer, Natural,
    base::num::{
        arithmetic::traits::{Mod, ModPow, UnsignedAbs},
        conversion::traits::ExactFrom,
    },
};

use super::parse_integer_literal;

use crate::term::fun::{
    eval_algebra_builtin, eval_degree, eval_matrix_builtin, eval_rewrite_builtin,
};
use crate::{
    context::{Context, Symbol},
    field::{
        Group, Monoid, PartiallyOrderedSet, Ring, Semiring, Set, SetParseExpression, integer::Z,
        matrix::M,
    },
    parser::Parser,
    polynom::factor::modular::{factor_with_multiplicities, is_prime},
    printer::{PrettyPrinter, PrintOptions},
    term::{self, Expand, SymbolTerm, Term, TermSet},
};

/// The ring of integers modulo `n`, `{$ZZ\/n ZZ$}`, which is a field when `n` is prime.
///
/// The modulus is chosen at runtime, elements are their representative in `{$[0, n)$}`.
/// ```
/// use formalith::{field::modular::Zn, parse};
///
/// let z7 = Zn::new(7);
/// assert_eq!(parse!("3*5", z7), parse!("1", z7));
/// assert_eq!(parse!("1/3", z7), parse!("5", z7));
/// ```
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Zn {
    modulus: u64,
}

impl Zn {
    /// Create the ring `{$ZZ\/n ZZ$}`.
    ///
    /// # Panics
    /// Panics if `n` is lower than 2 or greater than `{$2^63$}`.
    #[must_use]
    pub const fn new(n: u64) -> Self {
        assert!(
            n >= 2 && n <= 1 << 63,
            "The modulus must be between 2 and 2^63"
        );
        Self { modulus: n }
    }

    /// Get the modulus `n`.
    #[must_use]
    pub const fn modulus(&self) -> u64 {
        self.modulus
    }

    /// Check if this ring is a field, i.e. if its modulus is prime.
    #[must_use]
    pub fn is_field(&self) -> bool {
        is_prime(self.modulus)
    }

    /// Reduce an integer modulo `n`.
    #[must_use]
    pub fn reduce(&self, n: &Integer) -> u64 {
        // The remainder is below the modulus
        u64::exact_from(&n.mod_op(Integer::from(self.modulus)))
    }

    /// Compute `base^exponant`, returning `None` for negative powers of non invertible elements.
    fn pow(self, base: u64, exponant: &Integer) -> Option<u64> {
        let base = if *exponant < 0 {
            self.try_inv(&base)?
        } else {
            base
        };
        let res = Natural::from(base).mod_pow(exponant.unsigned_abs(), Natural::from(self.modulus));
        Some(u64::try_from(&res).expect("Reduced integer fits in u64"))
    }

    /// Get the coefficients of a univariate polynomial expression, lowest degree first, with its variable.
    ///
    /// Returns `None` if the expression isn't an expanded polynomial in a single symbol.
    fn univariate(self, term: &Term<Self>) -> Option<(Symbol, Vec<u64>)> {
        const MAX_DEGREE: usize = 1 << 16;
        let mut variable = None;
        let mut coefficients = vec![0];
        let monomials = match term {
            Term::Add(add) => add.terms.as_slice(),
            term => std::slice::from_ref(term),
        };
        for monomial in monomials {
            let (coefficient, power) = match monomial {
                Term::Value(value) => {
                    coefficients[0] = self.add(&coefficients[0], &value.value);
                    continue;
                }
                Term::Mul(mul) if mul.factors.len() == 1 => (mul.coefficient, &mul.factors[0]),
                term => (1, term),
            };
            let (symbol, degree) = match power {
                Term::Symbol(symbol) => (symbol.symbol, 1),
                Term::Pow(term::Pow { base, exponant, .. }) => match (&**base, &***exponant) {
                    (Term::Symbol(symbol), Term::Value(exponant)) => (
                        symbol.symbol,
                        usize::try_from(&exponant.value)
                            .ok()
                            .filter(|degree| *degree <= MAX_DEGREE)?,
                    ),
                    _ => return None,
                },
                _ => return None,
            };
            if *variable.get_or_insert(symbol) != symbol {
                return None;
            }
            if coefficients.len() <= degree {
                coefficients.resize(degree + 1, 0);
            }
            coefficients[degree] = self.add(&coefficients[degree], &coefficient);
        }
        while coefficients.last() == Some(&0) {
            coefficients.pop();
        }
        variable.map(|variable| (variable, coefficients))
    }

    /// Build the expression `{$sum c_i x^i$}`.
    fn polynomial(self, coefficients: &[u64], x: &Term<Self>) -> Term<Self> {
        coefficients
            .iter()
            .enumerate()
            .filter(|(_, c)| **c != 0)
            .fold(Term::zero(self), |res, (i, c)| {
                res + Term::constant(*c, self) * x.pow(&Term::constant(Integer::from(i), Z))
            })
    }

    /// Factor a univariate polynomial expression into irreducible factors, when the modulus is prime.
    pub(crate) fn factor(self, term: &Term<Self>) -> Option<Term<Self>> {
        let expanded = term.expand();
        // A constant, like a polynomial whose other coefficients are multiples of `n`
        if let Term::Value(_) = expanded {
            return Some(expanded);
        }
        if !self.is_field() {
            return None;
        }
        let (variable, coefficients) = self.univariate(&expanded)?;
        let leading_coefficient = *coefficients.last()?;
        let x = Term::Symbol(SymbolTerm::new(variable, self));
        Some(
            factor_with_multiplicities(&coefficients, self.modulus)
                .into_iter()
                .fold(
                    Term::constant(leading_coefficient, self),
                    |res, (factor, multiplicity)| {
                        res * self
                            .polynomial(&factor, &x)
                            .pow(&Term::constant(Integer::from(multiplicity), Z))
                    },
                ),
        )
    }
}

impl Set for Zn {
    type Element = u64;
    type ExponantSet = Z<Integer>;
    type ProductCoefficientSet = Self;

    fn get_exponant_set(&self) -> Self::ExponantSet {
        Z
    }
    fn get_coefficient_set(&self) -> Self::ProductCoefficientSet {
        *self
    }
    fn print(
        &self,
        elem: &Self::Element,
        _: &PrintOptions,
        f: &mut std::fmt::Formatter<'_>,
    ) -> std::fmt::Result {
        write!(f, "{elem}")
    }
    fn pretty_print(&self, elem: &Self::Element, _: &PrintOptions) -> PrettyPrinter {
        PrettyPrinter::from(format!("{elem}"))
    }
    fn element_eq(&self, a: &Self::Element, b: &Self::Element) -> bool {
        a == b
    }
}

impl PartiallyOrderedSet for Zn {
    /// There is no order compatible with the ring operations, elements are only compared for equality.
    fn partial_cmp(&self, a: &Self::Element, b: &Self::Element) -> Option<Ordering> {
        (a == b).then_some(Ordering::Equal)
    }
}

impl Monoid for Zn {
    fn zero(&self) -> Self::Element {
        0
    }

    fn add(&self, a: &Self::Element, b: &Self::Element) -> Self::Element {
        u64::try_from((u128::from(*a) + u128::from(*b)) % u128::from(self.modulus))
            .expect("Reduced integer fits in u64")
    }
}

impl Group for Zn {
    fn nth(&self, nth: i64) -> Self::Element {
        u64::try_from(i128::from(nth).rem_euclid(i128::from(self.modulus)))
            .expect("Reduced integer fits in u64")
    }

    fn neg(&self, a: &Self::Element) -> Self::Element {
        if *a == 0 { 0 } else { self.modulus - a }
    }
}

impl Semiring for Zn {
    fn one(&self) -> Self::Element {
        1
    }

    fn mul(&self, a: &Self::Element, b: &Self::Element) -> Self::Element {
        u64::try_from((u128::from(*a) * u128::from(*b)) % u128::from(self.modulus))
            .expect("Reduced integer fits in u64")
    }

    fn normalize(&self, a: Term<Self>) -> Term<Self> {
        match &a {
            Term::Pow(term::Pow { base, exponant, .. }) => {
                if let (Term::Value(base), Term::Value(exponant)) = (&**base, &***exponant)
                    && let Some(res) = self.pow(base.value, &exponant.value)
                {
                    return Term::constant(res, *self);
                }
            }
            Term::Fun(fun) => match fun.get_ident() {
                Context::EXPAND | Context::SIMPLIFY => {
                    if let Some(res) = eval_rewrite_builtin(&**fun) {
                        return res;
                    }
                }
                Context::FACTOR => {
                    if let Some(res) = fun.get_arg::<Self>().and_then(|arg| self.factor(arg)) {
                        return res;
                    }
                }
                Context::DET | Context::TRACE | Context::RANK | Context::CHARPOLY => {
                    if let Some(res) = eval_matrix_builtin(&**fun) {
                        return res;
                    }
                }
                Context::DEGREE => {
                    if let Some(res) = eval_degree(&**fun) {
                        return res;
                    }
                }
                _ => {
                    if let Some(res) = eval_algebra_builtin(&**fun) {
                        return res;
                    }
                }
            },
            _ => {}
        }
        a
    }

    fn expand(&self, a: Term<Self>) -> Term<Self> {
        if let Term::Pow(term::Pow { base, exponant, .. }) = &a
            && let (Term::Add(add), Term::Value(exponant)) = (&**base, &***exponant)
            && let Ok(n) = usize::try_from(&exponant.value)
            && n > 1
        {
            return Term::expand_sum_power(add, n, |n| self.reduce(&n));
        }
        a
    }
}

impl Ring for Zn {
    /// Inverse using the extended Euclidean algorithm, it exists when `a` and `n` are coprime.
    fn try_inv(&self, a: &Self::Element) -> Option<Self::Element> {
        let (mut r0, mut r1) = (i128::from(self.modulus), i128::from(*a));
        let (mut s0, mut s1) = (0i128, 1i128);
        while r1 != 0 {
            let q = r0 / r1;
            (r0, r1) = (r1, r0 - q * r1);
            (s0, s1) = (s1, s0 - q * s1);
        }
        (r0 == 1).then(|| {
            u64::try_from(s0.rem_euclid(i128::from(self.modulus)))
                .expect("Reduced integer fits in u64")
        })
    }
}

impl SetParseExpression for Zn {
    type MatrixArgumentSet = M<TermSet<Self>>;

    fn get_matrix_argument_set(&self) -> Self::MatrixArgumentSet {
        self.get_term_set().get_matrix_set()
    }

    fn parse_literal(&self, parser: &mut Parser) -> Result<Option<Self::Element>, String> {
        parser.is_literal_and(|value| Ok(Some(self.reduce(&parse_integer_literal(value)?))))
    }
}
