//! Polynomial rings `{$K[x]$}`.

use std::cmp::Ordering;

use malachite::{Integer, base::num::arithmetic::traits::Parity};

use crate::term::fun::{eval_algebra_builtin, eval_rewrite_builtin, natural_constant};
use crate::{
    context::{Context, Symbol},
    field::{
        EuclideanRing, Group, Monoid, PartiallyOrderedSet, Ring, Semiring, Set, SetParseExpression,
        integer::Z, matrix::M,
    },
    parser::{Parser, lexer::TokenKind},
    polynom::MultivariatePolynomial,
    printer::{PrettyPrint, PrettyPrinter, Print, PrintOptions},
    term::{self, Add, Function, SymbolTerm, Term, TermSet, flags::Flags},
};

/// A polynomial of [`Poly`], with coefficients in `K` and integer exponants.
pub type Polynomial<K> = MultivariatePolynomial<Symbol, K, Z<Integer>>;

/// The ring `{$K[x]$}` of univariate polynomials in `x` with coefficients in `K`.
///
/// Elements are whole polynomials, kept expanded: `x` is parsed as a value of this ring, while other identifiers
/// stay symbols. Polynomials can be divided with `quo` and `rem`, `gcd` and `lcm` are available when the
/// coefficients form a field, and `degree(p)` gives the degree of a non-zero polynomial.
/// ```
/// use formalith::{field::{Set, real::R}, parse, symbol};
///
/// let r_x = R.get_polynomial_ring(symbol!("x"));
/// assert_eq!(parse!("(x+1)^2", r_x), parse!("x^2+2*x+1", r_x));
/// assert_eq!(parse!("gcd(x^2-1, x^2+2*x+1)", r_x), parse!("x+1", r_x));
/// assert_eq!(parse!("degree(x^4-1)", r_x), parse!("4", r_x));
/// ```
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Poly<K> {
    coefficients: K,
    variable: Symbol,
}

impl<K> Poly<K> {
    /// Create the ring of polynomials in `variable` with coefficients in `coefficients`.
    pub const fn new(coefficients: K, variable: Symbol) -> Self {
        Self {
            coefficients,
            variable,
        }
    }

    /// Get the set of coefficients.
    pub const fn coefficients(&self) -> &K {
        &self.coefficients
    }

    /// Get the variable of the polynomials.
    pub const fn variable(&self) -> Symbol {
        self.variable
    }
}

impl<K: Ring> Poly<K> {
    fn normalized(mut a: Polynomial<K>) -> Polynomial<K> {
        a.normalize();
        a
    }

    /// Get the constant polynomial `c`.
    pub fn constant(&self, c: K::Element) -> Polynomial<K> {
        Self::normalized(MultivariatePolynomial::constant(c, self.coefficients, Z))
    }

    /// Get the polynomial `x`.
    pub fn x(&self) -> Polynomial<K> {
        Self::normalized(MultivariatePolynomial::variable(
            self.variable,
            self.coefficients,
            Z,
        ))
    }

    /// Return the coefficient of a constant polynomial, `None` if it isn't constant.
    fn as_constant(&self, a: &Polynomial<K>) -> Option<K::Element> {
        match a.terms() {
            [] => Some(self.coefficients.zero()),
            [(monomial, c)] if monomial.is_empty() => Some(c.clone()),
            _ => None,
        }
    }

    /// Convert an integer to a coefficient.
    fn integer(&self, n: &Integer) -> K::Element {
        if let Ok(n) = i64::try_from(n) {
            return self.coefficients.nth(n);
        }
        let half = self.integer(&(n >> 1u32));
        let double = self.coefficients.add(&half, &half);
        if n.odd() {
            self.coefficients.add(&double, &self.coefficients.one())
        } else {
            double
        }
    }

    /// Convert a polynomial to an expression over its coefficients, keeping the terms sorted by decreasing degree.
    ///
    /// # Panics
    /// Panics if a degree doesn't fit in an `i64`.
    pub fn to_term(&self, a: &Polynomial<K>) -> Term<K> {
        let set = self.coefficients;
        let exponant_set = set.get_exponant_set();
        let x = Term::Symbol(SymbolTerm::new(self.variable, set));
        let mut terms: Vec<Term<K>> = a
            .terms()
            .iter()
            .map(|(monomial, c)| {
                monomial
                    .iter()
                    .fold(Term::constant(c.clone(), set), |res, (_, degree)| {
                        let degree = i64::try_from(degree).expect("Degree fits in i64");
                        res * x.pow(&Term::constant(exponant_set.nth(degree), exponant_set))
                    })
            })
            .collect();
        match terms.len() {
            0 => Term::zero(set),
            1 => terms.pop().unwrap(),
            _ => {
                // Built without normalization, which would sort the terms in another order
                let mut sum = Term::Add(Add::new(terms, set));
                sum.set_normalized(true);
                sum
            }
        }
    }

    /// Evaluate the builtin function `fun`, returning `None` if it can't be evaluated.
    fn eval_builtin(self, fun: &dyn Function<Self>) -> Option<Term<Self>> {
        let value = |value| Term::constant(value, self);
        if let Some(res) = eval_rewrite_builtin(fun).or_else(|| eval_algebra_builtin(fun)) {
            return Some(res);
        }
        match (fun.get_ident(), fun.get_args::<Self>()?.as_slice()) {
            (Context::GCD, [Term::Value(a), Term::Value(b)]) => {
                Some(value(self.gcd(&a.value, &b.value)))
            }
            (Context::LCM, [Term::Value(a), Term::Value(b)]) => {
                if a.value.is_zero() || b.value.is_zero() {
                    return Some(Term::zero(self));
                }
                Some(value(Self::normalized(a.value.lcm(&b.value)?)))
            }
            (ident @ (Context::QUO | Context::REM), [Term::Value(a), Term::Value(b)])
                if !b.value.is_zero() =>
            {
                let (quotient, remainder) = self.quot_rem(&a.value, &b.value);
                Some(value(if ident == Context::QUO {
                    quotient
                } else {
                    remainder
                }))
            }
            (Context::DEGREE, [Term::Value(a)] | [Term::Value(a), Term::Value(_)])
                if !a.value.is_zero()
                    && fun
                        .get_args::<Self>()?
                        .get(1)
                        .is_none_or(|x| *x == value(self.x())) =>
            {
                let degree = i64::try_from(&a.value.degree()).ok()?;
                let degree = natural_constant(self.coefficients, degree)?;
                let Term::Value(degree) = degree else {
                    return None;
                };
                Some(value(self.constant(degree.value)))
            }
            _ => None,
        }
    }
}

impl<K: Ring> Set for Poly<K> {
    type Element = Polynomial<K>;
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
        options: &PrintOptions,
        f: &mut std::fmt::Formatter<'_>,
    ) -> std::fmt::Result {
        Print::print(&self.to_term(elem), options, f)
    }
    fn pretty_print(&self, elem: &Self::Element, options: &PrintOptions) -> PrettyPrinter {
        PrettyPrint::pretty_print(&self.to_term(elem), options)
    }
    fn element_eq(&self, a: &Self::Element, b: &Self::Element) -> bool {
        self.sub(a, b).is_zero()
    }
    fn is_atomic(&self, elem: &Self::Element) -> bool {
        match elem.terms() {
            [] => true,
            [(monomial, c)] if monomial.is_empty() => self.coefficients.is_atomic(c),
            [(_, c)] => self.coefficients.is_one(c),
            _ => false,
        }
    }
    fn is_sum(&self, elem: &Self::Element) -> bool {
        match elem.terms() {
            [(monomial, c)] if monomial.is_empty() => self.coefficients.is_sum(c),
            terms => terms.len() > 1,
        }
    }
}

impl<K: Ring> PartiallyOrderedSet for Poly<K> {
    /// Polynomials are only compared when they are constants.
    fn partial_cmp(&self, a: &Self::Element, b: &Self::Element) -> Option<Ordering> {
        if a == b {
            return Some(Ordering::Equal);
        }
        self.coefficients
            .partial_cmp(&self.as_constant(a)?, &self.as_constant(b)?)
    }
}

impl<K: Ring> Monoid for Poly<K> {
    fn zero(&self) -> Self::Element {
        self.constant(self.coefficients.zero())
    }

    fn is_zero(&self, a: &Self::Element) -> bool {
        a.is_zero()
    }

    fn add(&self, a: &Self::Element, b: &Self::Element) -> Self::Element {
        Self::normalized(a + b)
    }

    fn to_i64(&self, a: &Self::Element) -> Option<i64> {
        self.coefficients.to_i64(&self.as_constant(a)?)
    }
}

impl<K: Ring> Group for Poly<K> {
    fn nth(&self, nth: i64) -> Self::Element {
        self.constant(self.coefficients.nth(nth))
    }

    fn neg(&self, a: &Self::Element) -> Self::Element {
        Self::normalized(&self.zero() - a)
    }

    fn sub(&self, a: &Self::Element, b: &Self::Element) -> Self::Element {
        Self::normalized(a - b)
    }
}

impl<K: Ring> Semiring for Poly<K> {
    fn one(&self) -> Self::Element {
        self.constant(self.coefficients.one())
    }

    fn is_one(&self, a: &Self::Element) -> bool {
        a.is_one()
    }

    fn mul(&self, a: &Self::Element, b: &Self::Element) -> Self::Element {
        Self::normalized(a * b)
    }

    fn normalize(&self, a: Term<Self>) -> Term<Self> {
        match &a {
            Term::Pow(term::Pow { base, exponant, .. }) => {
                if let (Term::Value(base), Term::Value(exponant)) = (&**base, &***exponant)
                    && let Some(res) = self.pow_integer(&base.value, &exponant.value)
                {
                    return Term::constant(res, *self);
                }
            }
            Term::Fun(fun) => {
                if let Some(res) = self.eval_builtin(&**fun) {
                    return res;
                }
            }
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
            return Term::expand_sum_power(add, n, |n| self.constant(self.integer(&n)));
        }
        a
    }
}

impl<K: Ring> Ring for Poly<K> {
    /// Only constants with an invertible coefficient are invertible.
    fn try_inv(&self, a: &Self::Element) -> Option<Self::Element> {
        let c = self.as_constant(a)?;
        Some(self.constant(self.coefficients.try_inv(&c)?))
    }
}

impl<K: Ring> EuclideanRing for Poly<K> {
    fn rem(&self, a: &Self::Element, b: &Self::Element) -> Self::Element {
        self.quot_rem(a, b).1
    }

    fn quot_rem(&self, a: &Self::Element, b: &Self::Element) -> (Self::Element, Self::Element) {
        let (quotient, remainder) = a.quot_rem(b);
        (Self::normalized(quotient), Self::normalized(remainder))
    }

    /// Monic greatest common divisor.
    ///
    /// # Panics
    /// Panics if a leading coefficient met during the computation isn't invertible.
    fn gcd(&self, a: &Self::Element, b: &Self::Element) -> Self::Element {
        Self::normalized(a.gcd(b))
    }
}

impl<K: Ring + SetParseExpression> SetParseExpression for Poly<K> {
    type MatrixArgumentSet = M<TermSet<Self>>;

    fn get_matrix_argument_set(&self) -> Self::MatrixArgumentSet {
        self.get_term_set().get_matrix_set()
    }

    fn parse_literal(&self, parser: &mut Parser) -> Result<Option<Self::Element>, String> {
        if matches!(&parser.token.kind, TokenKind::Ident(ident)
            if *ident == self.variable.name())
        {
            parser.next_token();
            return Ok(Some(self.x()));
        }
        Ok(self
            .coefficients
            .parse_literal(parser)?
            .map(|c| self.constant(c)))
    }

    fn is_constant(&self, name: &str) -> bool {
        name == self.variable.name() || self.coefficients.is_constant(name)
    }
}
