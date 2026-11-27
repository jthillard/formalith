//! The integer ring `{$ZZ$}`

use std::{cmp::Ordering, marker::PhantomData};

use malachite::{
    Integer, Natural, Rational,
    base::num::{
        arithmetic::traits::{
            Abs, DivMod, DivisibleBy, Factorial, Gcd, Lcm, Mod, Parity, Pow, Sign, UnsignedAbs,
        },
        basic::traits::{NegativeOne, One, Zero},
    },
};

use super::{parse_integer_literal, primes};

use crate::combinatorics::Combinatorics;

use crate::{
    context::{Context, Symbol},
    field::{
        EuclideanRing, Group, Monoid, PartiallyOrderedSet, Ring, Semiring, Set, SetParseExpression,
        matrix::M,
        real::{
            MAX_FACTORIAL,
            expr::{Expr, value, variable, zero},
        },
    },
    parser::Parser,
    polynom::ToTerm,
    printer::PrettyPrinter,
    term::{
        self, Expand, Fun, SymbolTerm, Term, TermSet, Value,
        fun::{eval_integer_sum, eval_ring_builtin},
    },
};

/// The integer ring `{$ZZ$}`
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Z<T> {
    phantom: PhantomData<T>,
}

impl<T: Clone> Copy for Z<T> {}

impl Set for Z<Integer> {
    type Element = Integer;

    // Not `N`: exponent sets must be groups, and polynomial roots and factorization need `ExponantSet = Self`
    type ExponantSet = Self;
    type ProductCoefficientSet = Self;

    fn get_exponant_set(&self) -> Self::ExponantSet {
        *self
    }
    fn get_coefficient_set(&self) -> Self::ProductCoefficientSet {
        *self
    }
    fn print(
        &self,
        elem: &Self::Element,
        _: &crate::printer::PrintOptions,
        f: &mut std::fmt::Formatter<'_>,
    ) -> std::fmt::Result {
        write!(f, "{elem}")
    }
    fn pretty_print(
        &self,
        elem: &Self::Element,
        _: &crate::printer::PrintOptions,
    ) -> crate::printer::PrettyPrinter {
        PrettyPrinter::from(format!("{elem}"))
    }

    fn element_eq(&self, a: &Self::Element, b: &Self::Element) -> bool {
        a == b
    }
}

impl PartiallyOrderedSet for Z<Integer> {
    fn partial_cmp(&self, a: &Self::Element, b: &Self::Element) -> Option<Ordering> {
        a.partial_cmp(b)
    }
}

impl Monoid for Z<Integer> {
    fn zero(&self) -> Self::Element {
        Integer::ZERO
    }

    fn add(&self, a: &Self::Element, b: &Self::Element) -> Self::Element {
        a + b
    }

    fn to_i64(&self, a: &Self::Element) -> Option<i64> {
        i64::try_from(a).ok()
    }
}

impl Group for Z<Integer> {
    fn nth(&self, nth: i64) -> <Self::ProductCoefficientSet as Set>::Element {
        Integer::const_from_signed(nth)
    }

    fn neg(&self, a: &Self::Element) -> Self::Element {
        -a
    }
}

impl Semiring for Z<Integer> {
    fn one(&self) -> Self::Element {
        Integer::ONE
    }

    fn expand(&self, a: Term<Self>) -> Term<Self> {
        if let Term::Pow(term::Pow { base, exponant, .. }) = &a {
            match &**base {
                Term::Add(add) => {
                    if let Some(res) = Term::expand_integer_power(add, exponant, |n| n) {
                        return res;
                    }
                }
                // `{$(c x)^n = c^n x^n$}` for an integer `n`
                Term::Mul(mul) if matches!(&***exponant, Term::Value(_)) => {
                    return Term::distribute_pow(mul, exponant);
                }
                _ => {}
            }
        }
        a
    }

    fn mul(&self, a: &Self::Element, b: &Self::Element) -> Self::Element {
        a * b
    }

    fn normalize(&self, a: Term<Self>) -> Term<Self> {
        match &a {
            Term::Pow(term::Pow { base, exponant, .. }) => {
                if let (Term::Value(base), Term::Value(exponant)) = (&**base, &***exponant)
                    && let Ok(exponant) = u64::try_from(&exponant.value)
                {
                    return Term::Value(Value::new(Pow::pow(&base.value, exponant), *self));
                }
            }
            Term::Mul(mul) => {
                // Divide the coefficient by constant factors like `7^-1` when the division is exact
                let mut coeff = mul.coefficient.clone();
                let mut factors = vec![];
                for factor in mul {
                    if let Term::Pow(term::Pow { base, exponant, .. }) = factor
                        && let (Term::Value(base), Term::Value(exponant)) = (&**base, &***exponant)
                        && exponant.value.sign() == Ordering::Less
                        && let Ok(exponant) = u64::try_from(&-&exponant.value)
                    {
                        let divisor = Pow::pow(&base.value, exponant);
                        if (&coeff).divisible_by(&divisor) {
                            coeff /= divisor;
                            continue;
                        }
                    }
                    factors.push(factor.clone());
                }
                if factors.len() != mul.factors.len() {
                    return match factors.len() {
                        0 => Term::Value(Value::new(coeff, *self)),
                        1 if coeff == 1 => factors.pop().unwrap(),
                        _ => Term::Mul(term::Mul::new(coeff, factors, *self)),
                    };
                }
            }
            Term::Fun(fun) => {
                if let Some(res) = eval_ring_builtin(&**fun)
                    .or_else(|| eval_integer_sum(&**fun, |t| Some(t.clone())))
                {
                    return res;
                }
                if fun.get_ident() == Context::ABS
                    && let Some(fun) = fun.as_any().downcast_ref::<Fun<Self>>()
                    && let Some(Term::Value(value)) = fun.args.first()
                {
                    return Term::Value(Value::new((&value.value).abs(), *self));
                }
                match (fun.get_ident(), fun.get_args::<Self>().map(Vec::as_slice)) {
                    (
                        ident @ (Context::GCD | Context::LCM),
                        Some([Term::Value(a), Term::Value(b)]),
                    ) => {
                        let (a, b) = ((&a.value).unsigned_abs(), (&b.value).unsigned_abs());
                        let res = if ident == Context::GCD {
                            a.gcd(b)
                        } else {
                            a.lcm(b)
                        };
                        return Term::Value(Value::new(Integer::from(res), *self));
                    }
                    (ident @ (Context::GCD | Context::LCM), Some([a, b])) => {
                        if let Some(res) = polynomial_gcd_lcm(ident, a, b) {
                            return res;
                        }
                    }
                    (Context::ISPRIME, Some([Term::Value(n)])) => {
                        let prime = Natural::try_from(&n.value).is_ok_and(|n| primes::is_prime(&n));
                        return Term::Value(Value::new(Integer::from(u8::from(prime)), *self));
                    }
                    (Context::FACTOR, Some([arg])) => return arg.factor(),
                    (Context::BINOMIAL, Some([Term::Value(n), Term::Value(k)])) => {
                        return Term::Value(Value::new(binomial(&n.value, &k.value), *self));
                    }
                    (Context::FACTORIAL, Some([Term::Value(n)])) => {
                        // Poles at the negative integers
                        if n.value < 0 {
                            return Term::Symbol(SymbolTerm::new(Context::UNDEFINED, *self));
                        }
                        if let Ok(n) = u64::try_from(&n.value)
                            && n <= MAX_FACTORIAL
                        {
                            return Term::Value(Value::new(
                                Integer::from(Natural::factorial(n)),
                                *self,
                            ));
                        }
                    }
                    _ => {}
                }
                if let ident @ (Context::QUO | Context::REM) = fun.get_ident()
                    && let Some([Term::Value(a), Term::Value(b)]) =
                        fun.get_args::<Self>().map(Vec::as_slice)
                    && b.value != 0
                {
                    // Euclidean division, with a remainder in `{$[0, |b|)$}`
                    let remainder = (&a.value).mod_op((&b.value).abs());
                    return Term::Value(Value::new(
                        if ident == Context::REM {
                            remainder
                        } else {
                            (&a.value - remainder) / &b.value
                        },
                        *self,
                    ));
                }
            }
            _ => {}
        }
        a
    }
}

/// `{$binom(n, k)$}` for integers, `{$(-1)^k binom(k - n - 1, k)$}` for `{$n < 0$}` and 0 for `{$k < 0$}`.
fn binomial(n: &Integer, k: &Integer) -> Integer {
    if *k < 0 {
        Integer::ZERO
    } else if *n < 0 {
        let res = Integer::binom(k - n - Integer::ONE, k.clone());
        if k.odd() { -res } else { res }
    } else {
        Integer::binom(n.clone(), k.clone())
    }
}

impl Ring for Z<Integer> {
    fn try_inv(&self, a: &Self::Element) -> Option<Self::Element> {
        if *a == 1 {
            Some(Integer::const_from_unsigned(1))
        } else if *a == -1 {
            Some(Integer::const_from_signed(-1))
        } else {
            None
        }
    }
}
impl EuclideanRing for Z<Integer> {
    fn rem(&self, a: &Self::Element, b: &Self::Element) -> Self::Element {
        self.quot_rem(a, b).1
    }

    /// Floor division, the remainder having the sign of `b`, so it is in `{$[0, b)$}` for `{$b > 0$}`.
    fn quot_rem(&self, a: &Self::Element, b: &Self::Element) -> (Self::Element, Self::Element) {
        a.div_mod(b)
    }

    /// Non-negative greatest common divisor.
    fn gcd(&self, a: &Self::Element, b: &Self::Element) -> Self::Element {
        Integer::from(a.unsigned_abs().gcd(b.unsigned_abs()))
    }

    fn normal_unit(&self, a: &Self::Element) -> Self::Element {
        if *a < 0 {
            Integer::NEGATIVE_ONE
        } else {
            Integer::ONE
        }
    }
}

impl SetParseExpression for Z<Integer> {
    type MatrixArgumentSet = M<TermSet<Self>>;

    fn get_matrix_argument_set(&self) -> Self::MatrixArgumentSet {
        self.get_term_set().get_matrix_set()
    }

    fn parse_literal(&self, parser: &mut Parser) -> Result<Option<Self::Element>, String> {
        parser.is_literal_and(|value| Ok(Some(parse_integer_literal(value)?)))
    }
}

/// The integer ring, using [`malachite::Integer`] as constant to get arbitrary precision integers.
pub const Z: Z<Integer> = Z {
    phantom: PhantomData,
};

/// `{$gcd(a, b)$}` or `{$"lcm"(a, b)$}` of polynomials with integer coefficients, by Gauss's lemma: the gcd (or
/// lcm) of their contents times the primitive part of their gcd (or lcm) over `{$QQ$}`, with a positive leading
/// coefficient. `{$gcd(2x^2 - 2, 4x - 4) = 2x - 2$}`.
fn polynomial_gcd_lcm(
    ident: Symbol,
    a: &Term<Z<Integer>>,
    b: &Term<Z<Integer>>,
) -> Option<Term<Z<Integer>>> {
    let (a, b) = (
        to_real(&a.expand())?.expand(),
        to_real(&b.expand())?.expand(),
    );
    let (content_a, content_b) = (content(&a), content(&b));
    let (a_poly, b_poly) = (a.to_polynomial(), b.to_polynomial());
    let (content, rational) = if ident == Context::GCD {
        (content_a.gcd(content_b), a_poly.gcd(&b_poly).to_term())
    } else {
        (content_a.lcm(content_b), a_poly.lcm(&b_poly)?.to_term())
    };
    let rational = rational.expand();
    if rational.is_zero() || content == 0u32 {
        return Some(Term::zero(Z));
    }
    // The primitive part, from the leading coefficient of the polynomial over `{$QQ$}`, which is monic
    let coefficients = coefficients(&rational);
    let denominators = coefficients
        .iter()
        .fold(Natural::ONE, |res, c| res.lcm(c.denominator_ref()));
    let numerators = coefficients.iter().fold(Natural::ZERO, |res, c| {
        res.gcd(c.numerator_ref() * &denominators / c.denominator_ref())
    });
    let scale = Rational::from_naturals(denominators, numerators);
    let primitive = from_real(&(value(scale) * rational).expand())?;
    Some((Term::constant(Integer::from(content), Z) * primitive).expand())
}

/// The coefficients of the monomials of an expanded polynomial.
fn coefficients(p: &Expr) -> Vec<Rational> {
    let coefficient = |t: &Expr| match t {
        Term::Value(v) => v.value.clone(),
        Term::Mul(mul) => mul.coefficient.clone(),
        _ => Rational::ONE,
    };
    match p {
        Term::Add(add) => add.iter().map(coefficient).collect(),
        _ => vec![coefficient(p)],
    }
}

/// The content of an expanded polynomial with integer coefficients, the gcd of its coefficients.
fn content(p: &Expr) -> Natural {
    coefficients(p)
        .iter()
        .fold(Natural::ZERO, |res, c| res.gcd(c.numerator_ref()))
}

/// A polynomial of `{$ZZ$}` as a real expression, `None` for other terms.
fn to_real(t: &Term<Z<Integer>>) -> Option<Expr> {
    Some(match t {
        Term::Value(v) => value(Rational::from(&v.value)),
        Term::Symbol(s) => variable(s.symbol),
        Term::Add(add) => add
            .iter()
            .try_fold(zero(), |res, t| Some(res + to_real(t)?))?,
        Term::Mul(mul) => mul
            .iter()
            .try_fold(value(Rational::from(&mul.coefficient)), |res, t| {
                Some(res * to_real(t)?)
            })?,
        Term::Pow(pow) => match &**pow.exponant {
            Term::Value(n) if n.value >= 0 => {
                to_real(&pow.base)?.pow(&value(Rational::from(&n.value)))
            }
            _ => return None,
        },
        Term::Fun(_) => return None,
    })
}

/// A polynomial with integer coefficients as a term of `{$ZZ$}`, `None` for other terms.
fn from_real(t: &Expr) -> Option<Term<Z<Integer>>> {
    let integer = |q: &Rational| Integer::try_from(q).ok();
    Some(match t {
        Term::Value(v) => Term::constant(integer(&v.value)?, Z),
        Term::Symbol(s) => Term::Symbol(SymbolTerm::new(s.symbol, Z)),
        Term::Add(add) => add
            .iter()
            .try_fold(Term::zero(Z), |res, t| Some(res + from_real(t)?))?,
        Term::Mul(mul) => mul
            .iter()
            .try_fold(Term::constant(integer(&mul.coefficient)?, Z), |res, t| {
                Some(res * from_real(t)?)
            })?,
        Term::Pow(pow) => match &**pow.exponant {
            Term::Value(n) => from_real(&pow.base)?.pow(&Term::constant(integer(&n.value)?, Z)),
            _ => return None,
        },
        Term::Fun(_) => return None,
    })
}
