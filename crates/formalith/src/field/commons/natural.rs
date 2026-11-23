//! The natural integers set `{$NN$}`

use std::{cmp::Ordering, marker::PhantomData};

use malachite::{
    Integer, Natural,
    base::num::{
        arithmetic::traits::{DivMod, Factorial, Gcd, Lcm, Pow},
        basic::traits::{One, Zero},
    },
};

use super::{parse_rational_literal, primes};

use crate::{
    context::Context,
    field::{
        Monoid, PartiallyOrderedSet, Semiring, Set, SetParseExpression, integer::Z, matrix::M,
        real::MAX_FACTORIAL,
    },
    parser::Parser,
    printer::PrettyPrinter,
    term::{self, Term, TermSet, Value},
};

/// The natural integers set `{$NN$}`.
///
/// It has no additive inverses, so it is a [Semiring] but not a ring: `+`, `*` and powers are defined, `-` and
/// `/` aren't. Coefficients of products and exponents are integers of [`Z`].
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct N<T> {
    phantom: PhantomData<T>,
}

impl<T: Clone> Copy for N<T> {}

impl Set for N<Natural> {
    type Element = Natural;

    // N isn't a group nor a ring, use Z instead
    type ExponantSet = Z<Integer>;
    type ProductCoefficientSet = Z<Integer>;

    fn get_exponant_set(&self) -> Self::ExponantSet {
        Z
    }
    fn get_coefficient_set(&self) -> Self::ProductCoefficientSet {
        Z
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

impl PartiallyOrderedSet for N<Natural> {
    fn partial_cmp(&self, a: &Self::Element, b: &Self::Element) -> Option<Ordering> {
        a.partial_cmp(b)
    }
}

impl Monoid for N<Natural> {
    fn zero(&self) -> Self::Element {
        Natural::ZERO
    }

    fn add(&self, a: &Self::Element, b: &Self::Element) -> Self::Element {
        a + b
    }

    fn to_i64(&self, a: &Self::Element) -> Option<i64> {
        i64::try_from(a).ok()
    }
}

impl Semiring for N<Natural> {
    fn one(&self) -> Self::Element {
        Natural::ONE
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
                // Values are naturals while the coefficient is an integer: fold them into the coefficient, which
                // stays non-negative since nothing has a sign
                let mut coefficient = mul.coefficient.clone();
                let mut factors = vec![];
                for factor in mul {
                    if let Term::Value(value) = factor {
                        coefficient *= Integer::from(&value.value);
                    } else {
                        factors.push(factor.clone());
                    }
                }
                if factors.len() != mul.factors.len() {
                    return match (factors.len(), Natural::try_from(&coefficient)) {
                        (0, Ok(value)) => Term::Value(Value::new(value, *self)),
                        (1, _) if coefficient == 1 => factors.pop().unwrap(),
                        _ => Term::Mul(term::Mul::new(coefficient, factors, *self)),
                    };
                }
            }
            Term::Fun(fun) => match (fun.get_ident(), fun.get_args::<Self>().map(Vec::as_slice)) {
                (Context::ABS, Some([Term::Value(n)])) => return Term::Value(n.clone()),
                (ident @ (Context::GCD | Context::LCM), Some([Term::Value(a), Term::Value(b)])) => {
                    let (a, b) = (&a.value, &b.value);
                    let res = if ident == Context::GCD {
                        a.gcd(b)
                    } else {
                        a.lcm(b)
                    };
                    return Term::Value(Value::new(res, *self));
                }
                (ident @ (Context::QUO | Context::REM), Some([Term::Value(a), Term::Value(b)]))
                    if b.value != 0 =>
                {
                    let (quotient, remainder) = (&a.value).div_mod(&b.value);
                    let res = if ident == Context::QUO {
                        quotient
                    } else {
                        remainder
                    };
                    return Term::Value(Value::new(res, *self));
                }
                (Context::ISPRIME, Some([Term::Value(n)])) => {
                    let prime = primes::is_prime(&n.value);
                    return Term::Value(Value::new(Natural::from(u8::from(prime)), *self));
                }
                (Context::FACTORIAL, Some([Term::Value(n)])) => {
                    if let Ok(n) = u64::try_from(&n.value)
                        && n <= MAX_FACTORIAL
                    {
                        return Term::Value(Value::new(Natural::factorial(n), *self));
                    }
                }
                _ => {}
            },
            _ => {}
        }
        a
    }
}

impl SetParseExpression for N<Natural> {
    type MatrixArgumentSet = M<TermSet<Self>>;

    fn get_matrix_argument_set(&self) -> Self::MatrixArgumentSet {
        self.get_term_set().get_matrix_set()
    }

    fn parse_literal(&self, parser: &mut Parser) -> Result<Option<Self::Element>, String> {
        parser.is_literal_and(|value| {
            let rational = parse_rational_literal(value, "Natural")?;
            Ok(Some(Natural::try_from(rational).map_err(|_| {
                format!("\"{value}\" is not a natural integer")
            })?))
        })
    }
}

/// The natural integers set, using [`malachite::Natural`] as constant to get arbitrary precision natural integers.
pub const N: N<Natural> = N {
    phantom: PhantomData,
};
