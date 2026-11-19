//! The integer ring `{$ZZ$}`

use std::{cmp::Ordering, marker::PhantomData};

use malachite::{
    Integer, Natural,
    base::num::{
        arithmetic::traits::{Abs, DivisibleBy, Factorial, Gcd, Lcm, Mod, Pow, Sign, UnsignedAbs},
        basic::traits::{One, Zero},
    },
};

use super::parse_integer_literal;

use crate::{
    context::Context,
    field::{
        Group, PartiallyOrderedSet, Ring, Set, SetParseExpression, matrix::M, real::MAX_FACTORIAL,
    },
    parser::Parser,
    printer::PrettyPrinter,
    term::{self, Fun, Term, TermSet, Value},
};

/// The integer ring `{$ZZ$}`
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Z<T> {
    phantom: PhantomData<T>,
}

impl<T: Clone> Copy for Z<T> {}

impl Set for Z<Integer> {
    type Element = Integer;

    type ExponantSet = Self; // TODO change type to N ?
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

impl Group for Z<Integer> {
    fn zero(&self) -> Self::Element {
        Integer::ZERO
    }

    fn nth(&self, nth: i64) -> <Self::ProductCoefficientSet as Set>::Element {
        Integer::const_from_signed(nth)
    }

    fn add(&self, a: &Self::Element, b: &Self::Element) -> Self::Element {
        a + b
    }

    fn neg(&self, a: &Self::Element) -> Self::Element {
        -a
    }

    fn to_i64(&self, a: &Self::Element) -> Option<i64> {
        i64::try_from(a).ok()
    }
}

impl Ring for Z<Integer> {
    fn one(&self) -> Self::Element {
        Integer::ONE
    }

    fn mul(&self, a: &Self::Element, b: &Self::Element) -> Self::Element {
        a * b
    }

    fn try_inv(&self, a: &Self::Element) -> Option<Self::Element> {
        if *a == 1 {
            Some(Integer::const_from_unsigned(1))
        } else if *a == -1 {
            Some(Integer::const_from_signed(-1))
        } else {
            None
        }
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
                    (Context::FACTORIAL, Some([Term::Value(n)])) => {
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
