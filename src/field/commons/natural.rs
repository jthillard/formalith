//! The natural integers set `{$NN$}`

use std::{cmp::Ordering, marker::PhantomData};

use malachite::{
    Integer, Natural, base::num::conversion::traits::FromSciString, rational::Rational,
};

use crate::{
    field::{PartiallyOrderedSet, Set, SetParseExpression, integer::Z},
    parser::Parser,
    printer::PrettyPrinter,
};

/// The natural integers set `{$NN$}`.
///
/// It has no additive inverses, so it is neither a group nor a ring: it only supports ordering.
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

impl<Depth> SetParseExpression<Depth> for N<Natural> {
    fn parse_literal(&self, parser: &mut Parser) -> Result<Option<Self::Element>, String> {
        parser.is_literal_and(|value| {
            let rational = Rational::from_sci_string(value)
                .ok_or_else(|| format!("Failed to parse \"{value}\" to malachite::Natural",))?;
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
