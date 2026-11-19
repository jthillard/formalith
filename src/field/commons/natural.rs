//! The natural integers set `{$NN$}`

use std::{cmp::Ordering, marker::PhantomData};

use malachite::{Integer, Natural};

use super::parse_rational_literal;

use crate::{
    field::{PartiallyOrderedSet, Set, SetParseExpression, integer::Z, matrix::M},
    parser::Parser,
    printer::PrettyPrinter,
    term::TermSet,
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
