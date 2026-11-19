//! The cartesian power `{$T^K$}` of a set.

use std::cmp::Ordering;

use crate::{
    field::{Group, PartiallyOrderedSet, Set},
    printer::{PrettyPrinter, PrintOptions},
};

/// The cartesian power `{$T^K$}` of the set `T`, whose elements are `K`-tuples of elements of `T`.
///
/// Operations are componentwise. It's for instance used to define [`struct@crate::field::complex::C`] as `{$RR^2$}`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct CartesianPower<T, const K: usize> {
    pub(crate) set: T,
}

impl<T, const K: usize> CartesianPower<T, K> {
    /// Create the cartesian power `{$T^K$}` of the set `T`.
    pub const fn new(set: T) -> Self {
        Self { set }
    }
}

impl<T: Set, const K: usize> Set for CartesianPower<T, K> {
    type Element = [T::Element; K];

    type ExponantSet = T::ExponantSet;
    type ProductCoefficientSet = T::ProductCoefficientSet;

    fn get_exponant_set(&self) -> Self::ExponantSet {
        self.set.get_exponant_set()
    }
    fn get_coefficient_set(&self) -> Self::ProductCoefficientSet {
        self.set.get_coefficient_set()
    }
    fn print(
        &self,
        elem: &Self::Element,
        options: &PrintOptions,
        f: &mut std::fmt::Formatter<'_>,
    ) -> std::fmt::Result {
        write!(f, "(")?;
        for (i, component) in elem.iter().enumerate() {
            if i != 0 {
                write!(f, ", ")?;
            }
            self.set.print(component, options, f)?;
        }
        write!(f, ")")
    }
    fn pretty_print(&self, elem: &Self::Element, options: &PrintOptions) -> PrettyPrinter {
        let mut res = PrettyPrinter::empty();
        for component in elem {
            res.concat(",", true, &self.set.pretty_print(component, options));
        }
        res.paren();
        res
    }
    fn element_eq(&self, a: &Self::Element, b: &Self::Element) -> bool {
        a.iter().zip(b).all(|(a, b)| self.set.element_eq(a, b))
    }
}

impl<T: PartiallyOrderedSet, const K: usize> PartiallyOrderedSet for CartesianPower<T, K> {
    /// The product order: `a <= b` if each component of `a` is lower or equal than the matching component of `b`.
    fn partial_cmp(&self, a: &Self::Element, b: &Self::Element) -> Option<Ordering> {
        a.iter().zip(b).try_fold(Ordering::Equal, |res, (a, b)| {
            match (res, self.set.partial_cmp(a, b)?) {
                (res, Ordering::Equal) => Some(res),
                (Ordering::Equal, ordering) => Some(ordering),
                (res, ordering) if res == ordering => Some(res),
                _ => None,
            }
        })
    }
}

impl<T: Group, const K: usize> Group for CartesianPower<T, K> {
    fn zero(&self) -> Self::Element {
        std::array::from_fn(|_| self.set.zero())
    }

    /// The diagonal element `(n, n, ..., n)`.
    fn nth(&self, nth: i64) -> Self::Element {
        std::array::from_fn(|_| self.set.nth(nth))
    }

    fn add(&self, a: &Self::Element, b: &Self::Element) -> Self::Element {
        std::array::from_fn(|i| self.set.add(&a[i], &b[i]))
    }

    fn neg(&self, a: &Self::Element) -> Self::Element {
        std::array::from_fn(|i| self.set.neg(&a[i]))
    }
}

#[cfg(test)]
mod tests {
    use std::cmp::Ordering;

    use malachite::Rational;

    use crate::field::{Group, PartiallyOrderedSet, Set, real::R};

    fn pair(a: i64, b: i64) -> [Rational; 2] {
        [Rational::from(a), Rational::from(b)]
    }

    #[test]
    fn componentwise_group() {
        let set = R.get_cartesian_power::<2>();
        assert_eq!(set.add(&pair(1, 2), &pair(3, -5)), pair(4, -3));
        assert_eq!(set.neg(&pair(1, -2)), pair(-1, 2));
        assert_eq!(set.zero(), pair(0, 0));
        assert_eq!(set.nth(3), pair(3, 3));
    }

    #[test]
    fn product_order() {
        let set = R.get_cartesian_power::<2>();
        assert_eq!(
            set.partial_cmp(&pair(1, 2), &pair(1, 2)),
            Some(Ordering::Equal)
        );
        assert_eq!(
            set.partial_cmp(&pair(1, 2), &pair(1, 3)),
            Some(Ordering::Less)
        );
        assert_eq!(
            set.partial_cmp(&pair(2, 3), &pair(1, 2)),
            Some(Ordering::Greater)
        );
        assert_eq!(set.partial_cmp(&pair(1, 3), &pair(2, 2)), None);
    }
}
