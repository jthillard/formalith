//! The [`OptionalDefault`] trait for types with an optional default value.

use malachite::{Integer, Rational};

use crate::{
    field::{
        cartesian::CartesianPower, complex::C, integer::Z, matrix::M, modular::Zn,
        polynomial::Poly, real::R,
    },
    term::TermSet,
};

/// Same as [Default], but if no default value is meaningful, `None` can be returned.
pub trait OptionalDefault: Sized {
    /// Same as [`Default::default`], but optional.
    fn optional_default() -> Option<Self>;
}

impl OptionalDefault for Z<Integer> {
    fn optional_default() -> Option<Self> {
        Some(Z)
    }
}
impl OptionalDefault for R<Rational> {
    fn optional_default() -> Option<Self> {
        Some(R)
    }
}
impl OptionalDefault for C<R<Rational>> {
    fn optional_default() -> Option<Self> {
        Some(C)
    }
}
impl<T: OptionalDefault, const K: usize> OptionalDefault for CartesianPower<T, K> {
    fn optional_default() -> Option<Self> {
        T::optional_default().map(Self::new)
    }
}
impl OptionalDefault for Zn {
    fn optional_default() -> Option<Self> {
        None
    }
}
impl<K> OptionalDefault for Poly<K> {
    fn optional_default() -> Option<Self> {
        None
    }
}
impl<T> OptionalDefault for M<T> {
    fn optional_default() -> Option<Self> {
        None
    }
}
impl<T> OptionalDefault for TermSet<T> {
    fn optional_default() -> Option<Self> {
        None
    }
}
