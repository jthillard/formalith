//! Power expression.

use std::{fmt::Display, mem::ManuallyDrop};

use crate::{
    field::{Ring, Set},
    printer::{PrettyPrint, Print, PrintOptions},
    term::Normalize,
};

use super::{Flags, Term};

/// A power expression, `base^exponant`.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Pow<T: Set, E: Set = <T as Set>::ExponantSet> {
    flags: u8,
    pub(crate) base: Box<Term<T>>,
    /// `ManuallyDrop` is used to avoid drop-checking which fails for infinite type `T::ExponantSet::ExponantSet::...`
    pub(crate) exponant: ManuallyDrop<Box<Term<E>>>,
    pub(crate) set: T,
}

impl<T: Set> Flags for Pow<T> {
    fn get_flags(&self) -> u8 {
        self.flags
    }
    fn get_flags_mut(&mut self) -> &mut u8 {
        &mut self.flags
    }
}

impl<T: Set> Pow<T> {
    /// Create a new pow expression
    pub fn new<E: Into<Box<Term<T>>>, F: Into<Box<Term<T::ExponantSet>>>>(
        base: E,
        exponant: F,
        set: T,
    ) -> Self {
        Self {
            flags: 0,
            base: base.into(),
            exponant: ManuallyDrop::new(exponant.into()),
            set,
        }
    }

    /// The power with the opposite exponant, `base^(-exponant)`, not normalized.
    #[must_use]
    pub(crate) fn with_negated_exponant(&self) -> Self {
        let mut pow = self.clone();
        **pow.exponant = -&**pow.exponant;
        pow
    }
}

impl<T: Set, E: Set> Drop for Pow<T, E> {
    fn drop(&mut self) {
        unsafe {
            ManuallyDrop::drop(&mut self.exponant);
        }
    }
}
/// Split a fractional exponant `num/index` to print a power as a root.
trait RootExponant: Sized {
    /// Return `(num, index)` if `self` is a fraction, `num` being `None` if it is one and `index` being `None`
    /// for a square root.
    fn root_split(&self) -> Option<(Option<Self>, Option<Self>)>;
}

impl<E: Set> RootExponant for Term<E> {
    default fn root_split(&self) -> Option<(Option<Self>, Option<Self>)> {
        None
    }
}

impl<E: Ring> RootExponant for Term<E> {
    fn root_split(&self) -> Option<(Option<Self>, Option<Self>)> {
        // `x^(a + b/2)` reads better than a root of `x^(2a + b)`
        if matches!(self, Self::Add(_)) || self.needs_normalization() {
            return None;
        }
        let (num, den) = self.as_fraction(false);
        if den.is_one() {
            return None;
        }
        Some((
            (!num.is_one()).then_some(num),
            (den.to_i64() != Some(2)).then_some(den),
        ))
    }
}

impl<T: Set> Pow<T> {
    /// The expression under the radical sign when printing `self` as a root of index the denominator of its exponant.
    fn radicand(&self, num: Option<Term<T::ExponantSet>>) -> Term<T> {
        num.map_or_else(
            || (*self.base).clone(),
            |num| Term::Pow(Self::new(self.base.clone(), num, self.set)),
        )
    }
    /// Pretty print `self` assuming its exponant is positive, as a root if the exponant is a fraction.
    fn pretty_print_positive(&self, options: PrintOptions) -> crate::printer::PrettyPrinter {
        if let Some((num, index)) = self.exponant.root_split() {
            let mut radicand = PrettyPrint::pretty_print(&self.radicand(num), &options);
            radicand.root(index.map(|index| index.pretty_print(&options)).as_ref());
            return radicand;
        }
        let mut base = self.base.pretty_print_operand(options);
        let exponant = self.exponant.pretty_print_operand(options);
        if match &*self.base {
            Term::Mul(_) | Term::Add(_) => true,
            // `-1^x` reads as `-(1^x)`
            Term::Value(value) => {
                !value.set.is_atomic(&value.value) || value.typst().to_string().starts_with('-')
            }
            _ => false,
        } {
            base.paren();
        }
        base.pow(&exponant);
        base
    }
}

impl<T: Set> Print for Pow<T> {
    fn print(&self, options: &PrintOptions, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if options.typst && self.exponant.is_strictly_negative() {
            f.write_str("frac(1, ")?;
            Print::print(
                &Term::Pow(self.with_negated_exponant()).normalize(),
                options,
                f,
            )?;
            return f.write_str(")");
        }
        if options.typst
            && let Some((num, index)) = self.exponant.root_split()
        {
            if let Some(index) = index {
                f.write_str("root(")?;
                index.print(options, f)?;
                f.write_str(", ")?;
            } else {
                f.write_str("sqrt(")?;
            }
            self.radicand(num).print(options, f)?;
            return f.write_str(")");
        }
        // `-1^x` reads as `-(1^x)` (`group` already handles it in typst)
        if !options.typst
            && let Term::Value(value) = &*self.base
            && value.typst().to_string().starts_with('-')
        {
            Self::group_delim("(", options, f)?;
            value.print(options, f)?;
            Self::group_delim(")", options, f)?;
        } else {
            Self::group(&self.base, options, f)?;
        }
        Self::operator("^", options, f)?;
        // `x^1/2` would read as `(x^1)/2`
        if !options.typst
            && let Term::Value(value) = &**self.exponant
            && {
                struct Printed<'a, V>(&'a V, &'a PrintOptions);
                impl<V: Print> Display for Printed<'_, V> {
                    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                        self.0.print(self.1, f)
                    }
                }
                Printed(value, options).to_string().contains('/')
            }
        {
            Self::group_delim("(", options, f)?;
            self.exponant.print(options, f)?;
            Self::group_delim(")", options, f)?;
        } else {
            Self::group(&**self.exponant, options, f)?;
        }
        Ok(())
    }
}

impl<T: Set> PrettyPrint for Pow<T> {
    default fn pretty_print(&self, options: &PrintOptions) -> crate::printer::PrettyPrinter {
        match **self.exponant {
            Term::Value(_) if self.exponant.is_strictly_negative() => {
                self.with_negated_exponant().pretty_print_positive(*options)
            }
            _ => self.pretty_print_positive(*options),
        }
    }
}

impl<T: Ring> PrettyPrint for Pow<T> {
    fn pretty_print(&self, options: &PrintOptions) -> crate::printer::PrettyPrinter {
        // If exponant is negative, print as a fraction
        if matches!(**self.exponant, Term::Value(_)) && self.exponant.is_strictly_negative() {
            let den = match Term::Pow(self.with_negated_exponant()).normalize() {
                Term::Pow(pow) => pow.pretty_print_positive(*options),
                normalized => PrettyPrint::pretty_print(&normalized, options),
            };
            let mut res = PrettyPrint::pretty_print(&Term::one(self.set), options);
            res.vertical_concat("─", &den);
            return res;
        }
        self.pretty_print_positive(*options)
    }
}

impl<T: Set> Display for Pow<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        PrettyPrint::fmt(self, &PrintOptions::default(), f)
    }
}
