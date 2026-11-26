//! Numerical approximations of complex expressions, from the approximations of their real and imaginary parts.

use malachite::{Rational, base::num::basic::traits::Zero};

use super::{C, Complex, parts};
use crate::{
    field::real::approx::{Approximate, approximate, round_significant},
    term::{Term, Value, flags::Flags},
};

impl Approximate for Complex {
    /// Approximate a constant `z` to `digits` significant digits in each part.
    fn approximate_constant(z: &Term<Self>, digits: u64) -> Option<Term<Self>> {
        if !parts::is_constant(z) {
            return None;
        }
        let (u, v) = parts::split(z)?;
        let re = approximate(&u, digits)?;
        let im = if v.is_zero() {
            Rational::ZERO
        } else {
            approximate(&v, digits)?
        };
        let mut res = Term::Value(Value::new([re, im], C));
        res.set_approximate(true);
        Some(res)
    }

    fn round_coefficient([re, im]: &[Rational; 2], digits: u64) -> [Rational; 2] {
        [round_significant(re, digits), round_significant(im, digits)]
    }

    fn is_integer([re, im]: &[Rational; 2]) -> bool {
        *im == 0 && *re.denominator_ref() == 1
    }
}
