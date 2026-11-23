//! Numerical approximations of complex expressions, from the approximations of their real and imaginary parts.

use malachite::{Rational, base::num::basic::traits::Zero};

use super::{C, Complex, parts};
use crate::{
    context::Context,
    field::real::approx::{DEFAULT_DIGITS, MAX_DIGITS, approximate, round_significant},
    term::{Add, Fun, Mul, Normalize, Term, Value, flags::Flags},
};

/// Evaluate `{$"approx"(z, "digits")$}`, `None` for invalid arguments.
pub(super) fn eval_approx(args: &[Term<Complex>]) -> Option<Term<Complex>> {
    let (z, digits) = match args {
        [z] => (z, DEFAULT_DIGITS),
        [z, Term::Value(digits)] if digits.value[1] == 0 => {
            (z, u64::try_from(&digits.value[0]).ok()?)
        }
        _ => return None,
    };
    (1..=MAX_DIGITS)
        .contains(&digits)
        .then(|| approximate_term(z, digits))
}

/// Approximate a constant `z` to `digits` significant digits in each part.
fn approximate_constant(z: &Term<Complex>, digits: u64) -> Option<Term<Complex>> {
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

/// Approximate the numerical parts of `term` to `digits` significant digits, keeping symbols, like
/// `{$x + 0.540302305868140 + 0.841470984807897 i$}` for `{$x + e^i$}`. Integer exponents are kept exact.
fn approximate_term(term: &Term<Complex>, digits: u64) -> Term<Complex> {
    if let Some(res) = approximate_constant(term, digits) {
        return res;
    }
    match term {
        Term::Value(_) | Term::Symbol(_) => term.clone(),
        Term::Add(add) => Term::Add(Add::new(
            add.iter()
                .map(|term| approximate_term(term, digits))
                .collect(),
            C,
        ))
        .normalize(),
        Term::Mul(mul) => {
            let [re, im] = &mul.coefficient;
            let mut res = Mul::new(
                [round_significant(re, digits), round_significant(im, digits)],
                mul.iter()
                    .map(|factor| approximate_term(factor, digits))
                    .collect(),
                C,
            );
            res.set_approximate(true);
            Term::Mul(res).normalize()
        }
        Term::Pow(pow) => {
            let exponant: &Term<Complex> = &pow.exponant;
            let exponant = match exponant {
                Term::Value(value)
                    if value.value[1] == 0 && *value.value[0].denominator_ref() == 1 =>
                {
                    exponant.clone()
                }
                _ => approximate_term(exponant, digits),
            };
            approximate_term(&pow.base, digits).pow(&exponant)
        }
        Term::Fun(fun) => fun.get_args::<Complex>().map_or_else(
            || term.clone(),
            |args| {
                let args = args
                    .iter()
                    .enumerate()
                    .map(|(i, arg)| {
                        // The order of `{$psi^((m))$}` stays an integer
                        if i == 0 && fun.get_ident() == Context::POLYGAMMA {
                            arg.clone()
                        } else {
                            approximate_term(arg, digits)
                        }
                    })
                    .collect();
                Term::Fun(Box::new(Fun::new(fun.get_ident(), args, C))).normalize()
            },
        ),
    }
}
