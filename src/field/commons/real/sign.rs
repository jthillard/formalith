//! Signs of real expressions, from their structure, the assumptions on their symbols (see
//! [`assumptions`](crate::context::assumptions)) and numerical approximations of constants.

use malachite::base::num::arithmetic::traits::{Parity, Sign};

use super::{
    approx::approximate,
    expr::{DIGITS, Expr, Real, unary},
};
use crate::{
    context::{
        Context,
        assumptions::{SignSet, assumption},
    },
    term::Term,
};

/// How [`sign_set`] decides signs.
#[derive(Clone, Copy, Debug)]
pub(crate) struct SignMode {
    /// Approximate constants whose sign isn't found from their structure, like `{$pi - 3$}`.
    approximate: bool,
    /// Symbols without sign assumption are non-zero, a generic value of a parameter.
    generic_nonzero: bool,
}

impl SignMode {
    /// Only from the structure and the assumptions, cheap enough for normalization.
    pub(crate) const STRUCTURAL: Self = Self {
        approximate: false,
        generic_nonzero: false,
    };
    /// Also approximating constants.
    pub(crate) const APPROXIMATE: Self = Self {
        approximate: true,
        generic_nonzero: false,
    };
    /// Also approximating constants, and parameters are non-zero unless assumed otherwise.
    pub(crate) const GENERIC: Self = Self {
        approximate: true,
        generic_nonzero: true,
    };
}

/// The possible signs of `term`.
pub(crate) fn sign_set(term: &Expr, mode: SignMode) -> SignSet {
    let res = structural_sign(term, mode);
    if res.strict().is_none()
        && mode.approximate
        && !matches!(term, Term::Value(_))
        && term
            .symbols()
            .iter()
            .all(|symbol| Context::is_builtin_constant(*symbol))
        && let Some(value) = approximate(term, DIGITS)
    {
        return SignSet::from_ordering(value.sign());
    }
    res
}

/// The sign of `term` when it is known, see [`sign_set`].
pub(crate) fn sign(term: &Expr, mode: SignMode) -> Option<std::cmp::Ordering> {
    sign_set(term, mode).strict()
}

fn structural_sign(term: &Expr, mode: SignMode) -> SignSet {
    match term {
        Term::Value(value) => SignSet::from_ordering(value.value.sign()),
        Term::Symbol(symbol) => match symbol.symbol {
            Context::PI | Context::E | Context::OO | Context::EULER_GAMMA => SignSet::POSITIVE,
            Context::UNDEFINED => SignSet::ANY,
            symbol => {
                let sign = assumption(symbol).sign;
                if mode.generic_nonzero && !sign.is_subset(SignSet::ZERO) {
                    sign.intersect(SignSet::NONZERO)
                } else {
                    sign
                }
            }
        },
        Term::Add(add) => {
            let mut res = SignSet::ZERO;
            for t in add.iter() {
                res = res.add(structural_sign(t, mode));
                if res == SignSet::ANY {
                    break;
                }
            }
            res
        }
        Term::Mul(mul) => mul.iter().fold(
            SignSet::from_ordering(mul.coefficient.sign()),
            |res, factor| res.mul(structural_sign(factor, mode)),
        ),
        Term::Pow(pow) => {
            let base = structural_sign(&pow.base, mode);
            match &**pow.exponant {
                Term::Value(exponant) => {
                    let (num, den) = exponant.value.numerator_and_denominator_ref();
                    let negative = exponant.value < 0;
                    if den.even() {
                        // An even root, defined for a non-negative base
                        if negative || base.is_subset(SignSet::POSITIVE) {
                            SignSet::POSITIVE
                        } else if base == SignSet::ZERO {
                            SignSet::ZERO
                        } else {
                            SignSet::NONNEGATIVE
                        }
                    } else if num.even() {
                        if base == SignSet::ZERO {
                            SignSet::ZERO
                        } else if negative || base.is_subset(SignSet::NONZERO) {
                            SignSet::POSITIVE
                        } else {
                            SignSet::NONNEGATIVE
                        }
                    } else if negative && base != SignSet::ZERO {
                        // `{$u^(-n)$}` has the sign of `u`, which isn't zero
                        base.intersect(SignSet::NONZERO)
                    } else {
                        base
                    }
                }
                _ if base.is_subset(SignSet::POSITIVE) => SignSet::POSITIVE,
                _ => SignSet::ANY,
            }
        }
        Term::Fun(_) => {
            let Some((ident, arg)) = unary(term) else {
                return SignSet::ANY;
            };
            match ident {
                Context::EXP | Context::COSH => SignSet::POSITIVE,
                Context::ABS => {
                    let arg = structural_sign(arg, mode);
                    if arg == SignSet::ZERO {
                        SignSet::ZERO
                    } else if arg.is_subset(SignSet::NONZERO) {
                        SignSet::POSITIVE
                    } else {
                        SignSet::NONNEGATIVE
                    }
                }
                // Odd increasing functions, with the sign of their argument
                Context::SIGN
                | Context::SINH
                | Context::TANH
                | Context::ASINH
                | Context::ATANH
                | Context::ATAN
                | Context::ASIN
                | Context::ERF
                | Context::ERFI
                | Context::LAMBERTW => structural_sign(arg, mode),
                Context::ACOS | Context::ACOSH => SignSet::NONNEGATIVE,
                // `{$Gamma(u) > 0$}` for `{$u > 0$}`, `{$u! > 0$}` for `{$u >= 0$}`
                Context::GAMMA if structural_sign(arg, mode).is_subset(SignSet::POSITIVE) => {
                    SignSet::POSITIVE
                }
                Context::FACTORIAL
                    if structural_sign(arg, mode).is_subset(SignSet::NONNEGATIVE) =>
                {
                    SignSet::POSITIVE
                }
                // `{$zeta(s) > 0$}` for `{$s > 1$}`
                Context::ZETA if matches!(arg, Term::Value(s) if s.value > 1) => SignSet::POSITIVE,
                // `{$ln u$}` has the sign of `{$u - 1$}`, only checked on constants
                Context::LN if mode.approximate => {
                    structural_sign(&(arg - &super::expr::one()), mode)
                }
                _ => SignSet::ANY,
            }
        }
    }
}

/// Whether `term` is an integer: an integer value, a symbol assumed to be an integer, or a sum, product or
/// non-negative integer power of integers, or `floor` / `ceil` of a real.
pub(crate) fn is_integer(term: &Expr) -> bool {
    match term {
        Term::Value(value) => value.value.denominator_ref() == &1u32,
        Term::Symbol(symbol) => assumption(symbol.symbol).integer,
        Term::Add(add) => add.iter().all(is_integer),
        Term::Mul(mul) => mul.coefficient.denominator_ref() == &1u32 && mul.iter().all(is_integer),
        Term::Pow(pow) => {
            is_integer(&pow.base)
                && matches!(&**pow.exponant, Term::Value(e) if e.value >= 0 && e.value.denominator_ref() == &1u32)
        }
        Term::Fun(fun) => {
            matches!(fun.get_ident(), Context::FLOOR | Context::CEIL)
                && fun.get_args::<Real>().is_some()
        }
    }
}
