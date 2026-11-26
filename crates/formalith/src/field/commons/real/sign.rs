//! Signs of real expressions, from their structure, the assumptions on their symbols (see
//! [`assumptions`](crate::context::assumptions)) and numerical approximations of constants.

use malachite::{
    Rational,
    base::num::{
        arithmetic::traits::{Parity, Sign},
        basic::traits::{One, Zero},
    },
};

use super::{
    approx::approximate,
    expr::{DIGITS, Expr, Real, unary},
};
use crate::{
    context::{
        Context, Symbol,
        assumptions::{
            SignSet, assumption, is_relational,
            linear::{Constraint, LinearForm, Var},
            linear_signs,
        },
    },
    term::Term,
};

/// How [`sign_set`] decides signs.
#[derive(Clone, Copy, Debug)]
pub struct SignMode {
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
pub fn sign_set(term: &Expr, mode: SignMode) -> SignSet {
    let res = structural_sign(term, mode);
    if res.strict().is_none()
        && mode.approximate
        && !matches!(term, Term::Value(_))
        && term
            .symbols()
            .iter()
            .all(|symbol| Context::is_builtin_constant(*symbol))
        && let Some(value) = approximate(term, DIGITS)
        // Indistinguishable from zero at the maximum precision, like `{$sin(10^(-2000))$}`: zero is only known
        // structurally
        && value != 0
    {
        return SignSet::from_ordering(value.sign());
    }
    res
}

/// The sign of `term` when it is known, see [`sign_set`].
pub fn sign(term: &Expr, mode: SignMode) -> Option<std::cmp::Ordering> {
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
                if sign.strict().is_none() {
                    super::cases::record(symbol, Rational::ZERO);
                }
                if mode.generic_nonzero && !sign.is_subset(SignSet::ZERO) {
                    sign.intersect(SignSet::NONZERO)
                } else {
                    sign
                }
            }
        },
        Term::Add(add) => {
            let form = linear_form(term);
            if let Some(res) = form.as_ref().and_then(single_symbol_sign) {
                return res;
            }
            let res = sum_sign(add, mode);
            // A relation between several symbols, like `{$x - r_1$}`, for case splits
            if res.strict().is_none()
                && let Some(form) = form
            {
                super::cases::record_form(&form);
            }
            res
        }
        Term::Mul(mul) => mul.iter().fold(
            SignSet::from_ordering(mul.coefficient.sign()),
            |res, factor| res * structural_sign(factor, mode),
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
        Term::Fun(fun) if fun.get_ident() == Context::real_root() => fun
            .get_args::<Real>()
            .and_then(|args| super::rootof::sign(args))
            .map_or(SignSet::NONZERO, SignSet::from_ordering),
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
                | Context::LAMBERTW
                // Not increasing, but `{$"Si"(x) > 0$}` for `{$x > 0$}`
                | Context::SI => structural_sign(arg, mode),
                Context::ACOS | Context::ACOSH => SignSet::NONNEGATIVE,
                // `{$Gamma(u) > 0$}` for `{$u > 0$}`, `{$u! > 0$}` for `{$u >= 0$}`
                Context::GAMMA if structural_sign(arg, mode).is_subset(SignSet::POSITIVE) => {
                    SignSet::POSITIVE
                }
                // `{$W_(-1)(u) <= -1$}`
                ident if ident == Context::lambertw_m1() => SignSet::NEGATIVE,
                Context::FACTORIAL
                    if structural_sign(arg, mode).is_subset(SignSet::NONNEGATIVE) =>
                {
                    SignSet::POSITIVE
                }
                // `{$zeta(s) > 0$}` for `{$s > 1$}`
                Context::ZETA if matches!(arg, Term::Value(s) if s.value > 1) => SignSet::POSITIVE,
                // `{$ln u$}` has the sign of `{$u - 1$}` for `{$u > 0$}`, from the assumptions when `u` is linear in
                // symbols with relations, otherwise only checked on constants
                Context::LN if structural_sign(arg, mode).is_subset(SignSet::POSITIVE) => {
                    if let Some(res) = linear_form(arg).and_then(|form| {
                        single_symbol_sign(&form.add(&LinearForm::constant(-Rational::ONE)))
                    }) {
                        return res;
                    }
                    let terms: Vec<&Expr> = match arg {
                        Term::Add(add) => add.iter().collect(),
                        arg => vec![arg],
                    };
                    if has_relational_symbol(&terms) {
                        let signs: Vec<SignSet> =
                            terms.iter().map(|t| structural_sign(t, mode)).collect();
                        linear_sign(&terms, &signs, -Rational::ONE)
                    } else if mode.approximate {
                        structural_sign(&(arg - &super::expr::one()), mode)
                    } else {
                        SignSet::ANY
                    }
                }
                _ => SignSet::ANY,
            }
        }
    }
}

/// `term` as `{$c s$}` for a symbol `s` (`None` for a value `c`), when it is one.
fn linear_term(term: &Expr) -> Option<(Option<Symbol>, Rational)> {
    let symbol = |t: &Expr| match t {
        Term::Symbol(s) if !Context::is_builtin_constant(s.symbol) => Some(s.symbol),
        _ => None,
    };
    match term {
        Term::Value(value) => Some((None, value.value.clone())),
        Term::Mul(mul) => match mul.iter().as_slice() {
            [factor] => Some((Some(symbol(factor)?), mul.coefficient.clone())),
            _ => None,
        },
        term => Some((Some(symbol(term)?), Rational::ONE)),
    }
}

/// The possible signs of a form `{$k s + c$}` in a single symbol `s` under the current assumptions, recording the
/// point `{$-c/k$}` for case splits when it isn't a single sign (see [`super::cases`]). `None` for other forms.
fn single_symbol_sign(form: &LinearForm) -> Option<SignSet> {
    let mut coefficients = form.coefficients.iter();
    let (Some((Var::Symbol(s), k)), None) = (coefficients.next(), coefficients.next()) else {
        return None;
    };
    let assumed = assumption(*s);
    let res = if assumed.sign == SignSet::ANY && !assumed.integer && !is_relational(*s) {
        SignSet::ANY
    } else {
        linear_signs(form, &[])
    };
    if res.strict().is_none() {
        super::cases::record(*s, -(&form.constant / k));
    }
    Some(res)
}

/// The possible signs of a sum from those of its terms, see [`structural_sign`].
fn sum_sign(add: &crate::term::Add<super::Real>, mode: SignMode) -> SignSet {
    let terms: Vec<&Expr> = add.iter().collect();
    if has_relational_symbol(&terms) {
        let signs: Vec<SignSet> = terms.iter().map(|t| structural_sign(t, mode)).collect();
        let res = signs.iter().fold(SignSet::ZERO, |res, s| res + *s);
        if res.strict().is_some() {
            return res;
        }
        let linear = linear_sign(&terms, &signs, Rational::ZERO).intersect(res);
        return if linear == SignSet::EMPTY {
            res
        } else {
            linear
        };
    }
    let mut res = SignSet::ZERO;
    for t in add {
        res = res + structural_sign(t, mode);
        if res == SignSet::ANY {
            break;
        }
    }
    res
}

/// Whether a term is a multiple of a symbol with conditions other than on its sign.
fn has_relational_symbol(terms: &[&Expr]) -> bool {
    terms
        .iter()
        .any(|t| matches!(linear_term(t), Some((Some(s), _)) if is_relational(s)))
}

/// The possible signs of `{$sum t_i + c$}` under the current assumptions, `t_i` having signs in `signs`: multiples of
/// symbols are variables of a linear form, other terms are variables with their sign.
fn linear_sign(terms: &[&Expr], signs: &[SignSet], c: Rational) -> SignSet {
    let mut form = LinearForm::constant(c);
    let mut extra = vec![];
    for (i, (t, sign)) in terms.iter().zip(signs).enumerate() {
        match linear_term(t) {
            Some((None, c)) => form.constant += c,
            Some((Some(s), c)) => form.add_term(Var::Symbol(s), c),
            None => {
                let atom = Var::Atom(i);
                form.add_term(atom, Rational::ONE);
                let atom = LinearForm::variable(atom);
                if sign.is_subset(SignSet::NONNEGATIVE) {
                    extra.push(Constraint::new(atom.clone(), *sign == SignSet::POSITIVE));
                }
                if sign.is_subset(SignSet::NONPOSITIVE) {
                    extra.push(Constraint::new(atom.neg(), *sign == SignSet::NEGATIVE));
                }
            }
        }
    }
    linear_signs(&form, &extra)
}

/// `term` as a linear form in its symbols with rational coefficients, `None` when it isn't one or contains a builtin
/// constant like `{$pi$}`.
pub fn linear_form(term: &Expr) -> Option<LinearForm> {
    let terms: Vec<&Expr> = match term {
        Term::Add(add) => add.iter().collect(),
        term => vec![term],
    };
    let mut res = LinearForm::default();
    for t in terms {
        match linear_term(t)? {
            (None, c) => res.constant += c,
            (Some(s), c) => res.add_term(Var::Symbol(s), c),
        }
    }
    Some(res)
}

/// The expression `{$sum c_i x_i + c$}` of a linear form in symbols, with the values of `assignments` for their
/// symbols.
pub fn linear_expr(form: &LinearForm, assignments: &[(Symbol, Expr)]) -> Expr {
    form.coefficients.iter().fold(
        super::expr::value(form.constant.clone()),
        |res, (var, c)| {
            let Var::Symbol(s) = var else { return res };
            let term = assignments
                .iter()
                .find(|(x, _)| x == s)
                .map_or_else(|| super::expr::variable(*s), |(_, value)| value.clone());
            res + super::expr::value(c.clone()) * term
        },
    )
}

/// Whether `term` is an integer: an integer value, a symbol assumed to be an integer, or a sum, product or
/// non-negative integer power of integers, or `floor` / `ceil` of a real.
pub fn is_integer(term: &Expr) -> bool {
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
