//! Shorthands to build and inspect real expressions, shared by limits, series and integrals.

use std::{cmp::Ordering, convert::Infallible};

use malachite::{
    Rational,
    base::num::{arithmetic::traits::Sign, basic::traits::One},
};

use super::{
    R,
    sign::{SignMode, sign},
};
use crate::{
    context::{Context, Symbol},
    term::{Fun, Normalize, SymbolTerm, Term, Value},
};

pub use super::Real;
/// A real expression.
pub type Expr = Term<Real>;

/// Significant digits of the numerical approximations deciding signs and zeros.
pub const DIGITS: u64 = 30;

/// The constant `value`.
pub const fn value(value: Rational) -> Expr {
    Term::Value(Value::new(value, R))
}

/// The constant `{$p / q$}`.
pub fn ratio(p: i64, q: i64) -> Expr {
    value(Rational::from_signeds(p, q))
}

/// The constant 0.
pub fn zero() -> Expr {
    Term::zero(R)
}

/// The integer `n`.
pub fn int(n: i64) -> Expr {
    value(Rational::from(n))
}

/// The constant 1.
pub const fn one() -> Expr {
    value(Rational::ONE)
}

/// The constant `{$1/2$}`.
pub fn half() -> Expr {
    ratio(1, 2)
}

/// The symbol `x` as an expression.
pub const fn variable(x: Symbol) -> Expr {
    Term::Symbol(SymbolTerm::new(x, R))
}

/// `{$oo$}`.
pub const fn infinity() -> Expr {
    variable(Context::OO)
}

/// The function `ident(arg)`, normalized.
pub fn fun(ident: Symbol, arg: Expr) -> Expr {
    Term::Fun(Box::new(Fun::new(ident, vec![arg], R))).normalize()
}

/// `{$sqrt(u)$}`.
pub fn sqrt(u: &Expr) -> Expr {
    u.pow(&half())
}

/// The argument of `{$u + i v$}` in `{$(-pi, pi]$}`, `{$"undefined"$}` at 0, by the signs of `u` and `v`. `None` when
/// a sign is unknown.
pub fn arg(u: &Expr, v: &Expr) -> Option<Expr> {
    let sign_of = |t: &Expr| {
        if t.is_zero() {
            Some(Ordering::Equal)
        } else {
            sign(t, SignMode::APPROXIMATE)
        }
    };
    let pi = variable(Context::PI);
    let Some(su) = sign_of(u) else {
        // `{$arg(u + i v) = plus.minus pi/2 - atan(u/v)$}` for `{$v != 0$}`, whatever the sign of `u`
        let side = match sign_of(v)? {
            Ordering::Greater => 1,
            Ordering::Less => -1,
            Ordering::Equal => return None,
        };
        return Some(ratio(side, 2) * pi - fun(Context::ATAN, u / v));
    };
    // `{$arg(u + i v) = atan(v/u)$}` for `{$u > 0$}`, whatever the sign of `v`
    if su == Ordering::Greater && !v.is_zero() {
        return Some(fun(Context::ATAN, v / u));
    }
    Some(match (su, sign_of(v)?) {
        (Ordering::Equal, Ordering::Equal) => variable(Context::UNDEFINED),
        (Ordering::Greater, _) => zero(),
        (Ordering::Less, Ordering::Equal) => pi,
        (Ordering::Equal, side) => ratio(if side == Ordering::Greater { 1 } else { -1 }, 2) * pi,
        // Shifted by `{$plus.minus pi$}` for `{$u < 0$}`
        (Ordering::Less, Ordering::Greater) => fun(Context::ATAN, v / u) + pi,
        (Ordering::Less, Ordering::Less) => fun(Context::ATAN, v / u) - pi,
    })
}

/// The identifier and argument of a builtin function with one real argument.
pub fn unary(term: &Expr) -> Option<(Symbol, &Expr)> {
    match term {
        Term::Fun(fun) => match fun.get_args::<Real>().map(Vec::as_slice) {
            Some([arg]) => Some((fun.get_ident(), arg)),
            _ => None,
        },
        _ => None,
    }
}

/// `{$psi^((m))(u)$}`, normalized.
pub fn polygamma(m: u64, u: Expr) -> Expr {
    Term::Fun(Box::new(Fun::new(
        Context::POLYGAMMA,
        vec![value(Rational::from(m)), u],
        R,
    )))
    .normalize()
}

/// The order `m` and the argument `u` of `{$psi^((m))(u)$}`, for a natural `m`.
pub fn polygamma_args(term: &Expr) -> Option<(u64, &Expr)> {
    match term {
        Term::Fun(fun) if fun.get_ident() == Context::POLYGAMMA => {
            match fun.get_args::<Real>().map(Vec::as_slice) {
                Some([Term::Value(m), u]) => Some((u64::try_from(&m.value).ok()?, u)),
                _ => None,
            }
        }
        _ => None,
    }
}

/// `k` if `term` is the value `{$-k$}`, a non-positive integer, where `{$Gamma$}` and `{$psi^((m))$}` have poles.
pub fn gamma_pole(term: &Expr) -> Option<u64> {
    match term {
        Term::Value(v) if v.value <= 0 => u64::try_from(&-&v.value).ok(),
        _ => None,
    }
}

/// Whether `term` contains the symbol `x`.
pub fn depends(term: &Expr, x: Symbol) -> bool {
    term.symbols().contains(&x)
}

/// Whether `term` contains `{$oo$}` or `undefined`, which are only meaningful as limit points or results.
pub fn has_special_constant(term: &Expr) -> bool {
    if !depends(term, Context::OO) && !depends(term, Context::UNDEFINED) {
        return false;
    }
    match term {
        Term::Value(_) => false,
        Term::Symbol(_) => true,
        Term::Add(add) => add.iter().any(has_special_constant),
        Term::Mul(mul) => mul.iter().any(has_special_constant),
        Term::Pow(pow) => has_special_constant(&pow.base) || has_special_constant(&pow.exponant),
        // The upper bound `oo` of a whole series is left out
        Term::Fun(fun) => fun.get_args::<Real>().is_none_or(|args| {
            let args = if fun.get_ident() == Context::held_sum() {
                &args[..args.len().saturating_sub(1)]
            } else {
                args
            };
            args.iter().any(has_special_constant)
        }),
    }
}

/// `Some(Greater)` for `{$oo$}`, `Some(Less)` for `{$-oo$}`, `None` otherwise.
pub fn infinity_sign(term: &Expr) -> Option<Ordering> {
    if *term == infinity() {
        Some(Ordering::Greater)
    } else if *term == -infinity() {
        Some(Ordering::Less)
    } else {
        None
    }
}

/// Whether `term` is `{$oo$}` or `{$-oo$}`.
pub fn is_infinite(term: &Expr) -> bool {
    infinity_sign(term).is_some()
}

/// Whether `term` is proven zero: it normalizes or expands to 0, or is structurally zero. Faster than
/// [`is_numerically_zero`] when only a proof matters, since it never approximates.
pub fn is_proven_zero(term: &Expr) -> bool {
    let term = term.normalize();
    term.is_zero()
        || sign(&term, SignMode::STRUCTURAL) == Some(Ordering::Equal)
        || crate::term::Expand::expand(&term).is_zero()
        || super::rewrite::is_trigonometric_zero(&term)
}

/// Whether `term` is zero: `Some(true)` when it is proven zero (it normalizes or expands to 0, or is structurally
/// zero), `Some(false)` when it has a sign (from its structure, the assumptions, or for a constant an approximation
/// whose error bound excludes 0), and `None` otherwise, which must never be taken as an equality. A constant
/// indistinguishable from zero at the maximum precision of approximations isn't proven zero: `{$10^(-2000) sin(1)$}`
/// isn't.
pub fn is_numerically_zero(term: &Expr) -> Option<bool> {
    let term = term.normalize();
    if term.is_zero() {
        return Some(true);
    }
    if let Some(sign) = sign(&term, SignMode::STRUCTURAL) {
        return Some(sign == Ordering::Equal);
    }
    let constant = term
        .symbols()
        .iter()
        .all(|symbol| Context::is_builtin_constant(*symbol));
    if constant {
        // A quick approximation excluding 0, then a proof by expansion, then a precise approximation, which is slow
        // for zeros since it raises its precision to its maximum
        if super::approx::enclose(&term, 128).is_some_and(|ball| !ball.contains_zero()) {
            return Some(false);
        }
        if crate::term::Expand::expand(&term).is_zero()
            || super::rewrite::is_trigonometric_zero(&term)
        {
            return Some(true);
        }
        let approximation = super::approx::approximate(&term, DIGITS)?;
        return (approximation != 0).then_some(false);
    }
    (crate::term::Expand::expand(&term).is_zero() || super::rewrite::is_trigonometric_zero(&term))
        .then_some(true)
}

/// [`is_numerically_zero`] for a constant `term` whose approximation by [`super::approx::approximate`] is known.
pub fn zero_from_approximation(term: &Expr, approximation: &Rational) -> Option<bool> {
    if *approximation != 0 {
        return Some(false);
    }
    (crate::term::Expand::expand(term).is_zero() || super::rewrite::is_trigonometric_zero(term))
        .then_some(true)
}

/// The sign of a term free of the variable, from its structure and the assumptions on its symbols, or the
/// numerical approximation with [`DIGITS`] digits of a constant. `None` if it is unknown.
pub fn constant_sign(term: &Expr) -> Option<Ordering> {
    match term {
        Term::Value(value) => Some(value.value.sign()),
        _ => sign(term, SignMode::APPROXIMATE),
    }
}

/// `{$ident(u)$}` written with exponentials, for the hyperbolic functions `sinh`, `cosh` and `tanh`.
pub fn hyperbolic_as_exp(ident: Symbol, u: &Expr) -> Option<Expr> {
    match ident {
        Context::SINH | Context::COSH => {
            // `{$sinh u = (e^u - e^(-u))/2$}`, `{$cosh u = (e^u + e^(-u))/2$}`
            let (exp, exp_opposite) = (fun(Context::EXP, u.clone()), fun(Context::EXP, -u));
            Some(if ident == Context::SINH {
                (exp - exp_opposite) * half()
            } else {
                (exp + exp_opposite) * half()
            })
        }
        Context::TANH => {
            // `{$tanh u = (e^(2 u) - 1)/(e^(2 u) + 1)$}`
            let exp = fun(Context::EXP, int(2) * u.clone());
            Some((&exp - &one()) / (exp + one()))
        }
        _ => None,
    }
}

/// Rebuild `term` from its operands mapped by `f`: the terms of a sum, the factors of a product, the base then
/// the exponant of a power, and the arguments of a function with real arguments (normalized). Values,
/// symbols and functions with other arguments are returned unchanged.
pub fn try_map_operands<E>(
    term: &Expr,
    mut f: impl FnMut(&Expr) -> Result<Expr, E>,
) -> Result<Expr, E> {
    Ok(match term {
        Term::Value(_) | Term::Symbol(_) => term.clone(),
        Term::Add(add) => add.iter().try_fold(zero(), |res, t| Ok(res + f(t)?))?,
        Term::Mul(mul) => mul
            .iter()
            .try_fold(value(mul.coefficient.clone()), |res, t| Ok(res * f(t)?))?,
        Term::Pow(pow) => f(&pow.base)?.pow(&f(&pow.exponant)?),
        Term::Fun(function) => match function.get_args::<Real>() {
            Some(args) => Term::Fun(Box::new(Fun::new(
                function.get_ident(),
                args.iter().map(f).collect::<Result<_, _>>()?,
                R,
            )))
            .normalize(),
            None => term.clone(),
        },
    })
}

/// Replace the symbol `x` by `value` everywhere in `term`, also in exponents, normalizing the result.
pub fn subs(term: &Expr, x: Symbol, value: &Expr) -> Expr {
    match term {
        _ if !depends(term, x) => term.clone(),
        Term::Symbol(_) => value.clone(),
        _ => {
            let Ok(res) =
                try_map_operands::<Infallible>(term, |operand| Ok(subs(operand, x, value)));
            res
        }
    }
}

/// Rewrite `term` from the top: subterms for which `rewrite` gives a result are replaced, the others are rebuilt
/// from their rewritten parts.
pub fn map_tree(term: &Expr, rewrite: &impl Fn(&Expr) -> Option<Expr>) -> Expr {
    if let Some(res) = rewrite(term) {
        return res;
    }
    let Ok(res) = try_map_operands::<Infallible>(term, |operand| Ok(map_tree(operand, rewrite)));
    res
}

/// The smallest of `term` and `candidates` by [`size`], the first one among those of the same size.
pub fn smallest(term: Expr, candidates: impl IntoIterator<Item = Expr>) -> Expr {
    candidates.into_iter().fold(term, |best, candidate| {
        if size(&candidate) < size(&best) {
            candidate
        } else {
            best
        }
    })
}

/// Whether `term` or one of its subterms satisfies `predicate`.
pub fn any_subterm(term: &Expr, predicate: &impl Fn(&Expr) -> bool) -> bool {
    predicate(term)
        || match term {
            Term::Value(_) | Term::Symbol(_) => false,
            Term::Add(add) => add.iter().any(|t| any_subterm(t, predicate)),
            Term::Mul(mul) => mul.iter().any(|t| any_subterm(t, predicate)),
            Term::Pow(pow) => {
                any_subterm(&pow.base, predicate) || any_subterm(&pow.exponant, predicate)
            }
            Term::Fun(fun) => fun
                .get_args::<Real>()
                .is_some_and(|args| args.iter().any(|t| any_subterm(t, predicate))),
        }
}

/// Whether `term` contains a function among `idents`.
pub fn has_function(term: &Expr, idents: &[Symbol]) -> bool {
    any_subterm(
        term,
        &|t| matches!(t, Term::Fun(f) if idents.contains(&f.get_ident())),
    )
}

/// The number of nodes of a term.
pub fn size(term: &Expr) -> usize {
    1 + match term {
        Term::Value(_) | Term::Symbol(_) => 0,
        Term::Add(add) => add.iter().map(size).sum(),
        Term::Mul(mul) => mul.iter().map(size).sum(),
        Term::Pow(pow) => size(&pow.base) + size(&pow.exponant),
        Term::Fun(fun) => fun
            .get_args::<Real>()
            .map_or(0, |args| args.iter().map(size).sum()),
    }
}

/// Rewrite `{$exp(c ln u) = u^c$}` for a rational `c`, and `{$exp(ln u) = u$}`.
///
/// Not done by normalization, as limits and integrals build `{$exp(g ln b)$}` on purpose.
pub fn exp_of_ln(term: &Expr) -> Expr {
    map_tree(term, &|t| {
        let (Context::EXP, arg) = unary(t)? else {
            return None;
        };
        let arg = exp_of_ln(arg);
        let (c, ln) = match &arg {
            Term::Mul(mul) => match mul.iter().collect::<Vec<_>>().as_slice() {
                [ln] => (value(mul.coefficient.clone()), *ln),
                _ => return Some(fun(Context::EXP, arg.clone())),
            },
            _ => (one(), &arg),
        };
        match unary(ln) {
            Some((Context::LN, u)) => Some(u.pow(&c)),
            _ => Some(fun(Context::EXP, arg.clone())),
        }
    })
}
