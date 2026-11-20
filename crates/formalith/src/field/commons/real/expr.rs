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

pub(crate) use super::Real;
/// A real expression.
pub(crate) type Expr = Term<Real>;

/// Significant digits of the numerical approximations deciding signs and zeros.
pub(crate) const DIGITS: u64 = 30;

/// The constant `value`.
pub(crate) fn value(value: Rational) -> Expr {
    Term::Value(Value::new(value, R))
}

/// The constant `{$p / q$}`.
pub(crate) fn ratio(p: i64, q: i64) -> Expr {
    value(Rational::from_signeds(p, q))
}

/// The constant 0.
pub(crate) fn zero() -> Expr {
    Term::zero(R)
}

/// The constant 1.
pub(crate) fn one() -> Expr {
    value(Rational::ONE)
}

/// The constant `{$1/2$}`.
pub(crate) fn half() -> Expr {
    ratio(1, 2)
}

/// The symbol `x` as an expression.
pub(crate) const fn variable(x: Symbol) -> Expr {
    Term::Symbol(SymbolTerm::new(x, R))
}

/// `{$oo$}`.
pub(crate) const fn infinity() -> Expr {
    variable(Context::OO)
}

/// The function `ident(arg)`, normalized.
pub(crate) fn fun(ident: Symbol, arg: Expr) -> Expr {
    Term::Fun(Box::new(Fun::new(ident, vec![arg], R))).normalize()
}

/// `{$sqrt(u)$}`.
pub(crate) fn sqrt(u: Expr) -> Expr {
    u.pow(&half())
}

/// The identifier and argument of a builtin function with one real argument.
pub(crate) fn unary(term: &Expr) -> Option<(Symbol, &Expr)> {
    match term {
        Term::Fun(fun) => match fun.get_args::<Real>().map(Vec::as_slice) {
            Some([arg]) => Some((fun.get_ident(), arg)),
            _ => None,
        },
        _ => None,
    }
}

/// `{$psi^((m))(u)$}`, normalized.
pub(crate) fn polygamma(m: u64, u: Expr) -> Expr {
    Term::Fun(Box::new(Fun::new(
        Context::POLYGAMMA,
        vec![value(Rational::from(m)), u],
        R,
    )))
    .normalize()
}

/// The order `m` and the argument `u` of `{$psi^((m))(u)$}`, for a natural `m`.
pub(crate) fn polygamma_args(term: &Expr) -> Option<(u64, &Expr)> {
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
pub(crate) fn gamma_pole(term: &Expr) -> Option<u64> {
    match term {
        Term::Value(v) if v.value <= 0 => u64::try_from(&-&v.value).ok(),
        _ => None,
    }
}

/// Whether `term` contains the symbol `x`.
pub(crate) fn depends(term: &Expr, x: Symbol) -> bool {
    term.symbols().contains(&x)
}

/// Whether `term` contains `{$oo$}` or `undefined`, which are only meaningful as limit points or results.
pub(crate) fn has_special_constant(term: &Expr) -> bool {
    depends(term, Context::OO) || depends(term, Context::UNDEFINED)
}

/// `Some(Greater)` for `{$oo$}`, `Some(Less)` for `{$-oo$}`, `None` otherwise.
pub(crate) fn infinity_sign(term: &Expr) -> Option<Ordering> {
    if *term == infinity() {
        Some(Ordering::Greater)
    } else if *term == -infinity() {
        Some(Ordering::Less)
    } else {
        None
    }
}

/// Whether `term` is `{$oo$}` or `{$-oo$}`.
pub(crate) fn is_infinite(term: &Expr) -> bool {
    infinity_sign(term).is_some()
}

/// The sign of a term free of the variable, from its structure and the assumptions on its symbols, or the
/// numerical approximation with [`DIGITS`] digits of a constant. `None` if it is unknown.
pub(crate) fn constant_sign(term: &Expr) -> Option<Ordering> {
    match term {
        Term::Value(value) => Some(value.value.sign()),
        _ => sign(term, SignMode::APPROXIMATE),
    }
}

/// `{$ident(u)$}` written with exponentials, for the hyperbolic functions `sinh`, `cosh` and `tanh`.
pub(crate) fn hyperbolic_as_exp(ident: Symbol, u: &Expr) -> Option<Expr> {
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
            let exp = fun(Context::EXP, value(Rational::from(2)) * u.clone());
            Some((&exp - &one()) / (exp + one()))
        }
        _ => None,
    }
}

/// Rebuild `term` from its operands mapped by `f`: the terms of a sum, the factors of a product, the base then
/// the exponant of a power, and the arguments of a function with real arguments (normalized). Values,
/// symbols and functions with other arguments are returned unchanged.
pub(crate) fn try_map_operands<E>(
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
pub(crate) fn subs(term: &Expr, x: Symbol, value: &Expr) -> Expr {
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
pub(crate) fn map_tree(term: &Expr, rewrite: &impl Fn(&Expr) -> Option<Expr>) -> Expr {
    if let Some(res) = rewrite(term) {
        return res;
    }
    let Ok(res) = try_map_operands::<Infallible>(term, |operand| Ok(map_tree(operand, rewrite)));
    res
}

/// The number of nodes of a term.
pub(crate) fn size(term: &Expr) -> usize {
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
pub(crate) fn exp_of_ln(term: &Expr) -> Expr {
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
