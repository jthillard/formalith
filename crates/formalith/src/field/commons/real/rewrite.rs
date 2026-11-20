//! Rewrites done by the builtins `expand` and `simplify` in `{$RR$}`, on top of the expansion and simplification
//! of any ring. Internal expansions and simplifications (in limits, integrals or solving) don't do them.

use malachite::Rational;

use super::{
    R,
    expr::{Expr, exp_of_ln, fun, hyperbolic_as_exp, map_tree, one, size, unary, value},
};
use crate::{
    context::Context,
    term::{Expand, Term},
};

/// Largest integer `k` for which `{$sin(k u)$}` and `{$cos(k u)$}` are expanded by `simplify`.
const MAX_MULTIPLE_ANGLE: i64 = 6;

/// `expand(u)`: the addition formulas of `sin` and `cos` on arguments that are sums, then the expansion.
pub(super) fn expand(u: &Expr) -> Expr {
    trigonometric_sums(u, false).expand()
}

/// `simplify(u)`: the simplification of `u`, or of `u` rewritten with `{$exp(c ln u) = u^c$}`, integer quotients of
/// logarithms, hyperbolic functions as exponentials, trigonometric functions of sums and multiple angles, and
/// even powers of `sin` with `cos`, whichever is smaller.
pub(super) fn simplify(u: &Expr) -> Expr {
    profile_scope!("simplify");
    let simplified = u.simplify();
    let candidate = exp_of_ln(u);
    let candidate = logarithm_quotients(&candidate);
    let candidate = hyperbolic_free(&candidate);
    let candidate = trigonometric_sums(&candidate, true);
    let candidate = even_powers_of_sin(&candidate).simplify();
    if size(&candidate) < size(&simplified) {
        candidate
    } else {
        simplified
    }
}

/// `term` with its hyperbolic functions written with exponentials.
fn hyperbolic_free(term: &Expr) -> Expr {
    map_tree(term, &|t| {
        let (ident, arg) = unary(t)?;
        hyperbolic_as_exp(ident, &hyperbolic_free(arg))
    })
}

/// Rewrite `{$sin(a + b)$}` and `{$cos(a + b)$}` with the addition formulas, and with `multiple_angles`,
/// `{$sin(k u)$}` and `{$cos(k u)$}` for small integers `k`.
fn trigonometric_sums(term: &Expr, multiple_angles: bool) -> Expr {
    map_tree(term, &|t| match unary(t) {
        Some((ident @ (Context::SIN | Context::COS), arg)) => {
            let (sin, cos) = sin_cos(arg, multiple_angles);
            Some(if ident == Context::SIN { sin } else { cos })
        }
        _ => None,
    })
}

/// `{$(sin u, cos u)$}`, expanded when `u` is a sum (or a multiple, see [`trigonometric_sums`]).
fn sin_cos(u: &Expr, multiple_angles: bool) -> (Expr, Expr) {
    // `{$u = a + b$}`
    let split = match u {
        Term::Add(add) => {
            let mut terms = add.iter();
            terms
                .next()
                .map(|a| (a.clone(), terms.fold(Term::zero(R), |res, t| res + t)))
        }
        Term::Mul(mul) if multiple_angles => {
            let k = i64::try_from(&mul.coefficient)
                .ok()
                .filter(|k| (2..=MAX_MULTIPLE_ANGLE).contains(k));
            k.map(|k| {
                let a = mul.iter().fold(one(), |res, f| res * f);
                (a.clone(), value(Rational::from(k - 1)) * a)
            })
        }
        _ => None,
    };
    let Some((a, b)) = split else {
        let u = trigonometric_sums(u, multiple_angles);
        return (fun(Context::SIN, u.clone()), fun(Context::COS, u));
    };
    let ((sin_a, cos_a), (sin_b, cos_b)) =
        (sin_cos(&a, multiple_angles), sin_cos(&b, multiple_angles));
    (
        &sin_a * &cos_b + &cos_a * &sin_b,
        cos_a * cos_b - sin_a * sin_b,
    )
}

/// Rewrite `{$ln(a) / ln(b) = k$}` when `{$a = b^k$}` for rationals `a` and `b`.
fn logarithm_quotients(term: &Expr) -> Expr {
    let log_of_value = |t: &Expr| match unary(t) {
        Some((Context::LN, Term::Value(a))) => Some(a.value.clone()),
        _ => None,
    };
    map_tree(term, &|t| {
        let Term::Mul(mul) = t else { return None };
        let factors: Vec<_> = mul.iter().map(logarithm_quotients).collect();
        let numerator = factors.iter().position(|f| log_of_value(f).is_some())?;
        let (denominator, k) = factors.iter().enumerate().find_map(|(i, f)| {
            let Term::Pow(pow) = f else { return None };
            if pow.exponant.to_i64() != Some(-1) {
                return None;
            }
            let b = log_of_value(&pow.base)?;
            R::integer_log(&log_of_value(&factors[numerator])?, &b).map(|k| (i, k))
        })?;
        Some(
            factors
                .iter()
                .enumerate()
                .filter(|(i, _)| *i != numerator && *i != denominator)
                .fold(
                    value(mul.coefficient.clone() * Rational::from(k)),
                    |res, (_, f)| res * f,
                ),
        )
    })
}

/// Rewrite `{$sin(u)^(2 n) = (1 - cos(u)^2)^n$}`.
fn even_powers_of_sin(term: &Expr) -> Expr {
    map_tree(term, &|t| {
        let Term::Pow(pow) = t else { return None };
        let n = pow.exponant.to_i64().filter(|n| *n > 0 && n % 2 == 0)?;
        let (Context::SIN, u) = unary(&pow.base)? else {
            return None;
        };
        let u = even_powers_of_sin(u);
        let cos = fun(Context::COS, u);
        Some((one() - &cos * &cos).pow(&value(Rational::from(n / 2))))
    })
}
