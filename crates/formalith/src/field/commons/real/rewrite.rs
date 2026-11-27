//! Rewrites done by the builtins `expand` and `simplify` in `{$RR$}`, on top of the expansion and simplification
//! of any ring. Internal expansions and simplifications (in limits, integrals or solving) don't do them.

use malachite::Rational;

use super::{
    R,
    expr::{
        Expr, exp_of_ln, fun, has_function, hyperbolic_as_exp, map_tree, one, size, unary, value,
    },
};
use crate::{
    context::Context,
    term::{Expand, Term},
};

/// Largest integer `k` for which `{$sin(k u)$}` and `{$cos(k u)$}` are expanded by `simplify`.
const MAX_MULTIPLE_ANGLE: i64 = 6;
/// Largest number of `sin` and `cos` factors (with multiplicity) of a product written as a sum by `simplify`.
const MAX_LINEARIZED_FACTORS: usize = 8;

/// `expand(u)`: the addition formulas of `sin` and `cos` on arguments that are sums, then the expansion.
pub(super) fn expand(u: &Expr) -> Expr {
    trigonometric_sums(u, false).expand()
}

/// `simplify(u)`: the simplification of `u`, or of `u` rewritten with `{$exp(c ln u) = u^c$}`, integer quotients of
/// logarithms, hyperbolic functions as exponentials, trigonometric functions of sums and multiple angles, and
/// even powers of `sin` with `cos`, or the expansion of `u` with its products of `sin` and `cos` written as sums,
/// whichever is smaller.
pub(super) fn simplify(u: &Expr) -> Expr {
    profile_scope!("simplify");
    let simplified = u.simplify();
    let candidate = exp_of_ln(u);
    let candidate = logarithm_quotients(&candidate);
    let candidate = hyperbolic_free(&candidate);
    let candidate = trigonometric_sums(&candidate, true);
    let candidate = even_powers_of_sin(&candidate).simplify();
    let mut res = if size(&candidate) < size(&simplified) {
        candidate
    } else {
        simplified
    };
    let linearized = products_to_sums(u);
    if linearized != *u {
        let linearized = linearized.expand();
        if size(&linearized) < size(&res) {
            res = linearized;
        }
    }
    res
}

/// Whether `term` is proven zero by trigonometric identities: its products of `sin` and `cos` written as sums,
/// then expanded, give 0 (`{$sin(2 u) - 2 sin u cos u$}`). A proof, since these rewrites are identities.
pub(super) fn is_trigonometric_zero(term: &Expr) -> bool {
    if !has_function(term, &[Context::SIN, Context::COS]) {
        return false;
    }
    let linearized = products_to_sums(term);
    linearized != *term && linearized.expand().is_zero()
}

/// Rewrite the products and powers of `sin` and `cos` as sums, `{$sin a cos b = (sin(a + b) + sin(a - b))/2$}`,
/// `{$cos a cos b = (cos(a - b) + cos(a + b))/2$}`, `{$sin a sin b = (cos(a - b) - cos(a + b))/2$}`, so that
/// `{$cos(2 x) cos(3 x) + sin(2 x) sin(3 x) = cos x$}` and `{$cos(x)^3 = (3 cos x + cos(3 x))/4$}` once expanded.
fn products_to_sums(term: &Expr) -> Expr {
    map_tree(term, &|t| {
        let mut factors = vec![];
        let mut rest = one();
        match t {
            Term::Mul(mul) => {
                rest = value(mul.coefficient.clone());
                for factor in mul {
                    if !trigonometric_factor(factor, &mut factors) {
                        rest *= &products_to_sums(factor);
                    }
                }
            }
            Term::Pow(_) => {
                if !trigonometric_factor(t, &mut factors) {
                    return None;
                }
            }
            _ => return None,
        }
        if factors.len() < 2 || factors.len() > MAX_LINEARIZED_FACTORS {
            return None;
        }
        // The product as a sum of `{$c f(a)$}`
        let half = Rational::from_signeds(1, 2);
        let mut sum = vec![(Rational::from(1), factors[0].0, factors[0].1.clone())];
        for (g, b) in &factors[1..] {
            let mut next = vec![];
            for (c, f, a) in sum {
                let c = c * &half;
                let (plus, minus) = (&a + b, &a - b);
                next.extend(match (f, *g) {
                    (Context::SIN, Context::SIN) => {
                        [(c.clone(), Context::COS, minus), (-c, Context::COS, plus)]
                    }
                    (Context::COS, Context::COS) => {
                        [(c.clone(), Context::COS, minus), (c, Context::COS, plus)]
                    }
                    (Context::SIN, _) => {
                        [(c.clone(), Context::SIN, plus), (c, Context::SIN, minus)]
                    }
                    // `{$cos a sin b = (sin(a + b) - sin(a - b))/2$}`
                    _ => [(c.clone(), Context::SIN, plus), (-c, Context::SIN, minus)],
                });
            }
            sum = next;
        }
        Some(
            rest * sum
                .into_iter()
                .fold(Term::zero(R), |res, (c, f, a)| res + value(c) * fun(f, a)),
        )
    })
}

/// Push `factor` to `factors` as `{$(f, a)$}` repeated `n` times when it is `{$f(a)^n$}` for `f` being `sin` or
/// `cos` and a positive integer `n`, its argument linearized. Whether it was one.
fn trigonometric_factor(factor: &Expr, factors: &mut Vec<(crate::context::Symbol, Expr)>) -> bool {
    let (base, n) = match factor {
        Term::Pow(pow) => (&*pow.base, pow.exponant.to_i64().filter(|n| *n > 0)),
        _ => (factor, Some(1)),
    };
    match (unary(base), n.and_then(|n| usize::try_from(n).ok())) {
        (Some((ident @ (Context::SIN | Context::COS), arg)), Some(n))
            if n <= MAX_LINEARIZED_FACTORS =>
        {
            factors.extend(std::iter::repeat_n((ident, products_to_sums(arg)), n));
            true
        }
        _ => false,
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
