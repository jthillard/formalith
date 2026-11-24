//! Integrals of elementary functions of a linear argument, of square roots of quadratic polynomials, of
//! products `{$e^u sin v$}` and `{$e^u cos v$}`, and of `{$p e^q$}` for polynomials `p` and quadratic
//! polynomials `q` with the error functions `{$"erf"$}` and `{$"erfi"$}`, and of `{$1 / (A x^2 + B)$}` with
//! symbolic `A` and `B`, and of `{$e^u / v$}`, `{$sin(u) / v$}` and `{$cos(u) / v$}` for linear `u` and `v`, with the
//! exponential, sine and cosine integrals.

use crate::field::real::expr::{
    Expr, constant_sign, depends, fun, map_tree, one, ratio, unary, value, variable, zero,
};
use crate::field::real::expr::{half, sqrt};
use std::cmp::Ordering;

use malachite::Rational;

use crate::{
    context::{Context, Symbol},
    term::{Expand, Term},
};

use super::{Integrator, factors, linear, ln_abs, poly::Poly};

pub(super) fn integrate(_: &mut Integrator, f: &Expr, x: Symbol) -> Option<Expr> {
    match f {
        Term::Symbol(_) => Some(ratio(1, 2) * variable(x).pow(&value(Rational::from(2)))),
        Term::Pow(pow) => {
            let (base, exponant) = (&*pow.base, &**pow.exponant);
            if !depends(exponant, x) {
                if let Some(a) = linear(base, x) {
                    // `{$integral u^n = u^(n+1) / (n+1)$}`, `{$integral 1/u = ln|u|$}`
                    if *exponant == value(Rational::from(-1)) {
                        return Some(ln_abs(base, x) / a);
                    }
                    let n = exponant + &one();
                    return Some(base.pow(&n) / (n * a));
                }
                if *exponant == value(Rational::from(-1))
                    && let Some(res) = symbolic_atan(base, x)
                {
                    return Some(res);
                }
                return quadratic_power(base, exponant, x);
            }
            // `{$integral b^u = b^u / ln b$}`
            if !depends(base, x)
                && let Some(a) = linear(exponant, x)
            {
                return Some(f / &(a * fun(Context::LN, base.clone())));
            }
            None
        }
        Term::Fun(_) => {
            let (ident, u) = unary(f)?;
            if ident == Context::EXP
                && let Some(res) = gaussian(u, x)
            {
                return Some(res);
            }
            let a = linear(u, x)?;
            Some(elementary(ident, u)? / a)
        }
        Term::Mul(_) => exp_trig(f, x)
            .or_else(|| linear_quadratic(f, x))
            .or_else(|| polynomial_gaussian(f, x))
            .or_else(|| exponential_integral(f, x)),
        Term::Value(_) | Term::Add(_) => None,
    }
}

/// `{$integral f(u) dif u$}` for an elementary function `f`.
fn elementary(ident: Symbol, u: &Expr) -> Option<Expr> {
    let one = one();
    let f = fun(ident, u.clone());
    let u2 = u * u;
    Some(match ident {
        Context::EXP => f,
        Context::SIN => -fun(Context::COS, u.clone()),
        Context::COS => fun(Context::SIN, u.clone()),
        // `{$integral tan = -ln|cos|$}`
        Context::TAN => -fun(Context::LN, fun(Context::ABS, fun(Context::COS, u.clone()))),
        Context::SINH => fun(Context::COSH, u.clone()),
        Context::COSH => fun(Context::SINH, u.clone()),
        Context::TANH => fun(Context::LN, fun(Context::COSH, u.clone())),
        // By parts, `{$integral f = u f - integral u f'$}`
        Context::LN => u * &f - u.clone(),
        Context::ASIN => u * &f + sqrt(&(&one - &u2)),
        Context::ACOS => u * &f - sqrt(&(&one - &u2)),
        Context::ATAN => u * &f - half() * fun(Context::LN, &one + &u2),
        Context::ASINH => u * &f - sqrt(&(&u2 + &one)),
        Context::ACOSH => u * &f - sqrt(&(&u2 - &one)),
        Context::ATANH => u * &f + half() * fun(Context::LN, &one - &u2),
        Context::ABS => half() * u * f,
        Context::SIGN => fun(Context::ABS, u.clone()),
        // By parts, `{$integral "erf" = u "erf" u + e^(-u^2) / sqrt(pi)$}`
        Context::ERF => u * &f + fun(Context::EXP, -u2) / sqrt(&variable(Context::PI)),
        Context::ERFI => u * &f - fun(Context::EXP, u2) / sqrt(&variable(Context::PI)),
        // By parts, `{$integral "Si" = u "Si" u + cos u$}`, with the derivatives `{$sin(u)/u$}`, `{$cos(u)/u$}`, `{$e^u/u$}`
        Context::SI => u * &f + fun(Context::COS, u.clone()),
        Context::CI => u * &f - fun(Context::SIN, u.clone()),
        Context::EI => u * &f - fun(Context::EXP, u.clone()),
        _ => return None,
    })
}

/// `{$integral e^u sin v$}` and `{$integral e^u cos v$}` for linear `u` and `v`.
fn exp_trig(f: &Expr, x: Symbol) -> Option<Expr> {
    let [first, second] = factors(f).try_into().ok()?;
    let ((exp @ (Context::EXP, _), trig) | (trig, exp @ (Context::EXP, _))) =
        (unary(&first)?, unary(&second)?)
    else {
        return None;
    };
    let (u, (ident, v)) = (exp.1, trig);
    let (a, b) = (linear(u, x)?, linear(v, x)?);
    let exp = fun(Context::EXP, u.clone());
    let (sin, cos) = (fun(Context::SIN, v.clone()), fun(Context::COS, v.clone()));
    let norm = &a * &a + &b * &b;
    Some(match ident {
        Context::SIN => exp * (&a * &sin - &b * &cos) / norm,
        Context::COS => exp * (a * cos + b * sin) / norm,
        _ => return None,
    })
}

/// `{$integral g(a x + b) / (p x + q)$}` for `{$g = exp$}`, `sin` or `cos`, with the exponential, sine and cosine
/// integrals: with `{$t = p x + q$}`, `{$a x + b = alpha t + beta$}`, `{$integral e^(alpha t + beta) / t = e^beta "Ei"(alpha t)$}`,
/// `{$integral sin(alpha t + beta) / t = cos(beta) "Si"(alpha t) + sin(beta) "Ci"(alpha t)$}` and
/// `{$integral cos(alpha t + beta) / t = cos(beta) "Ci"(alpha t) - sin(beta) "Si"(alpha t)$}`.
fn exponential_integral(f: &Expr, x: Symbol) -> Option<Expr> {
    let [first, second] = factors(f).try_into().ok()?;
    let ((ident, u), t) = match (&first, &second) {
        (Term::Pow(pow), g) | (g, Term::Pow(pow))
            if **pow.exponant == value(Rational::from(-1)) =>
        {
            (unary(g)?, &*pow.base)
        }
        _ => return None,
    };
    if !matches!(ident, Context::EXP | Context::SIN | Context::COS) {
        return None;
    }
    let (a, p) = (linear(u, x)?, linear(t, x)?);
    let alpha = &a / &p;
    let beta = u - &(&alpha * t);
    if depends(&beta, x) {
        return None;
    }
    let scaled = (&alpha * t).expand();
    let (si, ci) = (
        fun(Context::SI, scaled.clone()),
        fun(Context::CI, scaled.clone()),
    );
    let (cos, sin) = (
        fun(Context::COS, beta.clone()),
        fun(Context::SIN, beta.clone()),
    );
    Some(
        match ident {
            Context::EXP => fun(Context::EXP, beta) * fun(Context::EI, scaled),
            Context::SIN => cos * si + sin * ci,
            _ => cos * ci - sin * si,
        } / p,
    )
}

/// A quadratic polynomial `{$c_2 x^2 + c_1 x + c_0$}` written `{$c_2 (x + h)^2 + k$}`, as `{$(c_2, h, k)$}`.
pub(super) fn quadratic(q: &Expr, x: Symbol) -> Option<(Rational, Rational, Rational)> {
    let p = Poly::from_term(q, x)?;
    if p.degree() != 2 {
        return None;
    }
    let [c0, c1, c2] = p.coefficients() else {
        return None;
    };
    let h = c1 / (Rational::from(2) * c2);
    let k = c0 - c1 * c1 / (Rational::from(4) * c2);
    Some((c2.clone(), h, k))
}

/// `{$integral e^q$}` for a quadratic polynomial `{$q = c (x + h)^2 + k$}`:
/// `{$e^k sqrt(pi) / (2 sqrt(-c)) "erf"(sqrt(-c) (x + h))$}` for `{$c < 0$}`, and the same with `{$"erfi"$}` and
/// `{$sqrt(c)$}` for `{$c > 0$}`.
fn gaussian(q: &Expr, x: Symbol) -> Option<Expr> {
    let (c, h, k) = quadratic(q, x)?;
    let (ident, c) = if c < 0 {
        (Context::ERF, -c)
    } else {
        (Context::ERFI, c)
    };
    let sqrt_c = sqrt(&value(c));
    let erf = fun(ident, &sqrt_c * &(variable(x) + value(h)));
    Some(fun(Context::EXP, value(k)) * sqrt(&variable(Context::PI)) / (ratio(2, 1) * sqrt_c) * erf)
}

/// `{$integral p e^q$}` for a polynomial `p` and a quadratic polynomial `q`: dividing `p` by `{$q'$}`,
/// `{$p = a q' + r$}` with a constant `r`, `{$integral a q' e^q = a e^q - integral a' e^q$}`, so the degree of the
/// remaining polynomial decreases until only `{$r integral e^q$}` is left.
fn polynomial_gaussian(f: &Expr, x: Symbol) -> Option<Expr> {
    // Products of exponentials `{$e^u e^v = e^(u + v)$}` and their powers are merged
    let mut q = zero();
    let mut rest = one();
    for factor in factors(f) {
        let (base, n) = match &factor {
            Term::Pow(pow) if pow.exponant.to_i64().is_some() => {
                (&*pow.base, (**pow.exponant).clone())
            }
            _ => (&factor, one()),
        };
        match unary(base) {
            Some((Context::EXP, u)) => q += n * u,
            _ => rest *= &factor,
        }
    }
    quadratic(&q, x)?;
    let mut p = Poly::from_term(&rest, x)?;
    let dq = Poly::from_term(&q, x)?.derivative();
    let mut part = Poly::zero();
    let mut constant = Rational::from(0);
    while !p.is_zero() {
        if p.degree() == 0 {
            constant = p.coefficient(0);
            break;
        }
        let (a, r) = p.div_rem(&dq);
        p = r.sub(&a.derivative());
        part = part.add(&a);
    }
    Some(part.to_term(x) * fun(Context::EXP, q.clone()) + value(constant) * gaussian(&q, x)?)
}

/// `{$integral 1 / (A x^2 + B) = atan(x / s) / (A s)$}` with `{$s = sqrt(B / A)$}`, for `A` and `B` free of `x` and
/// not both values (those are rational functions). Absolute values are dropped from `s`, `atan` being odd, and `s`
/// must not have roots left (like `{$sqrt(2/a)$}`, which may be the root of a negative number).
fn symbolic_atan(q: &Expr, x: Symbol) -> Option<Expr> {
    let Term::Add(add) = q else { return None };
    let square = variable(x).pow(&value(Rational::from(2)));
    let (mut a, mut b) = (zero(), zero());
    for term in add {
        if depends(term, x) {
            a += term / &square;
        } else {
            b += term;
        }
    }
    if depends(&a, x) || a.is_zero() || b.is_zero() {
        return None;
    }
    if matches!((&a, &b), (Term::Value(_), Term::Value(_))) {
        return None;
    }
    let s = map_tree(&sqrt(&(&b / &a)), &|t| match unary(t) {
        Some((Context::ABS, u)) => Some(u.clone()),
        _ => None,
    });
    if has_root(&s) {
        return None;
    }
    Some(fun(Context::ATAN, variable(x) / &s) / (a * s))
}

/// Whether `term` contains a power with a non-integer exponent.
fn has_root(term: &Expr) -> bool {
    match term {
        Term::Value(_) | Term::Symbol(_) => false,
        Term::Add(add) => add.iter().any(has_root),
        Term::Mul(mul) => mul.iter().any(has_root),
        Term::Pow(pow) => pow.exponant.to_i64().is_none() || has_root(&pow.base),
        Term::Fun(_) => unary(term).is_some_and(|(_, u)| has_root(u)),
    }
}

/// `{$integral q^e$}` for a quadratic polynomial `q` and `{$e in {1/2, -1/2, -3/2}$}`, completing the square.
fn quadratic_power(q: &Expr, e: &Expr, x: Symbol) -> Option<Expr> {
    let (c2, h, k) = quadratic(q, x)?;
    let t = variable(x) + value(h);
    let sqrt_q = sqrt(q);
    let (c2_sign, k_sign) = (
        constant_sign(&value(c2.clone()))?,
        constant_sign(&value(k.clone()))?,
    );
    let sqrt = |v: Rational| sqrt(&value(v));
    if *e == ratio(-1, 2) {
        return match (c2_sign, k_sign) {
            // `{$integral 1 / sqrt(c_2 t^2 + k) = "asinh"(t sqrt(c_2 / k)) / sqrt(c_2)$}`
            (Ordering::Greater, Ordering::Greater) => {
                Some(fun(Context::ASINH, t * sqrt(&c2 / &k)) / sqrt(c2))
            }
            // `{$ln|sqrt(c_2) t + sqrt(q)| / sqrt(c_2)$}`
            (Ordering::Greater, Ordering::Less) => {
                let s = sqrt(c2);
                Some(fun(Context::LN, fun(Context::ABS, &s * &t + sqrt_q)) / s)
            }
            // `{$arcsin(t sqrt(-c_2 / k)) / sqrt(-c_2)$}`
            (Ordering::Less, Ordering::Greater) => {
                Some(fun(Context::ASIN, t * sqrt(-&c2 / &k)) / sqrt(-c2))
            }
            _ => None,
        };
    }
    if k_sign == Ordering::Equal {
        return None;
    }
    if *e == ratio(1, 2) {
        // `{$integral sqrt(q) = t sqrt(q) / 2 + k / 2 integral 1 / sqrt(q)$}`
        let inverse = quadratic_power(q, &ratio(-1, 2), x)?;
        return Some(ratio(1, 2) * t * sqrt_q + value(k / Rational::from(2)) * inverse);
    }
    if *e == ratio(-3, 2) {
        // `{$integral q^(-3/2) = t / (k sqrt(q))$}`
        return Some(t / (value(k) * sqrt_q));
    }
    None
}

/// `{$integral (alpha x + beta) q^e$}` for a quadratic polynomial `q`, writing
/// `{$alpha x + beta = alpha / (2 c_2) q' + beta - alpha h$}`.
fn linear_quadratic(f: &Expr, x: Symbol) -> Option<Expr> {
    let [first, second] = factors(f).try_into().ok()?;
    let (p, (q, e)) = match (&first, &second) {
        (p, Term::Pow(pow)) | (Term::Pow(pow), p) if quadratic(&pow.base, x).is_some() => {
            (p, (&*pow.base, &**pow.exponant))
        }
        _ => return None,
    };
    let p = Poly::from_term(p, x)?;
    if p.degree() != 1 || depends(e, x) || *e == ratio(-1, 1) {
        return None;
    }
    let (c2, h, _) = quadratic(q, x)?;
    let [beta, alpha] = p.coefficients() else {
        return None;
    };
    let n = e + &one();
    let derivative_part = value(alpha / (Rational::from(2) * c2)) * q.pow(&n) / n;
    let rest = value(beta - alpha * h);
    if rest.is_zero() {
        return Some(derivative_part);
    }
    Some(derivative_part + rest * quadratic_power(q, e, x)?)
}
