//! Integrals of elementary functions of a linear argument, of square roots of quadratic polynomials, of
//! products `{$e^u sin v$}` and `{$e^u cos v$}`, and of `{$p e^q$}` for polynomials `p` and quadratic
//! polynomials `q` with the error functions `{$"erf"$}` and `{$"erfi"$}`.

use std::cmp::Ordering;

use malachite::Rational;

use crate::{
    context::{Context, Symbol},
    limit::{depends, fun, value, variable},
    term::Term,
};

use super::{Expr, Integrator, constant_sign, factors, linear, ln_abs, poly::Poly, unary};

/// `{$p / q$}` as an expression.
fn ratio(p: i64, q: i64) -> Expr {
    value(Rational::from_signeds(p, q))
}

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
                    let n = exponant + &Term::one(crate::field::real::R);
                    return Some(base.pow(&n) / (n * a));
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
            .or_else(|| polynomial_gaussian(f, x)),
        Term::Value(_) | Term::Add(_) => None,
    }
}

/// `{$integral f(u) dif u$}` for an elementary function `f`.
fn elementary(ident: Symbol, u: &Expr) -> Option<Expr> {
    let one = Term::one(crate::field::real::R);
    let half = ratio(1, 2);
    let sqrt = |v: Expr| v.pow(&half);
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
        Context::ASIN => u * &f + sqrt(&one - &u2),
        Context::ACOS => u * &f - sqrt(&one - &u2),
        Context::ATAN => u * &f - half * fun(Context::LN, &one + &u2),
        Context::ASINH => u * &f - sqrt(&u2 + &one),
        Context::ACOSH => u * &f - sqrt(&u2 - &one),
        Context::ATANH => u * &f + half * fun(Context::LN, &one - &u2),
        Context::ABS => half * u * f,
        Context::SIGN => fun(Context::ABS, u.clone()),
        _ => return None,
    })
}

/// `{$integral e^u sin v$}` and `{$integral e^u cos v$}` for linear `u` and `v`.
fn exp_trig(f: &Expr, x: Symbol) -> Option<Expr> {
    let [first, second] = factors(f).try_into().ok()?;
    let (exp, trig) = match (unary(&first)?, unary(&second)?) {
        (exp @ (Context::EXP, _), trig) | (trig, exp @ (Context::EXP, _)) => (exp, trig),
        _ => return None,
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

/// A quadratic polynomial `{$c_2 x^2 + c_1 x + c_0$}` written `{$c_2 (x + h)^2 + k$}`, as `{$(c_2, h, k)$}`.
fn quadratic(q: &Expr, x: Symbol) -> Option<(Rational, Rational, Rational)> {
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
    let half = ratio(1, 2);
    let sqrt_c = value(c).pow(&half);
    let pi = Term::Symbol(crate::term::SymbolTerm::new(
        Context::PI,
        crate::field::real::R,
    ));
    let erf = fun(ident, &sqrt_c * &(variable(x) + value(h)));
    Some(fun(Context::EXP, value(k)) * pi.pow(&half) / (ratio(2, 1) * sqrt_c) * erf)
}

/// `{$integral p e^q$}` for a polynomial `p` and a quadratic polynomial `q`: dividing `p` by `{$q'$}`,
/// `{$p = a q' + r$}` with a constant `r`, `{$integral a q' e^q = a e^q - integral a' e^q$}`, so the degree of the
/// remaining polynomial decreases until only `{$r integral e^q$}` is left.
fn polynomial_gaussian(f: &Expr, x: Symbol) -> Option<Expr> {
    // Products of exponentials `{$e^u e^v = e^(u + v)$}` and their powers are merged
    let mut q = Term::zero(crate::field::real::R);
    let mut rest = Term::one(crate::field::real::R);
    for factor in factors(f) {
        let (base, n) = match &factor {
            Term::Pow(pow) if pow.exponant.to_i64().is_some() => {
                (&*pow.base, (**pow.exponant).clone())
            }
            _ => (&factor, Term::one(crate::field::real::R)),
        };
        match unary(base) {
            Some((Context::EXP, u)) => q = q + n * u,
            _ => rest = rest * &factor,
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

/// `{$integral q^e$}` for a quadratic polynomial `q` and `{$e in {1/2, -1/2, -3/2}$}`, completing the square.
fn quadratic_power(q: &Expr, e: &Expr, x: Symbol) -> Option<Expr> {
    let (c2, h, k) = quadratic(q, x)?;
    let t = variable(x) + value(h);
    let sqrt_q = q.pow(&ratio(1, 2));
    let (c2_sign, k_sign) = (
        constant_sign(&value(c2.clone()))?,
        constant_sign(&value(k.clone()))?,
    );
    let sqrt = |v: Rational| value(v).pow(&ratio(1, 2));
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
    let n = e + &Term::one(crate::field::real::R);
    let derivative_part = value(alpha / (Rational::from(2) * c2)) * q.pow(&n) / n;
    let rest = value(beta - alpha * h);
    if rest.is_zero() {
        return Some(derivative_part);
    }
    Some(derivative_part + rest * quadratic_power(q, e, x)?)
}
