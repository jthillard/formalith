//! Products, with an antiquotient `G`, `{$G(k + 1) / G(k) = f(k)$}`: the product from `a` to `b` is
//! `{$G(b + 1) / G(a)$}`. A linear factor `{$alpha k + beta$}` gives `{$alpha^k Gamma(k + beta / alpha)$}`, written
//! with a factorial when `{$beta / alpha$}` is an integer.

use std::{cmp::Ordering, convert::Infallible};

use malachite::Rational;

use crate::{
    context::{Context, Symbol},
    field::real::{
        R,
        expr::{
            Expr, depends, fun, gamma_pole, has_special_constant, infinity_sign, one, subs,
            try_map_operands, unary, value, variable,
        },
    },
    integrate::rational::rational_roots,
    polynom::{
        dense::{Coefficient, Poly},
        fraction::{EPoly, Elem},
    },
    term::{Expand, Normalize, Term},
};

use super::{SumError, SumResult, antidifference, field::Params, limit};

/// Largest integer difference between arguments of factorials merged by [`combine_factorials`].
const MAX_SHIFT: u64 = 50;

/// An antiquotient of `f` with respect to `k`, if one is found.
pub(super) fn antiquotient(f: &Expr, k: Symbol) -> Option<Expr> {
    let k_term = variable(k);
    if !depends(f, k) {
        return Some(f.pow(&k_term));
    }
    match f {
        Term::Mul(mul) => mul
            .iter()
            .try_fold(value(mul.coefficient.clone()).pow(&k_term), |res, t| {
                Some(res * antiquotient(t, k)?)
            }),
        Term::Pow(pow) if !depends(&pow.exponant, k) => {
            Some(antiquotient(&pow.base, k)?.pow(&pow.exponant))
        }
        // `{$product c^(g(k)) = c^(sum g(k))$}`
        Term::Pow(pow) if !depends(&pow.base, k) => {
            Some(pow.base.pow(&antidifference(&pow.exponant, k)?))
        }
        Term::Fun(_) => match unary(f) {
            Some((Context::EXP, g)) => Some(fun(Context::EXP, antidifference(g, k)?)),
            _ => None,
        },
        _ => rational(f, k),
    }
}

/// The antiquotient of a rational function of `k` whose numerator and denominator are products of linear
/// factors.
fn rational(f: &Expr, k: Symbol) -> Option<Expr> {
    let mut params = Params::default();
    let (num, den) = params.rational(f, k)?;
    Some(polynomial(&num, k, &params)? / polynomial(&den, k, &params)?)
}

/// The antiquotient of a polynomial of degree 1, or with rational coefficients and rational roots.
fn polynomial(p: &EPoly, k: Symbol, params: &Params) -> Option<Expr> {
    let k_term = variable(k);
    let lead = params.to_term(&p.leading());
    let mut res = lead.pow(&k_term);
    let roots: Vec<(Elem, usize)> = match p.degree() {
        0 => vec![],
        1 => vec![(p.coefficient(0).divide(&p.coefficient(1)).negate(), 1)],
        _ => {
            let coefficients: Option<Vec<_>> = p
                .coefficients()
                .iter()
                .map(|c| c.as_rational().cloned())
                .collect();
            let p = Poly::new(coefficients?);
            let (roots, split) = rational_roots(&p, k);
            if !split {
                return None;
            }
            roots
                .into_iter()
                .map(|root| {
                    let linear = Poly::new(vec![-root.clone(), Rational::from(1)]);
                    let mut cofactor = p.clone();
                    let mut multiplicity = 0;
                    while cofactor.divisible_by(&linear) {
                        cofactor = cofactor.exact_div(&linear);
                        multiplicity += 1;
                    }
                    (Elem::rational(root), multiplicity)
                })
                .collect()
        }
    };
    for (root, multiplicity) in roots {
        // `{$product (k - r) = Gamma(k - r) = (k - r - 1)!$}`
        let factor = match root.as_rational() {
            Some(r) if r.denominator_ref() == &1u32 => fun(
                Context::FACTORIAL,
                &k_term - &value(r.clone() + Rational::from(1)),
            ),
            _ => fun(Context::GAMMA, &k_term - &params.to_term(&root)),
        };
        res *= factor.pow(&value(Rational::from(multiplicity)));
    }
    Some(res)
}

/// `{$G(b + 1) / G(a)$}`, with a limit when `b` is infinite.
pub(super) fn quotient(antiquotient: &Expr, k: Symbol, a: &Expr, b: &Expr) -> SumResult<Expr> {
    let lower = subs(antiquotient, k, a);
    if has_pole(&lower) || has_special_constant(&lower) || lower.is_zero() {
        return Err(SumError::Unsupported);
    }
    let upper = if infinity_sign(b).is_some() {
        limit(antiquotient, k, b)?
    } else {
        let upper = subs(antiquotient, k, &(b + &one()));
        if has_pole(&upper) || has_special_constant(&upper) {
            return Err(SumError::Unsupported);
        }
        upper
    };
    if let Some(sign) = infinity_sign(&upper) {
        let lower_sign =
            crate::field::real::expr::constant_sign(&lower).ok_or(SumError::Unsupported)?;
        return Err(SumError::Divergent(if lower_sign == Ordering::Less {
            sign.reverse()
        } else {
            sign
        }));
    }
    Ok(combine_factorials(&(upper / lower)))
}

/// Whether a factorial or `{$Gamma$}` is evaluated at a pole in the term.
fn has_pole(term: &Expr) -> bool {
    let mut res = false;
    visit(term, &mut |t| {
        res |= match unary(t) {
            Some((Context::FACTORIAL, u)) => gamma_pole(&(u + &one())).is_some(),
            Some((Context::GAMMA, u)) => gamma_pole(u).is_some(),
            _ => false,
        };
    });
    res
}

/// Call `f` on every subterm of `term`.
fn visit(term: &Expr, f: &mut impl FnMut(&Expr)) {
    f(term);
    let _ = try_map_operands::<Infallible>(term, |t| {
        visit(t, f);
        Ok(t.clone())
    });
}

/// Merge factorials and `{$Gamma$}` functions of a product whose arguments differ by integers, like
/// `{$(n + 1)! / n! = n + 1$}`.
pub(super) fn combine_factorials(term: &Expr) -> Expr {
    let Ok(term) = try_map_operands::<Infallible>(term, |t| Ok(combine_factorials(t)));
    let Term::Mul(mul) = &term else {
        return term;
    };
    // The factors `{$f(u)^e$}`, with `f` a factorial or `{$Gamma$}` and `e` an integer
    let parse = |t: &Expr| -> Option<(Symbol, Expr, Expr)> {
        let (base, exponent) = match t {
            Term::Pow(pow) => match &**pow.exponant {
                Term::Value(e) if e.value.denominator_ref() == &1u32 => {
                    ((*pow.base).clone(), (**pow.exponant).clone())
                }
                _ => return None,
            },
            _ => (t.clone(), one()),
        };
        match unary(&base) {
            Some((ident @ (Context::FACTORIAL | Context::GAMMA), u)) => {
                Some((ident, u.clone(), exponent))
            }
            _ => None,
        }
    };
    let factors: Vec<Expr> = mul.iter().cloned().collect();
    let parsed: Vec<_> = factors.iter().map(parse).collect();
    let mut merged = vec![false; factors.len()];
    let mut res = value(mul.coefficient.clone());
    for i in 0..factors.len() {
        if merged[i] {
            continue;
        }
        let Some((ident, u, _)) = &parsed[i] else {
            res *= &factors[i];
            continue;
        };
        // The factors of the group of `i` with their shifts from `u`
        let group: Vec<(usize, i64)> = (i..factors.len())
            .filter(|j| !merged[*j])
            .filter_map(|j| {
                let (other, v, _) = parsed[j].as_ref()?;
                if other != ident {
                    return None;
                }
                match (v - u).normalize() {
                    Term::Value(shift) if shift.value.denominator_ref() == &1u32 => {
                        Some((j, i64::try_from(&shift.value).ok()?))
                    }
                    _ => None,
                }
            })
            .filter(|(_, shift)| shift.unsigned_abs() <= MAX_SHIFT)
            .collect();
        let base = group.iter().map(|(_, shift)| *shift).min().unwrap_or(0);
        let lowest = u + &value(Rational::from(base));
        let mut exponent_sum = Term::zero(R);
        for (j, shift) in &group {
            merged[*j] = true;
            let exponent = &parsed[*j].as_ref().expect("Parsed factor").2;
            exponent_sum += exponent;
            // `{$(u + m)! = u! (u + 1) ... (u + m)$}`, `{$Gamma(u + m) = Gamma(u) u ... (u + m - 1)$}`
            let offset = i64::from(*ident == Context::GAMMA);
            for step in 1..=(shift - base) {
                let factor = &lowest + &value(Rational::from(step - offset));
                res *= factor.pow(exponent);
            }
        }
        res *= fun(*ident, lowest).pow(&exponent_sum);
    }
    absorb_factors(res)
}

/// Rewrite `{$u^(-1) u! = (u - 1)!$}`, `{$u / u! = 1 / (u - 1)!$}` and `{$(u + 1)^e u!^e = (u + 1)!^e$}` in a
/// product, repeatedly.
fn absorb_factors(term: Expr) -> Expr {
    let Term::Mul(mul) = &term else {
        return term;
    };
    let factors: Vec<Expr> = mul.iter().cloned().collect();
    for (i, factor) in factors.iter().enumerate() {
        let (base, exponent) = match factor {
            Term::Pow(pow) => match &**pow.exponant {
                Term::Value(e) if e.value == 1 || e.value == -1 => (&*pow.base, e.value.clone()),
                _ => continue,
            },
            _ => (factor, Rational::from(1)),
        };
        let Some((Context::FACTORIAL, u)) = unary(base) else {
            continue;
        };
        // A factor `{$(plus.minus u)^(-e)$}`, or `{$(u + 1)^e$}`
        let Some((j, sign, shift)) = factors.iter().enumerate().find_map(|(j, t)| {
            let (base, e) = match t {
                Term::Pow(pow) => match &**pow.exponant {
                    Term::Value(e) => (&*pow.base, e.value.clone()),
                    _ => return None,
                },
                _ => (t, Rational::from(1)),
            };
            if j == i {
                None
            } else if e == -&exponent && base == u {
                Some((j, Rational::from(1), -one()))
            } else if e == -&exponent && (base + u).expand().is_zero() {
                Some((j, Rational::from(-1), -one()))
            } else if e == exponent && (base - &(u + &one())).expand().is_zero() {
                Some((j, Rational::from(1), one()))
            } else {
                None
            }
        }) else {
            continue;
        };
        let res = factors
            .iter()
            .enumerate()
            .filter(|(index, _)| *index != i && *index != j)
            .fold(value(&mul.coefficient * sign), |res, (_, t)| res * t)
            * fun(Context::FACTORIAL, u + &shift).pow(&value(exponent));
        return absorb_factors(res);
    }
    term
}

/// Merge pairs of factorials and `{$Gamma$}` functions of a product with the duplication formula
/// `{$Gamma(z) Gamma(z + 1/2) = 2^(1 - 2z) sqrt(pi) Gamma(2z)$}` (`{$u! = Gamma(u + 1)$}`), with the same integer
/// exponent, like `{$k! Gamma(k + 3/2) = 2^(-2k - 1) sqrt(pi) (2k + 1)!$}`. `{$Gamma(2z)$}` is written with a
/// factorial when the constant part of `{$2z$}` is a positive integer.
pub(super) fn duplicate_gammas(term: &Expr) -> Expr {
    let Ok(term) = try_map_operands::<Infallible>(term, |t| Ok(duplicate_gammas(t)));
    let Term::Mul(mul) = &term else {
        return term;
    };
    // The factors `{$Gamma(z)^e$}`
    let parse = |t: &Expr| -> Option<(Expr, Expr)> {
        let (base, exponent) = match t {
            Term::Pow(pow) => match &**pow.exponant {
                Term::Value(e) if e.value.denominator_ref() == &1u32 => {
                    (&*pow.base, (**pow.exponant).clone())
                }
                _ => return None,
            },
            _ => (t, one()),
        };
        match unary(base)? {
            (Context::FACTORIAL, u) => Some((u + &one(), exponent)),
            (Context::GAMMA, z) => Some((z.clone(), exponent)),
            _ => None,
        }
    };
    let factors: Vec<Expr> = mul.iter().cloned().collect();
    let parsed: Vec<_> = factors.iter().map(parse).collect();
    for i in 0..factors.len() {
        let Some((z, e)) = &parsed[i] else { continue };
        let Some(j) = (0..factors.len()).find(|&j| {
            j != i
                && parsed[j].as_ref().is_some_and(|(v, f)| {
                    f == e && (v - z).normalize() == value(Rational::from_signeds(1, 2))
                })
        }) else {
            continue;
        };
        let two_z = (&value(Rational::from(2)) * z).expand();
        let constant = match &two_z {
            Term::Add(add) => add.iter().find_map(|t| match t {
                Term::Value(v) => Some(v.value.clone()),
                _ => None,
            }),
            Term::Value(v) => Some(v.value.clone()),
            _ => Some(Rational::from(0)),
        }
        .unwrap_or_default();
        let gamma = if constant.denominator_ref() == &1u32 && constant >= 1 {
            fun(Context::FACTORIAL, &two_z - &one())
        } else {
            fun(Context::GAMMA, two_z.clone())
        };
        let merged = value(Rational::from(2)).pow(&((one() - two_z) * e).expand())
            * variable(Context::PI).pow(&(value(Rational::from_signeds(1, 2)) * e))
            * gamma.pow(e);
        let res = factors
            .iter()
            .enumerate()
            .filter(|(index, _)| *index != i && *index != j)
            .fold(value(mul.coefficient.clone()), |res, (_, t)| res * t)
            * merged;
        return duplicate_gammas(&res);
    }
    term
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{parse, symbol};

    #[test]
    fn antiquotients() {
        let k = symbol!("k");
        assert_eq!(
            antiquotient(&parse!("k", R), k),
            Some(parse!("factorial(k - 1)", R))
        );
        assert_eq!(
            antiquotient(&parse!("2k + 1", R), k),
            Some(parse!("2^k*gamma(k + 1/2)", R))
        );
    }

    #[test]
    fn duplicated_gammas() {
        assert_eq!(
            duplicate_gammas(&parse!("1/(factorial(k)*gamma(k + 3/2))", R)),
            parse!("2^(2k + 1)/(sqrt(pi)*factorial(2k + 1))", R)
        );
    }

    #[test]
    fn merged_factorials() {
        assert_eq!(
            combine_factorials(&parse!("factorial(n + 1)/factorial(n - 1)", R)),
            parse!("n*(n + 1)", R)
        );
        assert_eq!(
            combine_factorials(&parse!("(n + 2)/factorial(n + 2)", R)),
            parse!("1/factorial(n + 1)", R)
        );
    }
}
