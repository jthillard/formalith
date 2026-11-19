//! Gosper's algorithm (Petkovšek, Wilf, Zeilberger, *A = B*, chapter 5): the antidifference of a hypergeometric
//! term `t`, whose ratio `{$t(k + 1) / t(k)$}` is a rational function of `k`, when it is itself hypergeometric.
//!
//! The ratio is written `{$a(k) / b(k) dot c(k + 1) / c(k)$}` with `{$gcd(a(k), b(k + j)) = 1$}` for every natural
//! `j` (Gosper form). The antidifference is `{$b(k - 1) x(k) / c(k) dot t(k)$}`, `x` being a polynomial solution
//! of `{$a(k) x(k + 1) - b(k - 1) x(k) = c(k)$}`, whose degree is bounded.

use malachite::Rational;

use crate::{
    context::{Context, Symbol},
    field::real::expr::{Expr, depends, subs, value, variable},
    integrate::rational::rational_roots,
    polynom::{
        dense::{Coefficient, Poly},
        fraction::{EPoly, Elem, interpolate, sample_points, solve_linear},
    },
    term::{Expand, Term},
};

use super::field::{Params, reduce};

/// Maximum degree of the polynomial solution of the key equation.
const MAX_DEGREE: usize = 40;

/// The antidifference of the hypergeometric term `t`, or `None` if it isn't hypergeometric or has no
/// hypergeometric antidifference.
pub(super) fn antidifference(t: &Expr, k: Symbol) -> Option<Expr> {
    let mut params = Params::default();
    let (num, den) = ratio(t, k, &mut params)?;
    let (a, b, c) = gosper_form(&num, &den, k)?;
    let b_shifted = b.shift(&Elem::integer(-1));
    let x = solve_key_equation(&a, &b_shifted, &c)?;
    // The certificate times the rational part `{$p / q$}` of `t`, reduced
    let (rational, rest) = split_rational(t, k, &mut params);
    let (p, q) = params.rational(&rational, k)?;
    let (num, den) = reduce(&b_shifted.mul(&x).mul(&p), &c.mul(&q));
    Some(params.k_poly_to_term(&num, k) / params.k_poly_to_term(&den, k) * rest)
}

/// The product of the factors of `t` which aren't handled by [`special_ratio`], a rational function of `k` when
/// `t` is hypergeometric, and the product of the other factors.
fn split_rational(t: &Expr, k: Symbol, params: &mut Params) -> (Expr, Expr) {
    let (factors, coefficient): (Vec<Expr>, Expr) = match t {
        Term::Mul(mul) => (
            mul.iter().cloned().collect(),
            value(mul.coefficient.clone()),
        ),
        _ => (vec![t.clone()], Term::one(crate::field::real::R)),
    };
    factors.iter().fold(
        (Term::one(crate::field::real::R), coefficient),
        |(rational, rest), factor| {
            if depends(factor, k) && special_factor(factor, k, params).is_none() {
                (rational * factor, rest)
            } else {
                (rational, rest * factor)
            }
        },
    )
}

/// The ratio of a factor `{$u^e$}` of a hypergeometric term, `u` being handled by [`special_ratio`] and `e` an
/// integer.
fn special_factor(factor: &Expr, k: Symbol, params: &mut Params) -> Option<(EPoly, EPoly)> {
    let (base, exponent) = match factor {
        Term::Pow(pow) if !depends(&pow.exponant, k) => match &**pow.exponant {
            Term::Value(e) => ((*pow.base).clone(), i64::try_from(&e.value).ok()?),
            _ => return None,
        },
        _ => (factor.clone(), 1),
    };
    let (n, d) = special_ratio(&base, k, params)?;
    let (n, d) = if exponent < 0 { (d, n) } else { (n, d) };
    let e = usize::try_from(exponent.unsigned_abs()).ok()?;
    Some((n.pow(e), d.pow(e)))
}

/// The ratio `{$t(k + 1) / t(k)$}` as a reduced fraction of polynomials, if `t` is hypergeometric: a product of
/// integer powers of rational functions of `k`, powers `{$c^(alpha k + beta)$}`, exponentials, and factorials,
/// `{$Gamma$}` and binomial coefficients of linear arguments with integer slopes.
pub(super) fn ratio(t: &Expr, k: Symbol, params: &mut Params) -> Option<(EPoly, EPoly)> {
    let mut num = EPoly::one();
    let mut den = EPoly::one();
    let mut rational = Term::one(crate::field::real::R);
    let factors: Vec<Expr> = match t {
        Term::Mul(mul) => mul.iter().cloned().collect(),
        _ => vec![t.clone()],
    };
    for factor in factors.iter().filter(|factor| depends(factor, k)) {
        match special_factor(factor, k, params) {
            Some((n, d)) => {
                num = num.mul(&n);
                den = den.mul(&d);
            }
            None => rational = rational * factor,
        }
    }
    // The rational part `{$p(k + 1) q(k) / (p(k) q(k + 1))$}`
    let (p, q) = params.rational(&rational, k)?;
    let one = Elem::one();
    num = num.mul(&p.shift(&one)).mul(&q);
    den = den.mul(&p).mul(&q.shift(&one));
    if num.is_zero() || den.is_zero() {
        return None;
    }
    Some(reduce(&num, &den))
}

/// `{$alpha$}` with `{$g(k + 1) - g(k) = alpha$}`, if it is free of `k`.
fn step(g: &Expr, k: Symbol) -> Option<Expr> {
    let alpha = (subs(g, k, &(variable(k) + value(Rational::from(1)))) - g).expand();
    (!depends(&alpha, k)).then_some(alpha)
}

/// The ratio of a factor which isn't a rational function: `{$c^g$}`, `{$exp(g)$}`, `{$g!$}`, `{$Gamma(g)$}` and
/// `{$binom(u, v)$}` with `g`, `u`, `v` linear in `k`. `None` for other factors.
fn special_ratio(u: &Expr, k: Symbol, params: &mut Params) -> Option<(EPoly, EPoly)> {
    match u {
        Term::Pow(pow) if !depends(&pow.base, k) => {
            // `{$c^(alpha k + beta)$}`
            let alpha = step(&pow.exponant, k)?;
            let r = params.elem(&pow.base.pow(&alpha))?;
            Some((EPoly::constant(r), EPoly::one()))
        }
        Term::Fun(fun) => {
            let args = fun.get_args::<crate::field::real::expr::Real>()?;
            match (fun.get_ident(), args.as_slice()) {
                (Context::EXP, [g]) => {
                    let alpha = step(g, k)?;
                    let r = params.elem(&crate::field::real::expr::fun(Context::EXP, alpha))?;
                    Some((EPoly::constant(r), EPoly::one()))
                }
                (Context::FACTORIAL, [g]) => factorial_ratio(g, 1, k, params),
                (Context::GAMMA, [g]) => factorial_ratio(g, 0, k, params),
                (Context::BINOMIAL, [n, m]) => {
                    // `{$binom(n, m) = n! / (m! (n - m)!)$}`
                    let (n1, d1) = factorial_ratio(n, 1, k, params)?;
                    let (n2, d2) = factorial_ratio(m, 1, k, params)?;
                    let (n3, d3) = factorial_ratio(&(n - m), 1, k, params)?;
                    Some((n1.mul(&d2).mul(&d3), d1.mul(&n2).mul(&n3)))
                }
                _ => None,
            }
        }
        _ => None,
    }
}

/// The ratio of `{$(g + s - 1)!$}`, `s` being 1 for factorials and 0 for `{$Gamma$}`, `g` linear in `k` with an
/// integer slope.
fn factorial_ratio(g: &Expr, s: i64, k: Symbol, params: &mut Params) -> Option<(EPoly, EPoly)> {
    if !depends(g, k) {
        return Some((EPoly::one(), EPoly::one()));
    }
    let alpha = match step(g, k)? {
        Term::Value(v) => i64::try_from(&v.value).ok()?,
        _ => return None,
    };
    let g = params.poly(g, k)?;
    // `{$(g + alpha)! / g! = (g + 1) ... (g + alpha)$}`, the factors of `{$Gamma$}` being shifted by `-1`
    let product = |from: i64, to: i64| {
        (from..=to).fold(EPoly::one(), |res, i| {
            res.mul(&g.add(&EPoly::constant(Elem::integer(i))))
        })
    };
    Some(if alpha >= 0 {
        (product(s, alpha + s - 1), EPoly::one())
    } else {
        (EPoly::one(), product(alpha + s, s - 1))
    })
}

/// The Gosper form `(a, b, c)` of the ratio `{$num / den$}`.
fn gosper_form(num: &EPoly, den: &EPoly, k: Symbol) -> Option<(EPoly, EPoly, EPoly)> {
    let (mut a, mut b) = (num.clone(), den.clone());
    let mut c = EPoly::one();
    for j in shifts(&a, &b, k)? {
        let g = a.gcd(&b.shift(&Elem::integer(j)));
        if g.degree() == 0 {
            continue;
        }
        a = a.exact_div(&g);
        b = b.exact_div(&g.shift(&Elem::integer(-j)));
        for i in 1..=j {
            c = c.mul(&g.shift(&Elem::integer(-i)));
        }
    }
    Some((a, b, c))
}

/// The natural numbers `j` for which `{$a(k)$}` and `{$b(k + j)$}` may have a common factor, increasing: the
/// natural roots of `{$"res"_k(a(k), b(k + j))$}`, computed with the parameters replaced by rational values.
fn shifts(a: &EPoly, b: &EPoly, k: Symbol) -> Option<Vec<i64>> {
    if a.degree() == 0 || b.degree() == 0 {
        return Some(vec![]);
    }
    let specialize = |p: &EPoly, point: &[Rational]| -> Option<Poly> {
        let coefficients: Option<Vec<_>> = p.coefficients().iter().map(|c| c.eval(point)).collect();
        let res = Poly::new(coefficients?);
        (res.degree() == p.degree()).then_some(res)
    };
    let (a, b) = sample_points(64)
        .take(8)
        .find_map(|point| Some((specialize(a, &point)?, specialize(b, &point)?)))?;
    let degree = a.degree() * b.degree();
    let points: Vec<_> = (0..=degree).map(Rational::from).collect();
    let values: Vec<_> = points
        .iter()
        .map(|j| Elem::rational(a.resultant(&b.shift(j))))
        .collect();
    let resultant: Poly =
        interpolate(&points, &values).map(|c| c.as_rational().cloned().unwrap_or_default());
    if resultant.is_zero() {
        return None;
    }
    let (roots, _) = rational_roots(&resultant, k);
    let mut res: Vec<i64> = roots
        .iter()
        .filter(|r| **r >= 0)
        .filter_map(|r| i64::try_from(r).ok())
        .collect();
    res.sort_unstable();
    Some(res)
}

/// A polynomial `x` with `{$a(k) x(k + 1) - b(k) x(k) = c(k)$}`, if there is one.
pub(super) fn solve_key_equation(a: &EPoly, b: &EPoly, c: &EPoly) -> Option<EPoly> {
    let degree = degree_bound(a, b, c)?;
    if degree > MAX_DEGREE {
        return None;
    }
    // The image of each `{$k^i$}`
    let one = Elem::one();
    let images: Vec<EPoly> = (0..=degree)
        .map(|i| {
            let monomial = EPoly::monomial(Elem::one(), i);
            a.mul(&monomial.shift(&one)).sub(&b.mul(&monomial))
        })
        .collect();
    let rows_count = images
        .iter()
        .map(|p| p.coefficients().len())
        .chain(std::iter::once(c.coefficients().len()))
        .max()
        .unwrap_or(0);
    let rows: Vec<Vec<Elem>> = (0..rows_count)
        .map(|row| {
            images
                .iter()
                .map(|p| p.coefficient(row))
                .chain(std::iter::once(c.coefficient(row)))
                .collect()
        })
        .collect();
    let x = solve_linear(rows, degree + 1)?;
    Some(EPoly::new(x))
}

/// An upper bound of the degree of a polynomial solution of `{$a(k) x(k + 1) - b(k) x(k) = c(k)$}`, `None` if
/// there is none. Written `{$(a - b) (x(k + 1) + x(k)) / 2 + (a + b) (x(k + 1) - x(k)) / 2 = c$}`, the leading
/// terms of the left side cancel only for one degree.
fn degree_bound(a: &EPoly, b: &EPoly, c: &EPoly) -> Option<usize> {
    let difference = a.sub(b);
    let sum = a.add(b);
    let c_degree = c.degree();
    if !difference.is_zero() && (sum.is_zero() || difference.degree() >= sum.degree()) {
        return c_degree.checked_sub(difference.degree());
    }
    // `{$x_d (mu + lambda d / 2)$}` is the coefficient of `{$k^(d + l - 1)$}`
    let l = sum.degree();
    let lambda = sum.leading();
    let mu = if l == 0 {
        Elem::zero()
    } else {
        difference.coefficient(l - 1)
    };
    let mut bound = (c_degree + 1).checked_sub(l);
    if let Some(d) = mu
        .times(&Elem::integer(-2))
        .divide(&lambda)
        .as_rational()
        .and_then(|d| usize::try_from(d).ok())
    {
        bound = Some(bound.map_or(d, |bound| bound.max(d)));
    }
    bound
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{field::real::R, parse, symbol};

    #[test]
    fn ratios() {
        let k = symbol!("k");
        let mut params = Params::default();
        let (num, den) = ratio(&parse!("k*factorial(k)", R), k, &mut params).unwrap();
        // `{$(k + 1)^2 / k$}`
        assert_eq!(
            num,
            EPoly::new(vec![Elem::integer(1), Elem::integer(2), Elem::integer(1)])
        );
        assert_eq!(den, EPoly::x());
        let (num, den) = ratio(&parse!("2^k/factorial(2k)", R), k, &mut params).unwrap();
        assert_eq!(num.degree(), 0);
        assert_eq!(den.degree(), 2);
    }

    #[test]
    fn gosper_antidifferences() {
        let k = symbol!("k");
        assert_eq!(
            antidifference(&parse!("k*factorial(k)", R), k),
            Some(parse!("factorial(k)", R))
        );
        assert_eq!(
            antidifference(&parse!("1/(k*(k+1))", R), k),
            Some(parse!("-1/k", R))
        );
        assert_eq!(antidifference(&parse!("1/k", R), k), None);
    }
}
