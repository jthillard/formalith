//! Antidifferences of polynomials (Faulhaber's formula), of geometric terms `{$r^k p(k)$}`, and of rational
//! functions with rational coefficients as sums of polygamma functions.

use malachite::{
    Natural, Rational,
    base::num::{
        arithmetic::traits::{BinomialCoefficient, Factorial},
        basic::traits::One,
    },
};

use crate::{
    context::{Context, Symbol},
    field::real::{
        expr::{Expr, depends, fun, polygamma, subs, value, variable, zero},
        special::bernoulli,
    },
    integrate::rational::rational_roots,
    polynom::{
        dense::{Coefficient, Poly},
        fraction::{EPoly, Elem},
    },
    term::Term,
};

use super::{
    field::Params,
    gosper::{ratio, solve_key_equation},
};

/// Maximum degree of the polynomials summed with Faulhaber's formula.
const MAX_DEGREE: usize = 100;

/// The antidifference of a polynomial in `k`, if `f` is one.
pub(super) fn polynomial(f: &Expr, k: Symbol) -> Option<Expr> {
    let mut params = Params::default();
    let p = params.poly(f, k)?;
    if p.degree() > MAX_DEGREE {
        return None;
    }
    Some(params.k_poly_to_term(&faulhaber(&p), k))
}

/// The polynomial `{$F$}` with `{$F(k + 1) - F(k) = p(k)$}` and `{$F(0) = 0$}`: `{$sum_(j < k) j^m =
/// (B_(m + 1)(k) - B_(m + 1)) / (m + 1)$}`, `{$B_n(k) = sum_i binom(n, i) B_i k^(n - i)$}` being the Bernoulli
/// polynomials.
fn faulhaber(p: &EPoly) -> EPoly {
    let mut res = EPoly::zero();
    for (m, c) in p.coefficients().iter().enumerate() {
        if c.is_zero() {
            continue;
        }
        let n = m + 1;
        let coefficients: Vec<Elem> = (0..=n)
            .map(|power| {
                if power == 0 {
                    return Elem::zero();
                }
                let i = n - power;
                let binomial = Natural::binomial_coefficient(Natural::from(n), Natural::from(i));
                Elem::rational(Rational::from(binomial) * bernoulli(i) / Rational::from(n))
            })
            .collect();
        res = res.add(&EPoly::new(coefficients).scale(c));
    }
    res
}

/// The antidifference of `{$r^k p(k)$}`, a product of powers `{$c^(alpha k + beta)$}` and exponentials of linear
/// arguments by a polynomial, `{$r != 1$}`: `{$r^k q(k)$}` with `{$r q(k + 1) - q(k) = p(k)$}`.
pub(super) fn geometric(f: &Expr, k: Symbol) -> Option<Expr> {
    let factors: Vec<Expr> = match f {
        Term::Mul(mul) => mul.iter().cloned().collect(),
        _ => vec![f.clone()],
    };
    let is_exponential = |t: &Expr| match t {
        Term::Pow(pow) => !depends(&pow.base, k),
        Term::Fun(fun) => fun.get_ident() == Context::EXP,
        _ => false,
    };
    let (exponentials, rest): (Vec<_>, Vec<_>) = factors
        .into_iter()
        .filter(|t| depends(t, k))
        .partition(|t| is_exponential(t));
    if exponentials.is_empty() {
        return None;
    }
    let exponential = exponentials
        .iter()
        .fold(Term::one(crate::field::real::R), |res, t| res * t);
    let polynomial = rest
        .iter()
        .fold(Term::one(crate::field::real::R), |res, t| res * t);
    let mut params = Params::default();
    let (r, den) = ratio(&exponential, k, &mut params)?;
    if r.degree() != 0 || den.degree() != 0 || r.leading() == den.leading() {
        return None;
    }
    let r = r.leading().divide(&den.leading());
    let p = params.poly(&polynomial, k)?;
    let constant = |c: Elem| EPoly::constant(c);
    let q = solve_key_equation(&constant(r), &EPoly::one(), &p)?;
    // Constant factors of `f`
    let coefficient = match f {
        Term::Mul(mul) => mul
            .iter()
            .filter(|t| !depends(t, k))
            .fold(value(mul.coefficient.clone()), |res, t| res * t),
        _ => value(Rational::ONE),
    };
    Some(coefficient * exponential * params.k_poly_to_term(&q, k))
}

/// The antidifference of a rational function of `k` with rational coefficients whose denominator is a product
/// of linear factors over `{$QQ$}`: `{$1 / (k - r)^m$}` gives `{$(-1)^(m - 1) / (m - 1)! psi^((m - 1))(k - r)$}`,
/// the polynomial part is summed with Faulhaber's formula.
pub(super) fn rational(f: &Expr, k: Symbol) -> Option<Expr> {
    let mut params = Params::default();
    let (num, den) = params.rational(f, k)?;
    if den.degree() == 0 {
        return None;
    }
    let to_rational = |p: &EPoly| -> Option<Poly> {
        let coefficients: Option<Vec<_>> = p
            .coefficients()
            .iter()
            .map(|c| c.as_rational().cloned())
            .collect();
        Some(Poly::new(coefficients?))
    };
    let (num, den) = (to_rational(&num)?, to_rational(&den)?);
    let (roots, split) = rational_roots(&den, k);
    if !split {
        return None;
    }
    let (quo, rem) = num.div_rem(&den);
    let mut res = params.k_poly_to_term(&faulhaber(&quo.map(|c| Elem::rational(c.clone()))), k);
    for root in roots {
        // `{$den = (k - r)^m d(k)$}`
        let linear = Poly::new(vec![-root.clone(), Rational::ONE]);
        let mut cofactor = den.clone();
        let mut multiplicity = 0;
        while cofactor.divisible_by(&linear) {
            cofactor = cofactor.exact_div(&linear);
            multiplicity += 1;
        }
        // The Laurent coefficients at `r` are the first coefficients of the series of `{$rem(r + u) / d(r + u)$}`
        let series = series_quotient(&rem.shift(&root), &cofactor.shift(&root), multiplicity);
        let argument = variable(k) - value(root);
        for (i, c) in series.iter().enumerate() {
            if *c == 0 {
                continue;
            }
            let j = multiplicity - i;
            let order = u64::try_from(j - 1).ok()?;
            let sign = if j % 2 == 1 {
                Rational::ONE
            } else {
                -Rational::ONE
            };
            let factor = sign / Rational::from(Natural::factorial(order)) * c;
            res += value(factor) * polygamma(order, argument.clone());
        }
    }
    Some(res)
}

/// The first `n` coefficients of the power series of `{$p / q$}`, with `{$q(0) != 0$}`.
fn series_quotient(p: &Poly, q: &Poly, n: usize) -> Vec<Rational> {
    let q0 = Rational::ONE / q.coefficient(0);
    let mut res: Vec<Rational> = Vec::with_capacity(n);
    for i in 0..n {
        let mut c = p.coefficient(i);
        for (j, r) in res.iter().enumerate() {
            c -= q.coefficient(i - j) * r;
        }
        res.push(c * &q0);
    }
    res
}

/// The infinite sum `{$sum_(k = a)^oo f$}` of a classic series: `{$k^(-s)$}` gives `{$zeta(s)$}` and
/// `{$x^k / k!$}` gives `{$e^x$}`, minus their first terms when `a` is a larger natural number.
pub(super) fn known_series(f: &Expr, k: Symbol, a: &Expr) -> Option<Expr> {
    let Term::Value(start) = a else {
        return None;
    };
    let start = u64::try_from(&start.value).ok()?;
    let head = |first: u64, term: &dyn Fn(u64) -> Expr| -> Option<Expr> {
        if start < first || start - first > super::MAX_TERMS {
            return None;
        }
        Some((first..start).fold(zero(), |res, i| res + term(i)))
    };
    let k_term = variable(k);
    // `{$zeta(s) = sum_(k >= 1) k^(-s)$}`
    if let Term::Pow(pow) = f
        && *pow.base == k_term
        && !depends(&pow.exponant, k)
    {
        let s = -(**pow.exponant).clone();
        let head = head(1, &|i| value(Rational::from(i)).pow(&pow.exponant))?;
        return Some(fun(Context::ZETA, s) - head);
    }
    // `{$e^x = sum_(k >= 0) x^k / k!$}`
    let factors: Vec<Expr> = match f {
        Term::Mul(mul) => mul.iter().cloned().collect(),
        _ => vec![f.clone()],
    };
    let factorial = fun(Context::FACTORIAL, k_term).inv();
    if !factors.contains(&factorial) {
        return None;
    }
    let rest = f / &factorial;
    let mut params = Params::default();
    let (r, den) = ratio(&rest, k, &mut params)?;
    if r.degree() != 0 || den.degree() != 0 {
        return None;
    }
    let x = params.to_term(&r.leading().divide(&den.leading()));
    // `{$f = c x^k / k!$}`
    let c = subs(&rest, k, &zero());
    let head = head(0, &|i| subs(f, k, &value(Rational::from(i))))?;
    Some(c * fun(Context::EXP, x) - head)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{field::real::R, parse, symbol};

    #[test]
    fn faulhaber_sums() {
        let k = symbol!("k");
        // `{$sum_(j < k) j = k (k - 1) / 2$}`
        assert_eq!(
            polynomial(&parse!("k", R), k),
            Some(parse!("k^2/2 - k/2", R))
        );
        assert_eq!(
            polynomial(&parse!("k^3", R), k),
            Some(parse!("k^4/4 - k^3/2 + k^2/4", R))
        );
    }

    #[test]
    fn polygamma_sums() {
        let k = symbol!("k");
        assert_eq!(
            rational(&parse!("1/k", R), k),
            Some(parse!("polygamma(0, k)", R))
        );
        assert_eq!(
            rational(&parse!("1/k^2", R), k),
            Some(parse!("-polygamma(1, k)", R))
        );
    }
}
