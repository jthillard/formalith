//! Truncated generalized power series in `{$w -> 0^+$}`, used for the leading terms of the Gruntz algorithm.
//!
//! A series is `{$sum_i c_i w^(e_i) + O(w^n)$}`, where the exponents `{$e_i$}` are constants (not necessarily
//! rational, like `{$ln 2 / ln 3$}`) and the coefficients `{$c_i$}` are free of `w` but may depend on `x`.
//! Orders are requested as absolute orders `n`, each operation computing its operands to the precision it needs.
//! `{$ln w$}` is replaced by its expression in `x`.

use crate::field::real::{
    expr::{
        Expr, depends, fun, gamma_pole, half, one, polygamma, polygamma_args, ratio, subs, unary,
        value, variable, zero,
    },
    special::bernoulli,
};
use std::cmp::Ordering;

use malachite::{
    Rational,
    base::num::{
        arithmetic::traits::Pow,
        basic::traits::{One, Zero},
    },
};

use crate::{
    context::{Context, Symbol},
    term::Term,
};

use super::{
    LimitError, LimitResult, const_cmp,
    gruntz::{Gruntz, eistar, erfcx, erfix, lgammastar, sif, sig},
    rational_bound,
};

/// Maximum number of times the order of a series is raised to find a non-zero leading term.
const MAX_REFINEMENTS: usize = 5;
/// Maximum number of terms of the power series composed with a series.
const MAX_TERMS: usize = 64;

/// A truncated series `{$sum_i c_i w^(e_i) + O(w^n)$}`.
#[derive(Clone, Debug)]
struct Series {
    /// Pairs `{$(e_i, c_i)$}`, sorted by increasing exponent, with distinct exponents.
    terms: Vec<(Expr, Expr)>,
    /// The order `n` of the remainder, `None` if the series is exact.
    order: Option<Rational>,
}

/// The smallest order, `None` standing for an exact series.
fn min_order(a: Option<&Rational>, b: Option<&Rational>) -> Option<Rational> {
    match (a, b) {
        (Some(a), Some(b)) => Some(a.min(b).clone()),
        (Some(order), None) | (None, Some(order)) => Some(order.clone()),
        (None, None) => None,
    }
}

impl Series {
    /// The exact series 0.
    const fn zero() -> Self {
        Self {
            terms: vec![],
            order: None,
        }
    }

    /// The exact series `{$c w^e$}`.
    fn monomial(exponant: Expr, coefficient: Expr) -> Self {
        let mut res = Self::zero();
        if !coefficient.is_zero() {
            res.terms.push((exponant, coefficient));
        }
        res
    }

    /// The exact constant series `c`.
    fn constant(coefficient: Expr) -> Self {
        Self::monomial(zero(), coefficient)
    }

    /// Whether the series is exactly zero.
    const fn is_zero(&self) -> bool {
        self.terms.is_empty() && self.order.is_none()
    }

    /// Add `{$c w^e$}` to the series, keeping it sorted.
    fn insert(&mut self, exponant: Expr, coefficient: Expr) -> LimitResult<()> {
        if coefficient.is_zero() {
            return Ok(());
        }
        for i in 0..self.terms.len() {
            match const_cmp(&exponant, &self.terms[i].0)? {
                Ordering::Equal => {
                    let sum = &self.terms[i].1 + &coefficient;
                    if sum.is_zero() {
                        self.terms.remove(i);
                    } else {
                        self.terms[i].1 = sum;
                    }
                    return Ok(());
                }
                Ordering::Less => {
                    self.terms.insert(i, (exponant, coefficient));
                    return Ok(());
                }
                Ordering::Greater => {}
            }
        }
        self.terms.push((exponant, coefficient));
        Ok(())
    }

    /// Drop the terms which are not below `{$w^n$}`, returning whether some were dropped.
    fn retain_below(&mut self, n: &Rational) -> LimitResult<bool> {
        let bound = value(n.clone());
        let mut terms = Vec::with_capacity(self.terms.len());
        let mut dropped = false;
        for (exponant, coefficient) in self.terms.drain(..) {
            if const_cmp(&exponant, &bound)? == Ordering::Less {
                terms.push((exponant, coefficient));
            } else {
                dropped = true;
            }
        }
        self.terms = terms;
        Ok(dropped)
    }

    /// Drop the terms which are not below the order of the series.
    fn clip(&mut self) -> LimitResult<()> {
        if let Some(order) = self.order.clone() {
            self.retain_below(&order)?;
        }
        Ok(())
    }

    /// Truncate the series at order `n`. An exact series stays exact if it has no term above `n`.
    fn truncate(&mut self, n: &Rational) -> LimitResult<()> {
        if self.retain_below(n)? || self.order.is_some() {
            self.order = min_order(self.order.as_ref(), Some(n));
        }
        Ok(())
    }

    /// A lower bound of the valuation, `None` for the zero series.
    fn valuation(&self) -> LimitResult<Option<Rational>> {
        match self.terms.first() {
            Some((exponant, _)) => rational_bound(exponant, false).map(Some),
            None => Ok(self.order.clone()),
        }
    }

    /// `{$a + b$}`.
    fn add(&self, other: &Self) -> LimitResult<Self> {
        let mut res = self.clone();
        for (exponant, coefficient) in &other.terms {
            res.insert(exponant.clone(), coefficient.clone())?;
        }
        res.order = min_order(self.order.as_ref(), other.order.as_ref());
        res.clip()?;
        Ok(res)
    }

    /// `{$a b$}`.
    fn mul(&self, other: &Self) -> LimitResult<Self> {
        if self.is_zero() || other.is_zero() {
            return Ok(Self::zero());
        }
        let mut res = Self::zero();
        for (e1, c1) in &self.terms {
            for (e2, c2) in &other.terms {
                res.insert(e1 + e2, c1 * c2)?;
            }
        }
        // `{$(a + O(w^n))(b + O(w^m)) = a b + O(w^(min(n + v(b), m + v(a))))$}`
        let (va, vb) = (self.valuation()?, other.valuation()?);
        let left = self.order.as_ref().zip(vb).map(|(n, v)| n + v);
        let right = other.order.as_ref().zip(va).map(|(m, v)| m + v);
        res.order = min_order(left.as_ref(), right.as_ref());
        res.clip()?;
        Ok(res)
    }

    /// `{$c w^e$}` times the series.
    fn scale(&self, exponant: &Expr, coefficient: &Expr) -> LimitResult<Self> {
        if coefficient.is_zero() {
            return Ok(Self::zero());
        }
        let mut res = Self::zero();
        for (e, c) in &self.terms {
            res.insert(e + exponant, c * coefficient)?;
        }
        res.order = match &self.order {
            Some(order) => Some(order + rational_bound(exponant, false)?),
            None => None,
        };
        Ok(res)
    }

    /// `{$u$}` such that the series is `{$c_0 w^(e_0) (1 + u)$}`, where `{$c_0 w^(e_0)$}` is its leading term.
    fn rest(&self, e0: &Expr, c0: &Expr) -> LimitResult<Self> {
        let mut res = Self::zero();
        for (e, c) in self.terms.iter().skip(1) {
            res.insert(e - e0, c / c0)?;
        }
        res.order = match &self.order {
            Some(order) => Some(order - rational_bound(e0, true)?),
            None => None,
        };
        Ok(res)
    }
}

/// The leading term `{$(c_0, e_0)$}` of `f`, `{$f ~ c_0 w^(e_0)$}` when `{$w -> 0^+$}`, `{$ln w$}` being `logw`.
pub(super) fn leadterm(gruntz: &mut Gruntz, f: &Expr, logw: &Expr) -> LimitResult<(Expr, Expr)> {
    let mut expander = Expander { gruntz, logw };
    let mut order = Rational::ONE;
    for _ in 0..MAX_REFINEMENTS {
        let mut series = expander.series(f, &order)?;
        if let Some((e0, c0)) = expander.strip_lead(&mut series) {
            return Ok((c0.simplify(), e0));
        }
        if series.order.is_none() {
            // `f` is zero
            return Ok((zero(), zero()));
        }
        order = refine(&order);
    }
    Err(LimitError::Unknown)
}

/// The terms `{$(e_i, c_i)$}` of the series of `f` up to `{$O(w^n)$}`, sorted by increasing exponent, without zero
/// coefficients, `{$ln w$}` being `logw`.
pub(super) fn expand(
    gruntz: &mut Gruntz,
    f: &Expr,
    logw: &Expr,
    n: &Rational,
) -> LimitResult<Vec<(Expr, Expr)>> {
    expand_exact(gruntz, f, logw, n).map(|(terms, _)| terms)
}

/// The terms of [`expand`], and whether they are the whole series of `f` (no remainder).
pub(super) fn expand_exact(
    gruntz: &mut Gruntz,
    f: &Expr,
    logw: &Expr,
    n: &Rational,
) -> LimitResult<(Vec<(Expr, Expr)>, bool)> {
    let series = Expander { gruntz, logw }.series(f, n)?;
    let exact = series.order.is_none();
    let terms = series
        .terms
        .into_iter()
        .filter(|(_, coefficient)| !gruntz.is_zero(coefficient))
        .map(|(exponant, coefficient)| (exponant, coefficient.simplify()))
        .collect();
    Ok((terms, exact))
}

/// A higher order to retry an expansion with.
fn refine(order: &Rational) -> Rational {
    if *order >= 1 {
        order * Rational::from(2)
    } else {
        order + Rational::ONE
    }
}

/// `{$1/n!$}`.
fn inverse_factorial(n: usize) -> Rational {
    (1..=n).fold(Rational::ONE, |res, i| res / Rational::from(i))
}

/// Computes series of expressions in `w`.
struct Expander<'a> {
    gruntz: &'a mut Gruntz,
    /// `{$ln w$}` as an expression in `x`.
    logw: &'a Expr,
}

impl Expander<'_> {
    /// The series of `f` up to `{$O(w^n)$}`.
    fn series(&mut self, f: &Expr, n: &Rational) -> LimitResult<Series> {
        let w = self.gruntz.w;
        if !depends(f, w) {
            return Ok(Series::constant(f.clone()));
        }
        let mut res = match f {
            Term::Symbol(_) => Series::monomial(one(), one()),
            Term::Add(add) => {
                let mut res = Series::zero();
                for term in add {
                    res = res.add(&self.series(term, n)?)?;
                }
                res
            }
            Term::Mul(mul) => {
                let factors: Vec<_> = mul.iter().collect();
                self.product(&value(mul.coefficient.clone()), &factors, n)?
            }
            Term::Pow(pow) if !depends(&pow.exponant, w) => {
                self.power(&pow.base, &pow.exponant, n)?
            }
            _ if polygamma_args(f).is_some() => {
                let (m, a) = polygamma_args(f).ok_or(LimitError::Unsupported)?;
                self.polygamma(m, a, n)?
            }
            _ => match unary(f) {
                Some((Context::EXP, a)) => self.exp(a, n)?,
                Some((Context::GAMMA, a)) => self.gamma(a, n)?,
                Some((ident, a)) if ident == lgammastar() => self.lgammastar(a, n)?,
                Some((Context::LN, a)) => self.ln(a, n)?,
                Some((ident @ (Context::SIN | Context::COS), a)) => self.sin_cos(ident, a, n)?,
                Some((Context::ABS, a)) => self.abs(a, n)?,
                Some((Context::ATAN, a)) => self.atan(a, n)?,
                Some((ident @ (Context::ERF | Context::ERFI), a)) => self.erf(ident, a, n)?,
                Some((ident, a)) if ident == erfcx() => self.erfcx(a, n, true)?,
                Some((ident, a)) if ident == erfix() => self.erfcx(a, n, false)?,
                Some((ident @ (Context::SI | Context::CI | Context::EI), a)) => {
                    self.exponential_integral(ident, a, n)?
                }
                Some((ident, a)) if ident == sif() || ident == sig() || ident == eistar() => {
                    self.auxiliary_integral(ident, a, n)?
                }
                _ => return Err(LimitError::Unsupported),
            },
        };
        res.truncate(n)?;
        Ok(res)
    }

    /// Remove the leading terms of `series` with a zero coefficient, and return its leading term `{$(e_0, c_0)$}`.
    fn strip_lead(&self, series: &mut Series) -> Option<(Expr, Expr)> {
        while let Some((exponant, coefficient)) = series.terms.first() {
            if self.gruntz.is_zero(coefficient) {
                series.terms.remove(0);
            } else {
                return Some((exponant.clone(), coefficient.clone()));
            }
        }
        None
    }

    /// The series of `f` with a known leading term, raising the order until it is found. Fails if `f` is zero.
    fn with_lead(&mut self, f: &Expr, n: &Rational) -> LimitResult<(Series, Expr, Expr)> {
        let mut order = n.clone();
        for _ in 0..MAX_REFINEMENTS {
            let mut series = self.series(f, &order)?;
            if let Some((e0, c0)) = self.strip_lead(&mut series) {
                return Ok((series, e0, c0));
            }
            if series.order.is_none() {
                return Err(LimitError::Unsupported);
            }
            order = refine(&order);
        }
        Err(LimitError::Unknown)
    }

    /// The series of `c` times the product of `factors`.
    fn product(&mut self, c: &Expr, factors: &[&Expr], n: &Rational) -> LimitResult<Series> {
        let mut series = factors
            .iter()
            .map(|factor| self.series(factor, n))
            .collect::<LimitResult<Vec<_>>>()?;
        if series.iter().any(Series::is_zero) {
            return Ok(Series::zero());
        }
        let valuations = series
            .iter()
            .map(|series| series.valuation().map(Option::unwrap_or_default))
            .collect::<LimitResult<Vec<_>>>()?;
        let total: Rational = valuations.iter().sum();
        // Each factor needs the precision `n` minus the valuation of the others
        for (i, factor) in factors.iter().enumerate() {
            let needed = n - (&total - &valuations[i]);
            if series[i]
                .order
                .as_ref()
                .is_some_and(|order| *order < needed)
            {
                series[i] = self.series(factor, &needed)?;
            }
        }
        series
            .iter()
            .try_fold(Series::constant(c.clone()), |res, series| res.mul(series))
    }

    /// `{$sum_j a_j u^j + O(w^"target")$}` for `u` with a positive valuation, `{$a_j$}` being `coefficients(j)`,
    /// `None` when the power series ends.
    fn compose(
        u: &Series,
        coefficients: impl Fn(usize) -> Option<Expr>,
        target: &Rational,
    ) -> LimitResult<Series> {
        let target = min_order(Some(target), u.order.as_ref()).unwrap_or_default();
        let mut res = Series::constant(coefficients(0).unwrap_or(zero()));
        let Some((valuation, _)) = u.terms.first() else {
            if u.order.is_some() {
                res.order = Some(target);
                res.clip()?;
            }
            return Ok(res);
        };
        let valuation = rational_bound(valuation, false)?;
        if valuation <= 0 {
            return Err(LimitError::Unknown);
        }
        let mut power = Series::constant(one());
        let mut ended = false;
        for j in 1.. {
            let Some(coefficient) = coefficients(j) else {
                ended = true;
                break;
            };
            if &valuation * Rational::from(j) >= target {
                break;
            }
            if j > MAX_TERMS {
                return Err(LimitError::Unknown);
            }
            power = power.mul(u)?;
            power.truncate(&target)?;
            res = res.add(&power.scale(&zero(), &coefficient)?)?;
        }
        if !ended {
            res.order = min_order(res.order.as_ref(), Some(&target));
            res.clip()?;
        }
        Ok(res)
    }

    /// `{$b^k$}` for a constant `k`, with `{$(c_0 w^(e_0) (1 + u))^k = c_0^k w^(e_0 k) sum_j binom(k, j) u^j$}`.
    fn power(&mut self, base: &Expr, k: &Expr, n: &Rational) -> LimitResult<Series> {
        let (mut series, mut e0, mut c0) = self.with_lead(base, n)?;
        let e0k = &e0 * k;
        // Relative precision of the result
        let relative = n - rational_bound(&e0k, false)?;
        let needed = rational_bound(&e0, true)? + &relative;
        if series.order.as_ref().is_some_and(|order| *order < needed) {
            (series, e0, c0) = self.with_lead(base, &needed)?;
        }
        // Roots of negative values aren't real
        if k.to_i64().is_none() && self.gruntz.sign(&c0) == Ok(Ordering::Less) {
            return Err(LimitError::Unsupported);
        }
        let u = series.rest(&e0, &c0)?;
        let natural = k.to_i64().filter(|k| *k >= 0);
        let binomial = |j: usize| {
            if natural.is_some_and(|k| usize::try_from(k).is_ok_and(|k| j > k)) {
                return None;
            }
            // `{$binom(k, j) = product_(i < j) (k - i) / j!$}`
            Some((0..j).fold(value(inverse_factorial(j)), |res, i| {
                res * (k - &value(Rational::from(i)))
            }))
        };
        let res = Self::compose(&u, binomial, &relative)?;
        res.scale(&(&e0 * k), &c0.pow(k))
    }

    /// The constant term and the rest of the series of `a`, which must not have negative exponents.
    fn split_constant(&self, series: Series) -> LimitResult<(Expr, Series)> {
        let mut constant = zero();
        let mut rest = Series {
            terms: vec![],
            order: series.order,
        };
        for (exponant, coefficient) in series.terms {
            match const_cmp(&exponant, &zero())? {
                Ordering::Less if !self.gruntz.is_zero(&coefficient) => {
                    return Err(LimitError::Unsupported);
                }
                Ordering::Less => {}
                Ordering::Equal => constant = coefficient,
                Ordering::Greater => rest.terms.push((exponant, coefficient)),
            }
        }
        Ok((constant, rest))
    }

    /// `{$e^a$}`, with `{$e^(a_0 + u) = e^(a_0) sum_j u^j / j!$}`.
    fn exp(&mut self, a: &Expr, n: &Rational) -> LimitResult<Series> {
        let n = n.max(&Rational::ONE).clone();
        let series = self.series(a, &n)?;
        let (a0, u) = self.split_constant(series)?;
        let res = Self::compose(&u, |j| Some(value(inverse_factorial(j))), &n)?;
        res.scale(&zero(), &fun(Context::EXP, a0))
    }

    /// `{$ln a$}`, with `{$ln(c_0 w^(e_0) (1 + u)) = ln c_0 + e_0 ln w + sum_(j >= 1) (-1)^(j + 1) u^j / j$}`.
    fn ln(&mut self, a: &Expr, n: &Rational) -> LimitResult<Series> {
        let n = n.max(&Rational::ONE).clone();
        let (mut series, mut e0, mut c0) = self.with_lead(a, &n)?;
        let needed = rational_bound(&e0, true)? + &n;
        if series.order.as_ref().is_some_and(|order| *order < needed) {
            (series, e0, c0) = self.with_lead(a, &needed)?;
        }
        let u = series.rest(&e0, &c0)?;
        let res = Self::compose(
            &u,
            |j| {
                Some(if j == 0 {
                    zero()
                } else {
                    let sign = if j % 2 == 0 { -1 } else { 1 };
                    value(Rational::from_signeds(sign, i64::try_from(j).ok()?))
                })
            },
            &n,
        )?;
        let constant = fun(Context::LN, c0) + e0 * self.logw;
        res.add(&Series::constant(constant))
    }

    /// `{$sin a$}` or `{$cos a$}`, expanded around the constant term of `a`.
    fn sin_cos(
        &mut self,
        ident: crate::context::Symbol,
        a: &Expr,
        n: &Rational,
    ) -> LimitResult<Series> {
        let n = n.max(&Rational::ONE).clone();
        let series = self.series(a, &n)?;
        let (a0, u) = self.split_constant(series)?;
        // `{$sin u = sum_j (-1)^j u^(2 j + 1) / (2 j + 1)!$}`, `{$cos u = sum_j (-1)^j u^(2 j) / (2 j)!$}`
        let taylor = |parity: usize| {
            move |j: usize| {
                Some(if j % 2 == parity {
                    let sign = if (j / 2) % 2 == 0 { 1 } else { -1 };
                    value(inverse_factorial(j) * Rational::from(sign))
                } else {
                    zero()
                })
            }
        };
        let sin_u = Self::compose(&u, taylor(1), &n)?;
        let cos_u = Self::compose(&u, taylor(0), &n)?;
        let (sin_a0, cos_a0) = (fun(Context::SIN, a0.clone()), fun(Context::COS, a0));
        let zero = zero();
        if ident == Context::SIN {
            // `{$sin(a_0 + u) = sin a_0 cos u + cos a_0 sin u$}`
            cos_u
                .scale(&zero, &sin_a0)?
                .add(&sin_u.scale(&zero, &cos_a0)?)
        } else {
            // `{$cos(a_0 + u) = cos a_0 cos u - sin a_0 sin u$}`
            cos_u
                .scale(&zero, &cos_a0)?
                .add(&sin_u.scale(&zero, &-sin_a0)?)
        }
    }

    /// `{$atan a$}`, with `{$atan a = plus.minus pi/2 - atan(1/a)$}` if `{$a -> plus.minus oo$}`, otherwise
    /// `{$atan a = atan a_0 + atan v$}` with `{$v = (a - a_0)/(1 + a_0 a)$}` and
    /// `{$atan v = sum_j (-1)^j v^(2 j + 1) / (2 j + 1)$}`.
    fn atan(&mut self, a: &Expr, n: &Rational) -> LimitResult<Series> {
        let n = n.max(&Rational::ONE).clone();
        let (series, e0, c0) = self.with_lead(a, &n)?;
        let zero = zero();
        if const_cmp(&e0, &zero)? == Ordering::Less {
            let half_pi = variable(Context::PI) * half();
            let half_pi = match self.gruntz.sign(&c0)? {
                Ordering::Greater => half_pi,
                Ordering::Less => -half_pi,
                Ordering::Equal => return Err(LimitError::Unknown),
            };
            let rest = self.atan(&a.inv(), &n)?;
            return Series::constant(half_pi).add(&rest.scale(&zero, &value(-Rational::ONE))?);
        }
        let (a0, _) = self.split_constant(series)?;
        let v = if a0.is_zero() {
            a.clone()
        } else {
            (a - &a0) / (one() + &a0 * a)
        };
        let v = self.series(&v, &n)?;
        let res = Self::compose(
            &v,
            |j| {
                Some(if j % 2 == 1 {
                    let sign = if (j / 2) % 2 == 0 { 1 } else { -1 };
                    value(Rational::from_signeds(sign, i64::try_from(j).ok()?))
                } else {
                    zero.clone()
                })
            },
            &n,
        )?;
        res.add(&Series::constant(fun(Context::ATAN, a0)))
    }

    /// `{$"erf" a$}` or `{$"erfi" a$}` for a bounded `a`, with the Taylor series
    /// `{$"erf"(a_0 + u) = "erf" a_0 + 2/sqrt(pi) e^(-a_0^2) sum_(j >= 1) (-1)^(j - 1) H_(j - 1)(a_0) u^j / j!$}`,
    /// `{$H_n$}` being the Hermite polynomials, and the same without the signs and with `{$e^(a_0^2)$}` for
    /// `{$"erfi"$}`.
    fn erf(&mut self, ident: Symbol, a: &Expr, n: &Rational) -> LimitResult<Series> {
        let n = n.max(&Rational::ONE).clone();
        let series = self.series(a, &n)?;
        let (a0, u) = self.split_constant(series)?;
        let imaginary = ident == Context::ERFI;
        let square = &a0 * &a0;
        let scale = value(Rational::from(2))
            * variable(Context::PI).pow(&ratio(-1, 2))
            * fun(Context::EXP, if imaginary { square } else { -square });
        Self::compose(
            &u,
            |j| {
                if j == 0 {
                    return Some(fun(ident, a0.clone()));
                }
                // `{$H_n(t) / (n + 1)! = 1/(n + 1) sum_m (-1)^m (2 t)^(n - 2 m) / (m! (n - 2 m)!)$}`
                let degree = j - 1;
                let hermite = (0..=degree / 2).fold(zero(), |res, m| {
                    let power = degree - 2 * m;
                    let sign = if imaginary || (degree + m) % 2 == 0 {
                        1
                    } else {
                        -1
                    };
                    let c = Rational::from(sign)
                        * Rational::from(2_u32).pow(u64::try_from(power).unwrap_or(0))
                        * inverse_factorial(m)
                        * inverse_factorial(power);
                    res + value(c) * a0.pow(&value(Rational::from(power)))
                });
                Some(&scale * &hermite / value(Rational::from(j)))
            },
            &n,
        )
    }

    /// `{$"erfcx" a$}` for `{$a -> +oo$}`, with the asymptotic series
    /// `{$"erfcx" a = 1/sqrt(pi) sum_k (-1)^k (2 k - 1)!! / 2^k a^(-2 k - 1)$}`, or `{$"erfix" a$}` with the same
    /// series without the signs when `alternating` is false.
    fn erfcx(&mut self, a: &Expr, n: &Rational, alternating: bool) -> LimitResult<Series> {
        let n = n.max(&Rational::ONE).clone();
        let (_, e0, c0) = self.with_lead(a, &n)?;
        if const_cmp(&e0, &zero())? != Ordering::Less || self.gruntz.sign(&c0)? != Ordering::Greater
        {
            return Err(LimitError::Unsupported);
        }
        let v = self.series(&a.inv(), &n)?;
        let inv_sqrt_pi = variable(Context::PI).pow(&ratio(-1, 2));
        Self::compose(
            &v,
            |j| {
                if j % 2 == 0 {
                    return Some(zero());
                }
                let k = (j - 1) / 2;
                // `{$(2 k - 1)!! / 2^k = prod_(i < k) (i + 1/2)$}`
                let c = (0..k).fold(Rational::ONE, |res, i| {
                    res * (Rational::from(i) + Rational::from_signeds(1, 2))
                });
                let c = if !alternating || k % 2 == 0 { c } else { -c };
                Some(value(c) * &inv_sqrt_pi)
            },
            &n,
        )
    }

    /// `{$"Si" a$}`, `{$"Ci" a$}` or `{$"Ei" a$}` for a bounded `a`. At `{$a_0 = 0$}`, with their power series
    /// `{$"Si" a = sum_k (-1)^k a^(2 k + 1) / ((2 k + 1) (2 k + 1)!)$}`,
    /// `{$"Ci" a = gamma + ln a + sum_(k >= 1) (-1)^k a^(2 k) / (2 k (2 k)!)$}` (`{$a -> 0^+$}`) and
    /// `{$"Ei" a = gamma + ln|a| + sum_(k >= 1) a^k / (k k!)$}`. Elsewhere, with their Taylor series, from the
    /// derivatives of `{$sin(t)/t$}`, `{$cos(t)/t$}` or `{$e^t/t$}` at `{$a_0$}` (positive for `{$"Ci"$}`).
    fn exponential_integral(
        &mut self,
        ident: Symbol,
        a: &Expr,
        n: &Rational,
    ) -> LimitResult<Series> {
        let n = n.max(&Rational::ONE).clone();
        let series = self.series(a, &n)?;
        let (a0, u) = self.split_constant(series.clone())?;
        if self.gruntz.is_zero(&a0) {
            if ident == Context::CI {
                let (_, _, c0) = self.with_lead(a, &n)?;
                if self.gruntz.sign(&c0)? != Ordering::Greater {
                    return Err(LimitError::Unsupported);
                }
            }
            let power = Self::compose(
                &series,
                |j| {
                    let (j_i64, sign) = (
                        i64::try_from(j).ok()?,
                        if (j / 2) % 2 == 0 { 1 } else { -1 },
                    );
                    let c = inverse_factorial(j) / Rational::from(j_i64.max(1));
                    Some(value(match ident {
                        Context::SI if j % 2 == 1 => Rational::from(sign) * c,
                        Context::CI if j % 2 == 0 && j > 0 => Rational::from(sign) * c,
                        Context::EI if j > 0 => c,
                        _ => Rational::ZERO,
                    }))
                },
                &n,
            )?;
            if ident == Context::SI {
                return Ok(power);
            }
            let log =
                variable(Context::EULER_GAMMA) + fun(Context::LN, fun(Context::ABS, a.clone()));
            return self.series(&log, &n)?.add(&power);
        }
        if ident == Context::CI && self.gruntz.sign(&a0)? != Ordering::Greater {
            return Err(LimitError::Unsupported);
        }
        // The derivatives of the integrand `{$d_1 = h(t)/t$}`, `{$d_(j + 1) = d_j'$}`, computed when needed
        let t = Symbol::new("@ts");
        let integrand = match ident {
            Context::SI => Context::SIN,
            Context::CI => Context::COS,
            _ => Context::EXP,
        };
        let derivatives = std::cell::RefCell::new(vec![fun(integrand, variable(t)) / variable(t)]);
        Self::compose(
            &u,
            |j| {
                if j == 0 {
                    return Some(fun(ident, a0.clone()));
                }
                let mut derivatives = derivatives.borrow_mut();
                while derivatives.len() < j {
                    let next = derivatives.last()?.derivative(t);
                    derivatives.push(next);
                }
                Some(subs(&derivatives[j - 1], t, &a0) * value(inverse_factorial(j)))
            },
            &n,
        )
    }

    /// The auxiliary functions [`sif`], [`sig`] and [`eistar`] of the sine, cosine and exponential integrals at
    /// `{$a -> plus.minus oo$}`, with their asymptotic series `{$sum_k (-1)^k (2 k)! a^(-2 k - 1)$}`,
    /// `{$sum_k (-1)^k (2 k + 1)! a^(-2 k - 2)$}` and `{$sum_(k >= 1) (k - 1)! a^(-k)$}`.
    fn auxiliary_integral(&mut self, ident: Symbol, a: &Expr, n: &Rational) -> LimitResult<Series> {
        let n = n.max(&Rational::ONE).clone();
        let (_, e0, _) = self.with_lead(a, &n)?;
        if const_cmp(&e0, &zero())? != Ordering::Less {
            return Err(LimitError::Unsupported);
        }
        let v = self.series(&a.inv(), &n)?;
        Self::compose(
            &v,
            |j| {
                if j == 0 {
                    return Some(zero());
                }
                // `{$(j - 1)!$}`, with the sign `{$(-1)^k$}` of the k-th term of `f` or `g`
                let factorial = (1..j).fold(Rational::ONE, |res, i| res * Rational::from(i));
                let sign = if ((j - 1) / 2) % 2 == 0 {
                    Rational::ONE
                } else {
                    -Rational::ONE
                };
                Some(value(if ident == eistar() {
                    factorial
                } else if (ident == sif()) == (j % 2 == 1) {
                    sign * factorial
                } else {
                    Rational::ZERO
                }))
            },
            &n,
        )
    }

    /// `{$Gamma(a)$}` for a bounded `a`, with `{$Gamma(a_0 + u) = Gamma(a_0) exp(sum_(j >= 1) psi^((j - 1))(a_0) u^j / j!)$}`,
    /// and `{$Gamma(a) = Gamma(a + k + 1) / (a (a + 1) ... (a + k))$}` at a pole `{$a_0 = -k$}`. Unbounded arguments
    /// are rewritten by Stirling's formula before (see [`lgammastar`]).
    fn gamma(&mut self, a: &Expr, n: &Rational) -> LimitResult<Series> {
        let n = n.max(&Rational::ONE).clone();
        let series = self.series(a, &n)?;
        let (a0, u) = self.split_constant(series)?;
        if let Some(k) = gamma_pole(&a0) {
            let shifted = (0..=k).fold(
                fun(Context::GAMMA, a + &value(Rational::from(k + 1))),
                |res, i| res / (a + &value(Rational::from(i))),
            );
            return self.series(&shifted, &n);
        }
        let exponant = Self::compose(
            &u,
            |j| {
                Some(if j == 0 {
                    zero()
                } else {
                    polygamma(u64::try_from(j - 1).ok()?, a0.clone()) * value(inverse_factorial(j))
                })
            },
            &n,
        )?;
        let res = Self::compose(&exponant, |j| Some(value(inverse_factorial(j))), &n)?;
        res.scale(&zero(), &fun(Context::GAMMA, a0))
    }

    /// `{$psi^((m))(a)$}`, with the Taylor series `{$psi^((m))(a_0 + u) = sum_j psi^((m + j))(a_0) u^j / j!$}`, the
    /// recurrence `{$psi^((m))(a) = psi^((m))(a + k + 1) - (-1)^m m! sum_(i <= k) (a + i)^(-m - 1)$}` at a pole
    /// `{$a_0 = -k$}`, and for `{$a -> +oo$}` the asymptotic series
    /// `{$psi(a) ~ ln a - 1/(2 a) - sum_k B_(2 k) / (2 k a^(2 k))$}`, and for `{$m >= 1$}`
    /// `{$psi^((m))(a) ~ (-1)^(m + 1) ((m - 1)!/a^m + m!/(2 a^(m + 1)) + sum_k B_(2 k) (2 k + m - 1)!/(2 k)! a^(-2 k - m))$}`.
    fn polygamma(&mut self, m: u64, a: &Expr, n: &Rational) -> LimitResult<Series> {
        let n = n.max(&Rational::ONE).clone();
        let (series, e0, c0) = self.with_lead(a, &n)?;
        if const_cmp(&e0, &zero())? == Ordering::Less {
            if self.gruntz.sign(&c0)? != Ordering::Greater {
                return Err(LimitError::Unsupported);
            }
            let v = self.series(&a.inv(), &n)?;
            // `{$(-1)^(m + 1) j! / j!$}` scaled factorials, as rationals
            let factorial = |j: u64| (1..=j).fold(Rational::ONE, |res, i| res * Rational::from(i));
            let sign = if m % 2 == 0 {
                -Rational::ONE
            } else {
                Rational::ONE
            };
            let rest = Self::compose(
                &v,
                |j| {
                    let j = u64::try_from(j).ok()?;
                    let c = if m == 0 {
                        // `{$-1/(2 a) - sum_k B_(2 k) / (2 k a^(2 k))$}`
                        match j {
                            1 => -Rational::from_signeds(1, 2),
                            _ if j >= 2 && j % 2 == 0 => {
                                -bernoulli(usize::try_from(j).ok()?) / Rational::from(j)
                            }
                            _ => Rational::ZERO,
                        }
                    } else if j == m {
                        &sign * factorial(m - 1)
                    } else if j == m + 1 {
                        &sign * factorial(m) / Rational::from(2)
                    } else if j > m + 1 && (j - m) % 2 == 0 {
                        let k = j - m;
                        &sign * bernoulli(usize::try_from(k).ok()?) * factorial(j - 1)
                            / factorial(k)
                    } else {
                        Rational::ZERO
                    };
                    Some(value(c))
                },
                &n,
            )?;
            return if m == 0 {
                rest.add(&self.ln(a, &n)?)
            } else {
                Ok(rest)
            };
        }
        let (a0, u) = self.split_constant(series)?;
        if let Some(k) = gamma_pole(&a0) {
            let order = value(Rational::from(m + 1));
            let factorial = (1..=m).fold(Rational::ONE, |res, i| res * Rational::from(i));
            let scale = value(if m % 2 == 0 { factorial } else { -factorial });
            let shifted = (0..=k)
                .fold(polygamma(m, a + &value(Rational::from(k + 1))), |res, i| {
                    res - &scale * &(a + &value(Rational::from(i))).pow(&-&order)
                });
            return self.series(&shifted, &n);
        }
        Self::compose(
            &u,
            |j| {
                Some(
                    polygamma(m + u64::try_from(j).ok()?, a0.clone()) * value(inverse_factorial(j)),
                )
            },
            &n,
        )
    }

    /// `{$"lgammastar" a$}` for `{$a -> +oo$}`, the remainder of Stirling's formula, with the asymptotic series
    /// `{$sum_k B_(2 k) / (2 k (2 k - 1) a^(2 k - 1))$}`.
    fn lgammastar(&mut self, a: &Expr, n: &Rational) -> LimitResult<Series> {
        let n = n.max(&Rational::ONE).clone();
        let (_, e0, c0) = self.with_lead(a, &n)?;
        if const_cmp(&e0, &zero())? != Ordering::Less || self.gruntz.sign(&c0)? != Ordering::Greater
        {
            return Err(LimitError::Unsupported);
        }
        let v = self.series(&a.inv(), &n)?;
        Self::compose(
            &v,
            |j| {
                if j % 2 == 0 {
                    return Some(zero());
                }
                let k = j.div_ceil(2);
                let c = bernoulli(2 * k) / Rational::from(u64::try_from(2 * k * (2 * k - 1)).ok()?);
                Some(value(c))
            },
            &n,
        )
    }

    /// `{$|a|$}`, the sign of the leading coefficient of `a`.
    fn abs(&mut self, a: &Expr, n: &Rational) -> LimitResult<Series> {
        let (series, _, c0) = self.with_lead(a, n)?;
        match self.gruntz.sign(&c0)? {
            Ordering::Greater => Ok(series),
            Ordering::Less => series.scale(&zero(), &value(-Rational::ONE)),
            Ordering::Equal => Err(LimitError::Unknown),
        }
    }
}
