//! The Gruntz algorithm, computing limits at `{$+oo$}` (Dominik Gruntz, "On Computing Limits in a Symbolic
//! Manipulation System", 1996).
//!
//! The most rapidly varying subexpressions of `f` ([`Gruntz::mrv`]) are its subexpressions `{$g$}` in the
//! greatest comparability class, `{$f$}` and `{$g$}` being in the same class if `{$ln|f| / ln|g|$}` has a finite
//! non-zero limit. They are `x` or exponentials. They are rewritten as `{$A w^c$}` with `{$w -> 0^+$}` and `A` in
//! a lower class ([`Gruntz::rewrite`]), and the leading term of the series of `f` in `w` decides the limit.

use std::cmp::Ordering;

use malachite::{Rational, base::num::basic::traits::Zero};

use crate::{
    context::{Context, Symbol},
    term::Term,
};

use super::{
    DIGITS, Expr, LimitError, LimitResult, const_sign, depends, fun, infinity, is_infinite,
    only_symbols, series, unary, value, variable,
};
use crate::field::real::approx::approximate;

/// Maximum depth of nested leading term computations.
const MAX_DEPTH: usize = 48;

/// Rational points where coefficients are evaluated to check if they are zero.
const ZERO_TEST_POINTS: [(i64, i64); 3] = [(23, 7), (47, 10), (61, 9)];

/// State of a limit computation at `{$x -> +oo$}`.
pub(super) struct Gruntz {
    /// The variable.
    pub(super) x: Symbol,
    /// The variable of series, `{$w -> 0^+$}`.
    pub(super) w: Symbol,
    /// Depth of nested leading term computations, bounded to avoid hanging.
    depth: usize,
}

impl Gruntz {
    /// A computation of limits when `x` tends to `{$+oo$}`.
    pub(super) fn new(x: Symbol) -> Self {
        Self {
            x,
            // Not a valid identifier, so it can't conflict with a symbol of the expression
            w: Symbol::new("@w"),
            depth: 0,
        }
    }

    /// Whether `term` depends on `x`.
    fn depends(&self, term: &Expr) -> bool {
        depends(term, self.x)
    }

    /// `{$lim_(x -> +oo) f$}`.
    pub(super) fn limit_infinity(&mut self, f: &Expr) -> LimitResult<Expr> {
        if !self.depends(f) {
            return Ok(f.clone());
        }
        let (c0, e0) = self.leadterm(f)?;
        match const_sign(&e0)? {
            Ordering::Greater => Ok(Term::zero(crate::field::real::R)),
            Ordering::Less => match self.sign(&c0)? {
                Ordering::Greater => Ok(infinity()),
                Ordering::Less => Ok(-infinity()),
                Ordering::Equal => Err(LimitError::Unknown),
            },
            Ordering::Equal => self.limit_infinity(&c0),
        }
    }

    /// The sign of `f` when `x` tends to `{$+oo$}`.
    pub(super) fn sign(&mut self, f: &Expr) -> LimitResult<Ordering> {
        if !self.depends(f) {
            return const_sign(f);
        }
        match f {
            Term::Symbol(_) => Ok(Ordering::Greater),
            Term::Mul(mul) => {
                let mut sign = const_sign(&value(mul.coefficient.clone()))?;
                for factor in mul {
                    sign = product_sign(sign, self.sign(factor)?);
                }
                Ok(sign)
            }
            Term::Pow(pow) if !self.depends(&pow.exponant) => {
                let base = self.sign(&pow.base)?;
                match pow.exponant.to_i64() {
                    _ if base == Ordering::Greater => Ok(base),
                    Some(n) if n % 2 == 0 => Ok(product_sign(base, base)),
                    Some(_) => Ok(base),
                    None => Err(LimitError::Unsupported),
                }
            }
            _ if matches!(unary(f), Some((Context::EXP, _))) => Ok(Ordering::Greater),
            _ => {
                let (c0, _) = self.leadterm(f)?;
                self.sign(&c0)
            }
        }
    }

    /// The leading term `{$(c_0, e_0)$}` of `f`, `{$f ~ c_0 w^(e_0)$}` where `w` tends to `{$0^+$}` as fast as the
    /// most rapidly varying subexpressions of `f`, and `{$c_0$}` is in a lower comparability class.
    fn leadterm(&mut self, f: &Expr) -> LimitResult<(Expr, Expr)> {
        if !self.depends(f) {
            return Ok((f.clone(), Term::zero(crate::field::real::R)));
        }
        if self.depth >= MAX_DEPTH {
            return Err(LimitError::Unknown);
        }
        self.depth += 1;
        let res = self.leadterm_inner(f);
        self.depth -= 1;
        res
    }

    fn leadterm_inner(&mut self, f: &Expr) -> LimitResult<(Expr, Expr)> {
        let mut omega = self.mrv(f)?;
        let mut f = f.clone();
        let x = variable(self.x);
        if omega.contains(&x) {
            // Move up, `{$lim_(x -> oo) f(x) = lim_(x -> oo) f(e^x)$}`, so that every element is an exponential.
            // The leading coefficient doesn't need to be moved down, only its limit and sign are used.
            let up = fun(Context::EXP, x);
            let move_up = |term: &Expr| term.substitute(self.x, &up).ok_or(LimitError::Unsupported);
            f = move_up(&f)?;
            omega = omega.iter().map(move_up).collect::<LimitResult<_>>()?;
        }
        let (rewritten, logw) = self.rewrite(&f, &omega)?;
        series::leadterm(self, &rewritten, &logw)
    }

    /// The most rapidly varying subexpressions of `f`.
    fn mrv(&mut self, f: &Expr) -> LimitResult<Vec<Expr>> {
        if !self.depends(f) {
            return Ok(vec![]);
        }
        match f {
            Term::Symbol(_) => Ok(vec![f.clone()]),
            Term::Add(add) => add.iter().try_fold(vec![], |res, term| {
                let omega = self.mrv(term)?;
                self.mrv_max(res, omega)
            }),
            Term::Mul(mul) => mul.iter().try_fold(vec![], |res, factor| {
                let omega = self.mrv(factor)?;
                self.mrv_max(res, omega)
            }),
            Term::Pow(pow) if !self.depends(&pow.exponant) => self.mrv(&pow.base),
            _ => match unary(f) {
                Some((Context::EXP, g)) => {
                    if is_infinite(&self.limit_infinity(g)?) {
                        let omega = self.mrv(g)?;
                        self.mrv_max(vec![f.clone()], omega)
                    } else {
                        self.mrv(g)
                    }
                }
                Some((Context::LN | Context::ABS, g)) => self.mrv(g),
                Some((Context::SIN | Context::COS, g)) => {
                    // Oscillates without a limit, or the limit can't be computed by series
                    if is_infinite(&self.limit_infinity(g)?) {
                        Err(LimitError::Unsupported)
                    } else {
                        self.mrv(g)
                    }
                }
                _ => Err(LimitError::Unsupported),
            },
        }
    }

    /// The most rapidly varying set among `f` and `g`, or their union if they are in the same class.
    fn mrv_max(&mut self, mut f: Vec<Expr>, g: Vec<Expr>) -> LimitResult<Vec<Expr>> {
        if f.is_empty() {
            return Ok(g);
        }
        if g.is_empty() {
            return Ok(f);
        }
        let order = if f.iter().any(|term| g.contains(term)) {
            Ordering::Equal
        } else {
            self.compare(&f[0], &g[0])?
        };
        Ok(match order {
            Ordering::Greater => f,
            Ordering::Less => g,
            Ordering::Equal => {
                for term in g {
                    if !f.contains(&term) {
                        f.push(term);
                    }
                }
                f
            }
        })
    }

    /// Compare the comparability classes of `a` and `b`, with the limit of `{$ln a / ln b$}`.
    fn compare(&mut self, a: &Expr, b: &Expr) -> LimitResult<Ordering> {
        let ratio = self.limit_infinity(&(log(a) / log(b)))?;
        Ok(if ratio.is_zero() {
            Ordering::Less
        } else if is_infinite(&ratio) {
            Ordering::Greater
        } else {
            Ordering::Equal
        })
    }

    /// Rewrite the elements of `omega`, exponentials in the same class, as `{$A w^c$}` in `f`. Returns the
    /// rewritten `f` and the expression of `{$ln w$}`.
    fn rewrite(&mut self, f: &Expr, omega: &[Expr]) -> LimitResult<(Expr, Expr)> {
        let arguments = omega
            .iter()
            .map(|element| match unary(element) {
                Some((Context::EXP, h)) => Ok((element, h)),
                _ => Err(LimitError::Unknown),
            })
            .collect::<LimitResult<Vec<_>>>()?;
        // The smallest element doesn't contain the others, so `w` is expressed in `x` only
        let (_, h) = *arguments
            .iter()
            .min_by_key(|(element, _)| size(element))
            .ok_or(LimitError::Unknown)?;
        // `{$g = e^h$}`, `{$w = g$}` if `{$h -> -oo$}`, `{$w = 1/g$}` if `{$h -> +oo$}`
        let (w_sign, logw) = match self.sign(h)? {
            Ordering::Greater => (-1, -h),
            Ordering::Less => (1, h.clone()),
            Ordering::Equal => return Err(LimitError::Unknown),
        };
        let mut replacements = vec![];
        for (element, k) in arguments {
            // `{$e^k = e^(k - c h) g^c$}` with `{$c = lim k / h$}`
            let c = self.limit_infinity(&(k / h))?;
            if is_infinite(&c) || self.depends(&c) {
                return Err(LimitError::Unknown);
            }
            replacements.push((element, k, c));
        }
        let w = variable(self.w);
        let res = self.replace(f, &replacements, h, &w, w_sign)?;
        Ok((res, logw))
    }

    /// Replace each `{$e^k$}` of `replacements` by `{$e^(k - c h) w^(plus.minus c)$}` in `f`.
    fn replace(
        &self,
        f: &Expr,
        replacements: &[(&Expr, &Expr, Expr)],
        h: &Expr,
        w: &Expr,
        w_sign: i64,
    ) -> LimitResult<Expr> {
        if !self.depends(f) {
            return Ok(f.clone());
        }
        let replace = |term: &Expr| self.replace(term, replacements, h, w, w_sign);
        if let Some((_, k, c)) = replacements.iter().find(|(element, _, _)| *element == f) {
            let argument = replace(k)? - c * h;
            return Ok(fun(Context::EXP, argument) * w.pow(&(c * &value(Rational::from(w_sign)))));
        }
        Ok(match f {
            Term::Value(_) | Term::Symbol(_) => f.clone(),
            Term::Add(add) => add
                .iter()
                .try_fold(Term::zero(crate::field::real::R), |res, term| {
                    Ok::<_, LimitError>(res + replace(term)?)
                })?,
            Term::Mul(mul) => mul
                .iter()
                .try_fold(value(mul.coefficient.clone()), |res, factor| {
                    Ok::<_, LimitError>(res * replace(factor)?)
                })?,
            Term::Pow(pow) => replace(&pow.base)?.pow(&pow.exponant),
            Term::Fun(_) => {
                let (ident, arg) = unary(f).ok_or(LimitError::Unsupported)?;
                fun(ident, replace(arg)?)
            }
        })
    }

    /// Whether the coefficient `c`, free of `w`, is zero. Coefficients depending only on `x` are evaluated at a
    /// few points, other symbols are assumed generic.
    pub(super) fn is_zero(&self, c: &Expr) -> bool {
        if c.is_zero() || c.simplify().is_zero() {
            return true;
        }
        if !only_symbols(c, &[self.x]) {
            return false;
        }
        if !self.depends(c) {
            return approximate(c, DIGITS).is_some_and(|value| value == Rational::ZERO);
        }
        let mut evaluated = false;
        for (num, den) in ZERO_TEST_POINTS {
            let point = value(Rational::from_signeds(num, den));
            if let Some(value) = c
                .substitute(self.x, &point)
                .and_then(|c| approximate(&c, DIGITS))
            {
                if value != Rational::ZERO {
                    return false;
                }
                evaluated = true;
            }
        }
        evaluated
    }
}

/// `{$ln a$}`, simplifying `{$ln e^h = h$}`.
fn log(a: &Expr) -> Expr {
    match unary(a) {
        Some((Context::EXP, h)) => h.clone(),
        _ => fun(Context::LN, a.clone()),
    }
}

/// The sign of a product.
fn product_sign(a: Ordering, b: Ordering) -> Ordering {
    match (a, b) {
        (Ordering::Equal, _) | (_, Ordering::Equal) => Ordering::Equal,
        _ if a == b => Ordering::Greater,
        _ => Ordering::Less,
    }
}

/// Number of nodes of a term.
fn size(term: &Expr) -> usize {
    1 + match term {
        Term::Value(_) | Term::Symbol(_) => 0,
        Term::Add(add) => add.iter().map(size).sum(),
        Term::Mul(mul) => mul.iter().map(size).sum(),
        Term::Pow(pow) => size(&pow.base) + size(&pow.exponant),
        Term::Fun(_) => unary(term).map_or(0, |(_, arg)| size(arg)),
    }
}
