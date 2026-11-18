//! The Gruntz algorithm, computing limits at `{$+oo$}` (Dominik Gruntz, "On Computing Limits in a Symbolic
//! Manipulation System", 1996).
//!
//! The most rapidly varying subexpressions of `f` ([`Gruntz::mrv`]) are its subexpressions `{$g$}` in the
//! greatest comparability class, `{$f$}` and `{$g$}` being in the same class if `{$ln|f| / ln|g|$}` has a finite
//! non-zero limit. They are `x` or exponentials. They are rewritten as `{$A w^c$}` with `{$w -> 0^+$}` and `A` in
//! a lower class ([`Gruntz::rewrite`]), and the leading term of the series of `f` in `w` decides the limit.

use std::cmp::Ordering;

use malachite::{
    Rational,
    base::num::{arithmetic::traits::Sign, basic::traits::Zero},
};

use crate::{
    context::{Context, Symbol},
    term::{Normalize, Term},
};

use super::{
    DIGITS, Expr, LimitError, LimitResult,
    bounds::{angles, bounds, has_angle},
    const_sign, depends, fun, infinity, is_infinite, one, only_symbols, series, unary, value,
    variable,
};
use crate::field::real::approx::{approximate, approximate_fixed};

/// Maximum depth of nested leading term computations.
const MAX_DEPTH: usize = 48;

/// Rational points where coefficients are evaluated to check if they are zero.
const ZERO_TEST_POINTS: [(i64, i64); 3] = [(23, 7), (47, 10), (61, 9)];

/// Number of values of the angles where a result is evaluated, to check if it depends on them.
const ANGLE_SAMPLES: i64 = 16;

/// Absolute precision, in bits, of the evaluations at angle samples.
const SAMPLE_BITS: u64 = 128;

/// The value of the `i`-th angle at the `j`-th sample, spread over more than a period.
fn angle_sample(i: usize, j: i64) -> Expr {
    let i = i64::try_from(i).unwrap_or(0);
    value(Rational::from_signeds(14 * j + 5 * i + 3, 35))
}

/// State of a limit computation at `{$x -> +oo$}`.
pub(super) struct Gruntz {
    /// The variable.
    pub(super) x: Symbol,
    /// The variable of series, `{$w -> 0^+$}`.
    pub(super) w: Symbol,
    /// Depth of nested leading term computations, bounded to avoid hanging.
    depth: usize,
    /// Angles replacing the arguments of oscillating `sin` and `cos`, with the argument they replace.
    angles: Vec<(Symbol, Expr)>,
}

impl Gruntz {
    /// A computation of limits when `x` tends to `{$+oo$}`.
    pub(super) fn new(x: Symbol) -> Self {
        Self {
            x,
            // Not a valid identifier, so it can't conflict with a symbol of the expression
            w: Symbol::new("@w"),
            depth: 0,
            angles: vec![],
        }
    }

    /// `{$lim_(x -> +oo) f$}`, the entry point. Unlike [`Gruntz::limit_infinity`], used for the intermediate
    /// limits, it supports oscillating `sin` and `cos`, and gives limits like `{$sign(a) oo$}` for a parameter `a`.
    pub(super) fn limit(&mut self, f: &Expr) -> LimitResult<Expr> {
        let f = self.remove_oscillations(f)?;
        self.check_bounded(&f)?;
        let mut f = f;
        let res = loop {
            if !self.depends(&f) {
                break f;
            }
            let (c0, e0) = self.leadterm(&f)?;
            match const_sign(&e0)? {
                Ordering::Greater => break Term::zero(crate::field::real::R),
                Ordering::Less => return Ok((self.top_sign(&c0)? * infinity()).normalize()),
                Ordering::Equal => f = c0,
            }
        };
        self.without_angles(&res).map(|res| res.normalize())
    }

    /// Replace the arguments `g` of `{$sin g$}` and `{$cos g$}` tending to `{$plus.minus oo$}` by angles.
    fn remove_oscillations(&mut self, f: &Expr) -> LimitResult<Expr> {
        if !self.depends(f) {
            return Ok(f.clone());
        }
        Ok(match f {
            Term::Value(_) | Term::Symbol(_) => f.clone(),
            Term::Add(add) => add
                .iter()
                .try_fold(Term::zero(crate::field::real::R), |res, term| {
                    Ok::<_, LimitError>(res + self.remove_oscillations(term)?)
                })?,
            Term::Mul(mul) => mul
                .iter()
                .try_fold(value(mul.coefficient.clone()), |res, factor| {
                    Ok::<_, LimitError>(res * self.remove_oscillations(factor)?)
                })?,
            Term::Pow(pow) => {
                let base = self.remove_oscillations(&pow.base)?;
                base.pow(&self.remove_oscillations(&pow.exponant)?)
            }
            Term::Fun(_) => {
                let (ident, arg) = unary(f).ok_or(LimitError::Unsupported)?;
                let arg = self.remove_oscillations(arg)?;
                if matches!(ident, Context::SIN | Context::COS)
                    && is_infinite(&self.limit_infinity(&arg)?)
                {
                    let angle = self.angle(&arg);
                    fun(ident, angle)
                } else {
                    fun(ident, arg)
                }
            }
        })
    }

    /// The angle replacing `g`, `{$k t + d$}` if `{$g ~ k g_t + d$}` for the argument `{$g_t$}` of an angle `t`
    /// and a rational `k`, a new angle otherwise.
    fn angle(&mut self, g: &Expr) -> Expr {
        for (t, h) in self.angles.clone() {
            if let Ok(k @ Term::Value(_)) = self.limit_infinity(&(g / &h)).map(|k| k.normalize())
                && !k.is_zero()
                && let Ok(d) = self.limit_infinity(&(g - &(&k * &h)))
                && !is_infinite(&d)
                && !self.depends(&d)
            {
                return k * variable(t) + d;
            }
        }
        let t = Symbol::new(format!("@t{}", self.angles.len()));
        self.angles.push((t, g.clone()));
        variable(t)
    }

    /// Check that the divisions, logarithms and roots of terms containing angles are bounded away from zero, so
    /// that leading terms computed with angles as constants hold for every value of the angles.
    fn check_bounded(&mut self, f: &Expr) -> LimitResult<()> {
        if !has_angle(f) {
            return Ok(());
        }
        let away_from_zero = |this: &mut Self, u: &Expr, positive: bool| {
            if !has_angle(u) {
                return Ok(());
            }
            let limit = this.limit_infinity(u)?;
            let bounded = if this.depends(&limit) {
                false
            } else if is_infinite(&limit) {
                true
            } else {
                bounds(&limit).is_some_and(|(lo, hi)| {
                    lo > Rational::ZERO || (!positive && hi < Rational::ZERO)
                })
            };
            if bounded {
                Ok(())
            } else {
                Err(LimitError::Unknown)
            }
        };
        match f {
            Term::Value(_) | Term::Symbol(_) => Ok(()),
            Term::Add(add) => add.iter().try_for_each(|term| self.check_bounded(term)),
            Term::Mul(mul) => mul.iter().try_for_each(|factor| self.check_bounded(factor)),
            Term::Pow(pow) => {
                self.check_bounded(&pow.base)?;
                self.check_bounded(&pow.exponant)?;
                match pow.exponant.to_i64() {
                    Some(n) if n >= 0 => Ok(()),
                    n => away_from_zero(self, &pow.base, n.is_none()),
                }
            }
            Term::Fun(_) => {
                let (ident, arg) = unary(f).ok_or(LimitError::Unsupported)?;
                self.check_bounded(arg)?;
                if ident == Context::LN {
                    away_from_zero(self, arg, true)
                } else {
                    Ok(())
                }
            }
        }
    }

    /// The sign of an infinite limit `{$c w^e$}`, `{$e < 0$}`: `{$plus.minus 1$}`, or `{$sign$}` of parameters.
    fn top_sign(&mut self, c: &Expr) -> LimitResult<Expr> {
        if self.depends(c) {
            if let Ok(sign) = self.sign(c) {
                return sign_value(sign);
            }
            let (c0, _) = self.leadterm(c)?;
            return self.top_sign(&c0);
        }
        if let Ok(sign) = const_sign(c) {
            return sign_value(sign);
        }
        if has_angle(c) {
            // Positive and negative for some angles: oscillates between `{$+oo$}` and `{$-oo$}`
            if let [t] = angles(c).as_slice()
                && only_symbols(c, &[*t])
            {
                let signs: Vec<_> = (0..ANGLE_SAMPLES)
                    .filter_map(|j| {
                        approximate_fixed(&c.substitute(*t, &angle_sample(0, j))?, SAMPLE_BITS)
                    })
                    .map(|value| value.sign())
                    .collect();
                if signs.contains(&Ordering::Greater) && signs.contains(&Ordering::Less) {
                    return Err(LimitError::Undefined);
                }
            }
            return Err(LimitError::Unknown);
        }
        if only_symbols(c, &[]) {
            return Err(LimitError::Unknown);
        }
        Ok(param_sign(c))
    }

    /// `res` if it doesn't depend on the angles. A result taking several values for a single angle doesn't exist.
    fn without_angles(&self, res: &Expr) -> LimitResult<Expr> {
        let angles = angles(res);
        if angles.is_empty() {
            return Ok(res.clone());
        }
        let at = |j: i64| {
            angles
                .iter()
                .enumerate()
                .try_fold(res.clone(), |res, (i, t)| {
                    res.substitute(*t, &angle_sample(i, j))
                })
        };
        let samples = (0..ANGLE_SAMPLES)
            .map(|j| at(j).and_then(|res| approximate_fixed(&res, SAMPLE_BITS)))
            .collect::<Option<Vec<_>>>()
            .ok_or(LimitError::Unknown)?;
        let tolerance = Rational::from_signeds(1, 1_000_000_000_000_000_000_i64);
        let small = |value: &Rational| *value < tolerance && -value < tolerance;
        let constant = samples.iter().all(|sample| small(&(sample - &samples[0])));
        if constant && small(&samples[0]) {
            Ok(Term::zero(crate::field::real::R))
        } else if constant {
            angles
                .iter()
                .try_fold(res.clone(), |res, t| {
                    res.substitute(*t, &Term::zero(crate::field::real::R))
                })
                .map(|res| res.simplify())
                .ok_or(LimitError::Unknown)
        } else if angles.len() == 1 && only_symbols(res, &angles) {
            Err(LimitError::Undefined)
        } else {
            Err(LimitError::Unknown)
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
                Some((Context::LN | Context::ABS | Context::ATAN, g)) => self.mrv(g),
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
            if is_infinite(&c) || self.depends(&c) || has_angle(&c) {
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
        // Angles are generic constants too, evaluated at the test points
        let mut symbols = angles(c);
        if self.depends(c) {
            symbols.push(self.x);
        }
        if !only_symbols(c, &symbols) {
            return false;
        }
        if symbols.is_empty() {
            return approximate(c, DIGITS).is_some_and(|value| value == Rational::ZERO);
        }
        let mut evaluated = false;
        for (num, den) in ZERO_TEST_POINTS {
            let at = symbols
                .iter()
                .zip(1..)
                .try_fold(c.clone(), |c, (symbol, i)| {
                    c.substitute(*symbol, &value(Rational::from_signeds(num + 3 * i, den)))
                });
            if let Some(value) = at.and_then(|c| approximate(&c, DIGITS)) {
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

/// The sign `{$plus.minus 1$}` as a term, failing on 0.
fn sign_value(sign: Ordering) -> LimitResult<Expr> {
    match sign {
        Ordering::Equal => Err(LimitError::Unknown),
        _ => Ok(value(Rational::from(sign as i8))),
    }
}

/// The sign of a constant `c` depending on parameters, assumed non-zero, as a product of `{$sign(a)$}`.
fn param_sign(c: &Expr) -> Expr {
    if let Ok(sign) = const_sign(c)
        && sign != Ordering::Equal
    {
        return value(Rational::from(sign as i8));
    }
    match c {
        Term::Mul(mul) => mul.iter().fold(
            param_sign(&value(mul.coefficient.clone())),
            |res, factor| res * param_sign(factor),
        ),
        Term::Pow(pow) => match pow.exponant.to_i64() {
            Some(n) if n % 2 == 0 => one(),
            Some(_) => param_sign(&pow.base),
            None => fun(Context::SIGN, c.clone()),
        },
        _ if matches!(unary(c), Some((Context::EXP, _))) => one(),
        _ => fun(Context::SIGN, c.clone()),
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
