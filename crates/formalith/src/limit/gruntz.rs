//! The Gruntz algorithm, computing limits at `{$+oo$}` (Dominik Gruntz, "On Computing Limits in a Symbolic
//! Manipulation System", 1996).
//!
//! The most rapidly varying subexpressions of `f` ([`Gruntz::mrv`]) are its subexpressions `{$g$}` in the
//! greatest comparability class, `{$f$}` and `{$g$}` being in the same class if `{$ln|f| / ln|g|$}` has a finite
//! non-zero limit. They are `x` or exponentials. They are rewritten as `{$A w^c$}` with `{$w -> 0^+$}` and `A` in
//! a lower class ([`Gruntz::rewrite`]), and the leading term of the series of `f` in `w` decides the limit.

use crate::field::real::expr::try_map_operands;
use crate::field::real::expr::{
    DIGITS, Expr, depends, fun, half, infinity, is_infinite, one, polygamma, polygamma_args, size,
    unary, value, variable, zero,
};
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
    LimitError, LimitResult,
    bounds::{angles, bounds, has_angle},
    const_sign, only_symbols, series,
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
    /// limits, it supports oscillating `sin` and `cos`, `{$Gamma(g)$}` with `{$g -> -oo$}` (see
    /// [`Self::reflect_gamma`]), and gives limits like `{$sign(a) oo$}` for a parameter `a`.
    pub(super) fn limit(&mut self, f: &Expr) -> LimitResult<Expr> {
        let f = self.reflect_gamma(f)?;
        let f = self.remove_oscillations(&f)?;
        if let Err(error) = self.check_bounded(&f) {
            return Err(if self.accumulating_poles(&f) {
                LimitError::Undefined
            } else {
                error
            });
        }
        let mut f = f;
        let res = loop {
            if !self.depends(&f) {
                break f;
            }
            let (c0, e0) = self.leadterm(&f)?;
            match const_sign(&e0)? {
                Ordering::Greater => break zero(),
                Ordering::Less => return Ok((self.top_sign(&c0)? * infinity()).normalize()),
                Ordering::Equal => f = c0,
            }
        };
        Self::without_angles(&res).map(|res| res.normalize())
    }

    /// Rewrite each `{$Gamma(g)$}` with `{$g -> -oo$}` in `f` by the reflection formula
    /// `{$Gamma(g) = pi / (sin(pi g) Gamma(1 - g))$}`, so that `{$Gamma(1 - g)$}` is rewritten by Stirling's
    /// formula and `{$sin(pi g)$}` gets an angle.
    fn reflect_gamma(&mut self, f: &Expr) -> LimitResult<Expr> {
        if !self.depends(f) {
            return Ok(f.clone());
        }
        Ok(match f {
            Term::Pow(pow) => self.reflect_gamma(&pow.base)?.pow(&pow.exponant),
            Term::Fun(_) if polygamma_args(f).is_some() => {
                let (m, arg) = polygamma_args(f).ok_or(LimitError::Unsupported)?;
                polygamma(m, self.reflect_gamma(arg)?)
            }
            Term::Fun(_) => {
                let (ident, arg) = unary(f).ok_or(LimitError::Unsupported)?;
                let arg = self.reflect_gamma(arg)?;
                if ident == Context::GAMMA && self.limit_infinity(&arg)? == -infinity() {
                    let pi = variable(Context::PI);
                    let sin = fun(Context::SIN, &pi * &arg);
                    return Ok(pi / (sin * fun(Context::GAMMA, one() - arg)));
                }
                fun(ident, arg)
            }
            _ => try_map_operands(f, |operand| self.reflect_gamma(operand))?,
        })
    }

    /// Whether `f`, rejected by [`Self::check_bounded`], has poles accumulating at `{$+oo$}` around which it is
    /// unbounded without tending to `{$plus.minus oo$}`, so that its limit doesn't exist: its denominator has a
    /// factor `{$D^n$}`, `D` being `{$sin u$}` or `{$cos u$}` for `u` linear in a single angle `t`, and the rest
    /// `A` of `f` doesn't vanish at the zeros `{$t_0$}` of `D` for large `x`. For an odd `n`, `f` changes sign
    /// across each pole; for an even `n`, `A` must have a finite limit, so that `f` stays bounded between the
    /// poles (`{$x / sin(x)^2 -> oo$}` on its domain).
    fn accumulating_poles(&mut self, f: &Expr) -> bool {
        let (num, den) = f.as_fraction(true);
        let factors = match &den {
            Term::Mul(mul) => mul.iter().cloned().collect(),
            _ => vec![den.clone()],
        };
        factors.iter().any(|factor| {
            let (base, n) = match factor {
                Term::Pow(pow) => match pow.exponant.to_i64() {
                    Some(n) if n > 0 => (&*pow.base, n),
                    _ => return false,
                },
                _ => (factor, 1),
            };
            self.pole_of(&num, &den, base, n).unwrap_or(false)
        })
    }

    /// Whether the factor `{$D^n$}` of the denominator `den` of `{$f = "num" / "den"$}` gives poles where `f` is
    /// unbounded, see [`Self::accumulating_poles`]. `None` when it can't be decided.
    fn pole_of(&mut self, num: &Expr, den: &Expr, d: &Expr, n: i64) -> Option<bool> {
        let (ident @ (Context::SIN | Context::COS), u) = unary(d)? else {
            return None;
        };
        let [t] = angles(u)[..] else {
            return None;
        };
        if self.depends(u) {
            return None;
        }
        // `{$u = k t + c$}`
        let c = u.substitute(t, &zero())?;
        let k = &u.substitute(t, &one())? - &c;
        if has_angle(&c)
            || has_angle(&k)
            || k.is_zero()
            || !(u - &(&k * &variable(t) + &c)).simplify().is_zero()
        {
            return None;
        }
        let root = if ident == Context::SIN {
            zero()
        } else {
            variable(Context::PI) * half()
        };
        let t0 = (root - c) / k;
        let rest = num * &(d.pow(&value(Rational::from(n))) / den);
        self.check_bounded(&rest).ok()?;
        let at_pole = rest.substitute(t, &t0)?;
        if has_angle(&at_pole) {
            return None;
        }
        let (c0, _) = self.leadterm(&at_pole).ok()?;
        if self.is_zero(&c0) {
            return None;
        }
        Some(n % 2 == 1 || !is_infinite(&self.limit_infinity(&rest).ok()?))
    }

    /// Replace the arguments `g` of `{$sin g$}` and `{$cos g$}` tending to `{$plus.minus oo$}` by angles.
    fn remove_oscillations(&mut self, f: &Expr) -> LimitResult<Expr> {
        if !self.depends(f) {
            return Ok(f.clone());
        }
        Ok(match f {
            Term::Fun(_) if unary(f).is_some() => {
                let (ident, arg) = unary(f).ok_or(LimitError::Unsupported)?;
                let arg = self.remove_oscillations(arg)?;
                if matches!(ident, Context::SIN | Context::COS) && self.tends_to_infinity(&arg)? {
                    let angle = self.angle(&arg);
                    fun(ident, angle)
                } else if matches!(ident, Context::SI | Context::CI)
                    && self.tends_to_infinity(&arg)?
                {
                    self.trigonometric_integral_at_infinity(ident, arg)?
                } else {
                    fun(ident, arg)
                }
            }
            _ => try_map_operands(f, |operand| self.remove_oscillations(operand))?,
        })
    }

    /// `{$"Si"(g)$}` or `{$"Ci"(g)$}` for `{$|g| -> oo$}`, written with an angle `t` in place of `g` as
    /// `{$"Si"(g) = plus.minus pi/2 - f(g) cos t - g(g) sin t$}` (`{$g -> plus.minus oo$}`) and
    /// `{$"Ci"(g) = f(g) sin t - g(g) cos t$}` (`{$g -> oo$}` only), the auxiliary functions [`sif`] and [`sig`]
    /// having asymptotic series.
    fn trigonometric_integral_at_infinity(&mut self, ident: Symbol, g: Expr) -> LimitResult<Expr> {
        let limit = self.limit_infinity(&g)?;
        let sign = if limit == infinity() {
            one()
        } else if limit == -infinity() && ident == Context::SI {
            -one()
        } else {
            return Err(LimitError::Unsupported);
        };
        let angle = self.angle(&g);
        let (sine, cosine) = (fun(Context::SIN, angle.clone()), fun(Context::COS, angle));
        let (f, h) = (fun(sif(), g.clone()), fun(sig(), g));
        Ok(if ident == Context::SI {
            sign * variable(Context::PI) * half() - f * cosine - h * sine
        } else {
            f * sine - h * cosine
        })
    }

    /// Whether `{$|g| -> oo$}`. Unlike the limit of `g`, it doesn't need the sign of its leading coefficient, so
    /// `{$t x$}` tends to infinity for a parameter `t`.
    fn tends_to_infinity(&mut self, g: &Expr) -> LimitResult<bool> {
        if !self.depends(g) {
            return Ok(false);
        }
        let (_, e0) = self.leadterm(g)?;
        Ok(const_sign(&e0)? == Ordering::Less)
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
            Term::Fun(_) if polygamma_args(f).is_some() => {
                let (_, arg) = polygamma_args(f).ok_or(LimitError::Unsupported)?;
                self.check_bounded(arg)
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
    fn without_angles(res: &Expr) -> LimitResult<Expr> {
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
            Ok(zero())
        } else if constant {
            angles
                .iter()
                .try_fold(res.clone(), |res, t| res.substitute(*t, &zero()))
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
    fn limit_infinity(&mut self, f: &Expr) -> LimitResult<Expr> {
        if !self.depends(f) {
            return Ok(f.clone());
        }
        let (c0, e0) = self.leadterm(f)?;
        match const_sign(&e0)? {
            Ordering::Greater => Ok(zero()),
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
            return Ok((f.clone(), zero()));
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
        let mut f = self.special_at_infinity(f)?;
        if !self.depends(&f) {
            // The rebuilt expression may normalize to a constant
            return Ok((f, zero()));
        }
        let mut omega = self.mrv(&f)?;
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

    /// Rewrite each `{$"erf" g$}` with `{$g -> plus.minus oo$}` in `f` as
    /// `{$plus.minus (1 - e^(-g^2) "erfcx"(plus.minus g))$}`, and each `{$"erfi" g$}` as
    /// `{$plus.minus e^(g^2) "erfix"(plus.minus g)$}`, so that the exponentials are seen by [`Self::mrv`] and
    /// `{$"erfcx"$}` (see [`erfcx`]) and `{$"erfix"$}` (see [`erfix`]) have asymptotic series. Each `{$Gamma(g)$}`
    /// with `{$g -> oo$}` is rewritten by Stirling's formula
    /// `{$Gamma(g) = exp((g - 1/2) ln g - g + ln(2 pi)/2 + "lgammastar"(g))$}` (see [`lgammastar`]).
    fn special_at_infinity(&mut self, f: &Expr) -> LimitResult<Expr> {
        if !self.depends(f) {
            return Ok(f.clone());
        }
        Ok(match f {
            Term::Pow(pow) => self.special_at_infinity(&pow.base)?.pow(&pow.exponant),
            Term::Fun(_) if polygamma_args(f).is_some() => {
                let (m, arg) = polygamma_args(f).ok_or(LimitError::Unsupported)?;
                polygamma(m, self.special_at_infinity(arg)?)
            }
            Term::Fun(_) => {
                let (ident, arg) = unary(f).ok_or(LimitError::Unsupported)?;
                let arg = self.special_at_infinity(arg)?;
                if ident == Context::GAMMA {
                    let limit = self.limit_infinity(&arg)?;
                    if limit == -infinity() {
                        // Poles accumulate at `{$-oo$}`, only rewritten at the top level by
                        // `Self::reflect_gamma`
                        return Err(LimitError::Unsupported);
                    }
                    if limit == infinity() {
                        let two_pi = value(Rational::from(2)) * variable(Context::PI);
                        let exponant = (&arg - &half()) * fun(Context::LN, arg.clone())
                            - arg.clone()
                            + fun(Context::LN, two_pi) * half()
                            + fun(lgammastar(), arg);
                        return Ok(fun(Context::EXP, exponant));
                    }
                }
                if ident == Context::EI && is_infinite(&self.limit_infinity(&arg)?) {
                    // `{$"Ei"(g) = e^g "eistar"(g)$}`
                    return Ok(fun(Context::EXP, arg.clone()) * fun(eistar(), arg));
                }
                if matches!(ident, Context::ERF | Context::ERFI) {
                    let limit = self.limit_infinity(&arg)?;
                    if is_infinite(&limit) {
                        let sign = if limit == infinity() { one() } else { -one() };
                        let square = &arg * &arg;
                        return Ok(if ident == Context::ERF {
                            let decay = fun(Context::EXP, -square);
                            &sign * &(one() - decay * fun(erfcx(), &sign * &arg))
                        } else {
                            &sign * &(fun(Context::EXP, square) * fun(erfix(), &sign * &arg))
                        });
                    }
                }
                fun(ident, arg)
            }
            _ => try_map_operands(f, |operand| self.special_at_infinity(operand))?,
        })
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
                Some((
                    Context::LN | Context::ABS | Context::ATAN | Context::ERF | Context::ERFI,
                    g,
                )) => self.mrv(g),
                Some((ident, g))
                    if ident == erfcx()
                        || ident == erfix()
                        || ident == lgammastar()
                        || ident == sif()
                        || ident == sig()
                        || ident == eistar() =>
                {
                    self.mrv(g)
                }
                // Unbounded arguments were rewritten, like `{$Gamma g$}` with `{$g -> oo$}`, and
                // `{$psi^((m))(g)$}` has a series
                Some((Context::SI | Context::CI | Context::EI | Context::GAMMA, g)) => self.mrv(g),
                None if polygamma_args(f).is_some() => {
                    let (_, g) = polygamma_args(f).ok_or(LimitError::Unsupported)?;
                    self.mrv(g)
                }
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
        if let Some((Context::EXP, k)) = unary(f) {
            // `{$e^(r k) = (e^k)^r$}` for a rational `r`, as powers of exponentials normalize to exponentials
            // (`{$x^2$}` becomes `{$e^(2 x)$}` when moved up)
            for (element, element_k, _) in replacements {
                if let Term::Value(ratio) = k / *element_k {
                    return Ok(replace(element)?.pow(&Term::Value(ratio)));
                }
            }
        }
        Ok(match f {
            Term::Pow(pow) => replace(&pow.base)?.pow(&pow.exponant),
            _ => try_map_operands(f, replace)?,
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
        // Polynomials and rational functions are zero when their expanded numerator is
        let (numerator, _) = c.as_fraction(true);
        let numerator = crate::term::Expand::expand(&numerator);
        if numerator.is_zero() {
            return true;
        }
        if is_polynomial(&numerator) {
            return false;
        }
        // Points depending on `c`, so that a coefficient can't vanish at all of them by construction
        let mut state = std::hash::DefaultHasher::new();
        std::hash::Hash::hash(&format!("{c:?}"), &mut state);
        let hash = std::hash::Hasher::finish(&state);
        let points = (0..3).map(|k| {
            let bits = (hash >> (16 * k)) & 0xffff;
            (3 + i64::try_from(bits % 4096).unwrap_or(0), 997)
        });
        let mut evaluated = false;
        for (num, den) in ZERO_TEST_POINTS.into_iter().chain(points) {
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

/// Whether `term` is a polynomial in its symbols with rational coefficients: sums and products of symbols and
/// their natural powers.
fn is_polynomial(term: &Expr) -> bool {
    match term {
        Term::Value(_) | Term::Symbol(_) => true,
        Term::Add(add) => add.iter().all(is_polynomial),
        Term::Mul(mul) => mul.iter().all(is_polynomial),
        Term::Pow(pow) => {
            matches!(&*pow.base, Term::Symbol(_))
                && matches!(&**pow.exponant, Term::Value(e) if e.value > 0 && e.value.denominator_ref() == &1u32)
        }
        Term::Fun(_) => false,
    }
}

/// The scaled complementary error function `{$"erfcx"(g) = e^(g^2) (1 - "erf" g)$}`, only used internally for
/// `{$g -> +oo$}`.
pub(super) fn erfcx() -> Symbol {
    Symbol::new("@erfcx")
}

/// The scaled imaginary error function `{$"erfix"(g) = e^(-g^2) "erfi" g$}`, only used internally for
/// `{$g -> +oo$}`.
pub(super) fn erfix() -> Symbol {
    Symbol::new("@erfix")
}

/// The remainder of Stirling's formula `{$"lgammastar"(g) = ln Gamma(g) - (g - 1/2) ln g + g - ln(2 pi)/2$}`, only
/// used internally for `{$g -> +oo$}`.
pub(super) fn lgammastar() -> Symbol {
    Symbol::new("@lgammastar")
}

/// The auxiliary function `{$f(g) = "Ci"(g) sin g + (pi/2 - "Si"(g)) cos g$}` of the sine and cosine integrals,
/// with the asymptotic series `{$sum_k (-1)^k (2 k)! / g^(2 k + 1)$}`, only used internally for `{$|g| -> oo$}`.
pub(super) fn sif() -> Symbol {
    Symbol::new("@sif")
}

/// The auxiliary function `{$g(g) = -"Ci"(g) cos g + (pi/2 - "Si"(g)) sin g$}` of the sine and cosine integrals,
/// with the asymptotic series `{$sum_k (-1)^k (2 k + 1)! / g^(2 k + 2)$}`, only used internally for `{$|g| -> oo$}`.
pub(super) fn sig() -> Symbol {
    Symbol::new("@sig")
}

/// The scaled exponential integral `{$"eistar"(g) = e^(-g) "Ei"(g)$}`, with the asymptotic series
/// `{$sum_(k >= 1) (k - 1)! / g^k$}`, only used internally for `{$|g| -> oo$}`.
pub(super) fn eistar() -> Symbol {
    Symbol::new("@eistar")
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

/// The sign of a constant `c` depending on parameters, assumed non-zero, as a product of `{$sign(a)$}`, `sign`
/// being evaluated for parameters with sign assumptions.
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
