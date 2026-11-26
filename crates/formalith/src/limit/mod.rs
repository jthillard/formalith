//! Limits of real expressions, `lim(f, x, a)`, computed with the Gruntz algorithm.
//!
//! Every limit is reduced to a limit at `{$+oo$}`: `{$x -> a^+$}` becomes `{$x -> a + 1/x$}`, `{$x -> a^-$}`
//! becomes `{$x -> a - 1/x$}` and `{$x -> -oo$}` becomes `{$x -> -x$}`. Two-sided limits compute both sides.
//! Powers with a variable exponent are first rewritten as `{$b^g = exp(g ln b)$}`, and `tan` as `sin / cos`.
//!
//! At `{$+oo$}`, the Gruntz algorithm finds the most rapidly varying subexpressions of `f`, rewrites
//! them as powers of a single `{$w -> 0^+$}`, and takes the leading term `{$c_0 w^(e_0)$}` of the series of `f`
//! in `w`. The limit is 0 if `{$e_0 > 0$}`, `{$plus.minus oo$}` if `{$e_0 < 0$}`, and the limit of
//! `{$c_0$}`, which varies less rapidly, otherwise. It is complete for expressions built with `exp` and `ln`.
//! `min`, `max` and `sign` are rewritten with `abs`. `floor` and `ceil` are replaced by their constant value near
//! the point, from the limit of their argument.
//!
//! `{$sin g$}` and `{$cos g$}` with `{$g -> plus.minus oo$}` oscillate: `g` is replaced by an angle `{$theta$}`, a
//! constant for the algorithm, after checking that the expression stays bounded away from its singularities for
//! every `{$theta$}`. A result depending on `{$theta$}` means that the limit doesn't exist, and so do poles of
//! `{$1/sin theta$}` accumulating at infinity (`{$tan x$}` at `{$oo$}`). `{$Gamma(g)$}` with `{$g -> -oo$}` is
//! rewritten by the reflection formula `{$Gamma(g) = pi / (sin(pi g) Gamma(1 - g))$}`. A limit whose sign
//! depends on parameters is `{$sign(a) oo$}`.
//!
//! The same series give expansions `series(f, x, a, n)`, see [`Term::series`].
//!
//! ```
//! use formalith::{field::real::R, parse};
//!
//! assert_eq!(parse!("lim(sin(x)/x, x, 0)", R), parse!("1", R));
//! assert_eq!(parse!("lim(sin(x)/x, x, oo)", R), parse!("0", R));
//! assert_eq!(parse!("lim((1 + 1/x)^x, x, oo)", R), parse!("exp(1)", R));
//! assert_eq!(parse!("lim(1/x, x, 0, -1)", R), parse!("-oo", R));
//! assert_eq!(parse!("lim(1/x, x, 0)", R), parse!("undefined", R));
//! ```

mod bounds;
mod expansion;
pub(crate) use expansion::{remainder, series_terms};
mod gruntz;
mod series;

use std::{cmp::Ordering, error::Error, fmt};

use malachite::{
    Rational,
    base::num::{arithmetic::traits::Floor, basic::traits::One},
};

use crate::{
    context::{Context, Symbol},
    field::real::{
        R,
        approx::approximate,
        expr::{
            DIGITS, Expr, Real, constant_sign, depends, fun, gamma_pole, half,
            has_special_constant, hyperbolic_as_exp, infinity, infinity_sign, one, polygamma,
            polygamma_args, sqrt, try_map_operands, unary, value, variable, zero,
        },
        sign::{SignMode, sign},
    },
    term::{Fun, Normalize, Term},
};

use gruntz::Gruntz;

/// The side from which the limit point is approached.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Direction {
    /// Two-sided limit, both sides must agree.
    Both,
    /// Right limit `{$x -> a^+$}`.
    Right,
    /// Left limit `{$x -> a^-$}`.
    Left,
}

impl Direction {
    /// The direction given by the optional last argument of `lim`: none for both sides, `1` for the right and `-1`
    /// for the left. Returns `None` for any other argument.
    #[must_use]
    pub fn from_args(args: &[Expr]) -> Option<Self> {
        match args {
            [] => Some(Self::Both),
            [Term::Value(value)] if value.value == 1 => Some(Self::Right),
            [Term::Value(value)] if value.value == -1 => Some(Self::Left),
            _ => None,
        }
    }
}

/// Why a limit couldn't be computed.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LimitError {
    /// The limit doesn't exist, like the two-sided limit of `{$1/x$}` at 0 or `{$sin(x)$}` at `{$oo$}`. `lim`
    /// evaluates to `undefined`.
    Undefined,
    /// The expression contains something the algorithm can't handle, like `{$floor(x)$}` at `{$oo$}`.
    Unsupported,
    /// The limit couldn't be determined, like `{$x / sin(x)^2$}` at `{$oo$}` (`{$oo$}` on its domain, which has
    /// holes at the zeros of `sin`), or a too deep recursion.
    Unknown,
}

impl fmt::Display for LimitError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Self::Undefined => "the limit doesn't exist",
            Self::Unsupported => "the expression isn't supported",
            Self::Unknown => "the limit couldn't be determined",
        })
    }
}

impl Error for LimitError {}

/// Result of a limit computation.
pub type LimitResult<T> = Result<T, LimitError>;

impl Term<Real> {
    /// Limit of the expression when `x` tends to `point`, from the side given by `direction`. `point` can be
    /// `{$oo$}` or `{$-oo$}` (with [`Direction::Both`]), and so can the result.
    ///
    /// # Errors
    /// See [`LimitError`].
    ///
    /// ```
    /// use formalith::{field::real::R, limit::{Direction, LimitError}, parse, symbol};
    ///
    /// let f = parse!("(x^2 - 1)/(x - 1)", R);
    /// assert_eq!(f.limit(symbol!("x"), &parse!("1", R), Direction::Both), Ok(parse!("2", R)));
    /// let f = parse!("exp(x)/x^3", R);
    /// assert_eq!(f.limit(symbol!("x"), &parse!("oo", R), Direction::Both), Ok(parse!("oo", R)));
    /// let f = parse!("1/x", R);
    /// assert_eq!(f.limit(symbol!("x"), &parse!("0", R), Direction::Both), Err(LimitError::Undefined));
    /// ```
    pub fn limit(&self, x: Symbol, point: &Self, direction: Direction) -> LimitResult<Self> {
        profile_scope!("limit");
        if depends(point, x) {
            return Err(LimitError::Unsupported);
        }
        if !depends(self, x) {
            return Ok(self.clone());
        }
        if has_step(self, x) {
            return match remove_steps(self, x, point, direction) {
                Ok(f) => f.limit(x, point, direction),
                Err(Step::BothSides) => both_sides(
                    &self.limit(x, point, Direction::Right)?,
                    &self.limit(x, point, Direction::Left)?,
                ),
                Err(Step::Limit(error)) => Err(error),
            };
        }
        let without_zero_powers = remove_zero_powers(self, x, point, direction)?;
        if without_zero_powers != *self {
            return without_zero_powers.limit(x, point, direction);
        }
        let (f, infinite) = prepare(self, x, point, direction)?;
        let at_infinity = |f: &Self| Gruntz::new(x).limit(f);
        if let Some(sign) = infinite {
            return if sign == Ordering::Less {
                at_infinity(
                    &f.substitute(x, &-variable(x))
                        .ok_or(LimitError::Unsupported)?,
                )
            } else {
                at_infinity(&f)
            };
        }
        if let Some(res) = eval_at(&f, x, point) {
            return Ok(res);
        }
        let side = |sign: i64| {
            let approach = point + &(value(Rational::from(sign)) / variable(x));
            at_infinity(&f.substitute(x, &approach).ok_or(LimitError::Unsupported)?)
        };
        match direction {
            Direction::Right => side(1),
            Direction::Left => side(-1),
            Direction::Both => both_sides(&side(1)?, &side(-1)?),
        }
    }
}

/// The two-sided limit from the `right` and `left` limits, `undefined` when they surely differ.
fn both_sides(right: &Expr, left: &Expr) -> LimitResult<Expr> {
    if right == left {
        return Ok(right.clone());
    }
    match (infinity_part(right), infinity_part(left)) {
        // Parameters are assumed non-zero, so `{$sign(a) oo != -sign(a) oo$}`
        (Some(r), Some(l)) if (&r + &l).is_zero() => Err(LimitError::Undefined),
        (Some(_), Some(_)) => Err(LimitError::Unknown),
        (Some(_), None) | (None, Some(_)) => Err(LimitError::Undefined),
        (None, None) => match const_sign(&(right - left))? {
            Ordering::Equal => Ok(right.clone()),
            _ => Err(LimitError::Undefined),
        },
    }
}

/// Why `floor` and `ceil` couldn't be removed by [`remove_steps`].
enum Step {
    /// The argument tends to an integer at a finite point, each side must be computed.
    BothSides,
    /// The limit of the argument failed.
    Limit(LimitError),
}

impl From<LimitError> for Step {
    fn from(error: LimitError) -> Self {
        Self::Limit(error)
    }
}

/// Whether `f` contains `floor` or `ceil` of an argument depending on `x`.
fn has_step(f: &Expr, x: Symbol) -> bool {
    match f {
        Term::Value(_) | Term::Symbol(_) => false,
        Term::Add(add) => add.iter().any(|t| has_step(t, x)),
        Term::Mul(mul) => mul.iter().any(|t| has_step(t, x)),
        Term::Pow(pow) => has_step(&pow.base, x) || has_step(&pow.exponant, x),
        Term::Fun(function) => {
            matches!(unary(f), Some((Context::FLOOR | Context::CEIL, g)) if depends(g, x))
                || function
                    .get_args::<Real>()
                    .is_some_and(|args| args.iter().any(|arg| has_step(arg, x)))
        }
    }
}

/// Replace `{$floor g$}` and `{$ceil g$}` in `f` by their constant value when `x` tends to `point`: the integer
/// part of `{$L = lim g$}` for a non-integer `L`. For an integer `L = n`, it depends on the sign `s` of `{$g - n$}`
/// on the side of the limit, `{$floor g = n$}` or `{$n - 1$}` and `{$ceil g = n + 1$}` or `{$n$}`.
fn remove_steps(f: &Expr, x: Symbol, point: &Expr, direction: Direction) -> Result<Expr, Step> {
    let Some((ident @ (Context::FLOOR | Context::CEIL), g)) = unary(f) else {
        return try_map_operands(f, |t| remove_steps(t, x, point, direction));
    };
    if !depends(g, x) {
        return Ok(f.clone());
    }
    let limit = g.limit(x, point, direction)?;
    if !limit
        .symbols()
        .iter()
        .all(|s| matches!(*s, Context::PI | Context::E | Context::EULER_GAMMA))
    {
        return Err(LimitError::Unsupported.into());
    }
    let n = match &limit {
        Term::Value(n) => n.value.clone(),
        _ => Rational::from(
            approximate(&limit, DIGITS)
                .ok_or(LimitError::Unknown)?
                .floor(),
        ),
    };
    if n.denominator_ref() != &1 || limit != value(n.clone()) {
        // `{$n < L < n + 1$}`
        let n = Rational::from(n.floor());
        if const_sign(&(&limit - &value(n.clone())))? != Ordering::Greater
            || const_sign(&(value(&n + Rational::ONE) - &limit))? != Ordering::Greater
        {
            return Err(LimitError::Unknown.into());
        }
        return Ok(value(if ident == Context::FLOOR {
            n
        } else {
            n + Rational::ONE
        }));
    }
    let direction = match direction {
        Direction::Both if infinity_sign(point).is_none() => return Err(Step::BothSides),
        direction => direction,
    };
    // The sign of `{$g - n$}` near the point
    let difference = g - &value(n.clone());
    let sign = (&difference / &fun(Context::ABS, difference.clone())).limit(x, point, direction)?;
    let n = match (ident, sign) {
        (Context::FLOOR, sign) if sign == one() => n,
        (Context::FLOOR, sign) if sign == -one() => n - Rational::ONE,
        (_, sign) if sign == one() => n + Rational::ONE,
        (_, sign) if sign == -one() => n,
        _ => return Err(LimitError::Unknown.into()),
    };
    Ok(value(n))
}

/// Replace `{$0^g$}` in `f`, `g` depending on `x`, by 0 when `{$L = lim g$}` is positive (`g` is then positive near
/// the point), which [`exp_log_form`] can't write as `{$exp(g ln 0)$}`. The limit is undefined for a negative `L`
/// (`{$0^g$}` is a division by zero near the point), and unknown otherwise.
fn remove_zero_powers(
    f: &Expr,
    x: Symbol,
    point: &Expr,
    direction: Direction,
) -> LimitResult<Expr> {
    match f {
        Term::Pow(pow) if pow.base.is_zero() && depends(&pow.exponant, x) => {
            match const_sign(&pow.exponant.limit(x, point, direction)?)? {
                Ordering::Greater => Ok(zero()),
                Ordering::Less => Err(LimitError::Undefined),
                Ordering::Equal => Err(LimitError::Unknown),
            }
        }
        _ => try_map_operands(f, |t| remove_zero_powers(t, x, point, direction)),
    }
}

/// Checks and rewrites shared by limits and series of `f` when `x` tends to `point`: `f` in the form of
/// [`exp_log_form`], and the sign of `point` when it is `{$plus.minus oo$}`. Infinite points must be approached
/// from both sides, and special constants are only allowed as an infinite point.
pub(crate) fn prepare(
    f: &Expr,
    x: Symbol,
    point: &Expr,
    direction: Direction,
) -> LimitResult<(Expr, Option<Ordering>)> {
    if depends(point, x) || has_special_constant(f) {
        return Err(LimitError::Unsupported);
    }
    let infinite = infinity_sign(point);
    let f = exp_log_form(f, x, infinite.is_some())?;
    if infinite.is_some() && direction != Direction::Both
        || infinite.is_none() && has_special_constant(point)
    {
        return Err(LimitError::Unsupported);
    }
    Ok((f, infinite))
}

/// The sign `s` of an infinite limit `{$s oo$}`, which is `{$plus.minus 1$}` or contains `sign` of parameters, or
/// `None` for a finite limit.
fn infinity_part(term: &Expr) -> Option<Expr> {
    match term {
        Term::Symbol(_) if *term == infinity() => Some(one()),
        Term::Mul(mul) if mul.iter().any(|factor| *factor == infinity()) => Some(
            mul.iter()
                .filter(|factor| **factor != infinity())
                .fold(value(mul.coefficient.clone()), |res, factor| res * factor),
        ),
        _ => None,
    }
}

/// The sign of a constant term, from its numerical approximation. Fails if it contains symbols, other than
/// builtin constants.
fn const_sign(term: &Expr) -> LimitResult<Ordering> {
    if !matches!(term, Term::Value(_)) && bounds::has_angle(term) {
        return bounds::bounds_sign(term).ok_or(LimitError::Unknown);
    }
    // Parameters without assumption are generic, so non-zero
    sign(term, SignMode::GENERIC).ok_or(LimitError::Unknown)
}

/// Compare two constant terms, see [`const_sign`].
fn const_cmp(a: &Expr, b: &Expr) -> LimitResult<Ordering> {
    if a == b {
        return Ok(Ordering::Equal);
    }
    const_sign(&(a - b))
}

/// A rational close to the constant `term`, below it if `!above`, above it otherwise.
fn rational_bound(term: &Expr, above: bool) -> LimitResult<Rational> {
    if let Term::Value(value) = term {
        return Ok(value.value.clone());
    }
    let epsilon = Rational::from_signeds(1, 1_000_000_000_000_i64);
    let value = approximate(term, DIGITS).ok_or(LimitError::Unknown)?;
    Ok(if above {
        value + epsilon
    } else {
        value - epsilon
    })
}

/// Whether `term` has only builtin constants and `allowed` as symbols.
fn only_symbols(term: &Expr, allowed: &[Symbol]) -> bool {
    term.symbols()
        .iter()
        .all(|symbol| Context::is_builtin_constant(*symbol) || allowed.contains(symbol))
}

/// Rewrite powers with an exponent depending on `x` as `{$b^g = exp(g ln b)$}` (`{$|b|^g cos(pi g)$}` for a
/// negative constant `b` at an infinite point, its value at integers `g`, unsupported at a finite point where
/// it isn't continuous, and for a constant `b` not known to be positive), `{$tan u$}` as
/// `{$sin u / cos u$}`, `{$sign u$}` as `{$u / |u|$}`, `min` and `max` with `abs`, hyperbolic functions and their
/// inverses with `exp` and `ln`, and `asin` and `acos` with `atan`.
fn exp_log_form(term: &Expr, x: Symbol, infinite: bool) -> LimitResult<Expr> {
    if !depends(term, x) {
        return Ok(term.clone());
    }
    Ok(match term {
        Term::Pow(pow) => {
            let base = exp_log_form(&pow.base, x, infinite)?;
            let exponant = exp_log_form(&pow.exponant, x, infinite)?;
            if depends(&exponant, x)
                && !depends(&base, x)
                && constant_sign(&base) == Some(Ordering::Less)
            {
                if !infinite {
                    return Err(LimitError::Unsupported);
                }
                fun(Context::EXP, &exponant * &fun(Context::LN, -base))
                    * fun(Context::COS, variable(Context::PI) * exponant)
            } else if depends(&exponant, x) {
                // `{$exp(g ln b)$}` is `{$b^g$}` only for `{$b > 0$}`, a constant base of unknown sign may be
                // negative or zero
                if !depends(&base, x) && constant_sign(&base) != Some(Ordering::Greater) {
                    return Err(LimitError::Unsupported);
                }
                fun(Context::EXP, exponant * fun(Context::LN, base))
            } else {
                base.pow(&exponant)
            }
        }
        Term::Fun(f) => {
            let args = f
                .get_args::<Real>()
                .ok_or(LimitError::Unsupported)?
                .iter()
                .map(|arg| exp_log_form(arg, x, infinite))
                .collect::<LimitResult<Vec<_>>>()?;
            match (f.get_ident(), args.as_slice()) {
                (Context::TAN, [u]) => fun(Context::SIN, u.clone()) / fun(Context::COS, u.clone()),
                // `{$u! = Gamma(u + 1)$}`, `{$binom(n, k) = Gamma(n + 1) / (Gamma(k + 1) Gamma(n - k + 1))$}`
                (Context::FACTORIAL, [u]) => fun(Context::GAMMA, u + &one()),
                (Context::BINOMIAL, [n, k]) => {
                    fun(Context::GAMMA, n + &one())
                        / (fun(Context::GAMMA, k + &one()) * fun(Context::GAMMA, n - k + one()))
                }
                (ident @ (Context::SINH | Context::COSH | Context::TANH), [u]) => {
                    hyperbolic_as_exp(ident, u).expect("A hyperbolic function")
                }
                // `{$"asinh" u = ln(u + sqrt(u^2 + 1))$}`, `{$"acosh" u = ln(u + sqrt(u^2 - 1))$}`
                (Context::ASINH, [u]) => fun(Context::LN, u + &sqrt(&(u * u + one()))),
                (Context::ACOSH, [u]) => fun(Context::LN, u + &sqrt(&(u * u - one()))),
                // `{$"atanh" u = ln((1 + u)/(1 - u))/2$}`
                (Context::ATANH, [u]) => {
                    fun(Context::LN, (one() + u.clone()) / (one() - u.clone())) * half()
                }
                (ident @ (Context::ASIN | Context::ACOS), [u]) => {
                    // `{$asin u = 2 atan(u/(1 + sqrt(1 - u^2)))$}`, `{$acos u = pi/2 - asin u$}`
                    let asin = value(Rational::from(2))
                        * fun(Context::ATAN, u / &(one() + sqrt(&(one() - u * u))));
                    if ident == Context::ASIN {
                        asin
                    } else {
                        variable(Context::PI) * half() - asin
                    }
                }
                (Context::SIGN, [u]) => u / &fun(Context::ABS, u.clone()),
                (Context::MIN | Context::MAX, [first, rest @ ..]) => {
                    // `{$max(f, g) = (f + g + |f - g|)/2$}`, `{$min(f, g) = (f + g - |f - g|)/2$}`
                    let sign = value(Rational::from(if f.get_ident() == Context::MAX {
                        1
                    } else {
                        -1
                    }));
                    rest.iter().fold(first.clone(), |res, arg| {
                        let distance = fun(Context::ABS, &res - arg);
                        (res + arg.clone() + sign.clone() * distance) * half()
                    })
                }
                (ident, _) => Term::Fun(Box::new(Fun::new(ident, args, R))).normalize(),
            }
        }
        _ => try_map_operands(term, |operand| exp_log_form(operand, x, infinite))?,
    })
}

/// Evaluate `term` at `{$x = a$}` if it is continuous there, returning `None` on any possible singularity, like a
/// division by zero or `{$ln(0)$}`. Parameters are assumed generic: a power of `{$a - b$}` is assumed defined.
fn eval_at(term: &Expr, x: Symbol, a: &Expr) -> Option<Expr> {
    if !depends(term, x) {
        return Some(term.clone());
    }
    let generic = |term: &Expr| !only_symbols(term, &[]);
    let positive = |term: &Expr| generic(term) || const_sign(term) == Ok(Ordering::Greater);
    let nonzero = |term: &Expr| {
        !term.is_zero() && (generic(term) || const_sign(term).is_ok_and(Ordering::is_ne))
    };
    match term {
        Term::Value(_) => Some(term.clone()),
        Term::Symbol(_) => Some(a.clone()),
        Term::Add(_) | Term::Mul(_) => {
            try_map_operands(term, |operand| eval_at(operand, x, a).ok_or(())).ok()
        }
        Term::Pow(pow) => {
            let exponant = &**pow.exponant;
            if depends(exponant, x) {
                return None;
            }
            let base = eval_at(&pow.base, x, a)?;
            let defined = if exponant.to_i64().is_some() {
                !exponant.is_strictly_negative() || nonzero(&base)
            } else {
                positive(&base)
            };
            defined.then(|| base.pow(exponant))
        }
        Term::Fun(_) if polygamma_args(term).is_some() => {
            let (m, arg) = polygamma_args(term)?;
            let arg = eval_at(arg, x, a)?;
            gamma_pole(&arg).is_none().then(|| polygamma(m, arg))
        }
        Term::Fun(_) => {
            let (ident, arg) = unary(term)?;
            let arg = eval_at(arg, x, a)?;
            match ident {
                Context::EXP
                | Context::SIN
                | Context::COS
                | Context::ABS
                | Context::ATAN
                | Context::ERF
                | Context::ERFI
                | Context::SI => Some(fun(ident, arg)),
                Context::LN | Context::CI if positive(&arg) => Some(fun(ident, arg)),
                Context::EI if nonzero(&arg) => Some(fun(ident, arg)),
                Context::GAMMA if gamma_pole(&arg).is_none() => Some(fun(ident, arg)),
                _ => None,
            }
        }
    }
}
