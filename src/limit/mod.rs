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
//! `min`, `max` and `sign` are rewritten with `abs`.
//!
//! `{$sin g$}` and `{$cos g$}` with `{$g -> plus.minus oo$}` oscillate: `g` is replaced by an angle `{$theta$}`, a
//! constant for the algorithm, after checking that the expression stays bounded away from its singularities for
//! every `{$theta$}`. A result depending on `{$theta$}` means that the limit doesn't exist. A limit whose sign
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
mod gruntz;
mod series;

use std::{cmp::Ordering, error::Error, fmt};

use malachite::{
    Rational,
    base::num::{arithmetic::traits::Sign, basic::traits::One},
};

use crate::{
    context::{Context, Symbol},
    field::real::{R, approx::approximate},
    term::{Fun, Normalize, SymbolTerm, Term, Value},
};

use gruntz::Gruntz;

type Real = R<Rational>;
type Expr = Term<Real>;

/// Significant digits of the numerical approximations deciding signs and zeros.
const DIGITS: u64 = 30;

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
    /// The expression contains something the algorithm can't handle, like `{$floor(x)$}`.
    Unsupported,
    /// The limit couldn't be determined, like `{$1/(x sin x)$}` at `{$oo$}` (unbounded near the zeros of `sin`),
    /// or a too deep recursion.
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
        if depends(point, x) {
            return Err(LimitError::Unsupported);
        }
        if !depends(self, x) {
            return Ok(self.clone());
        }
        if depends(self, Context::OO) || depends(self, Context::UNDEFINED) {
            return Err(LimitError::Unsupported);
        }
        let f = exp_log_form(self, x)?;
        let at_infinity = |f: &Self| Gruntz::new(x).limit(f);
        if let Some(sign) = infinity_sign(point) {
            if direction != Direction::Both {
                return Err(LimitError::Unsupported);
            }
            return if sign == Ordering::Less {
                at_infinity(
                    &f.substitute(x, &-variable(x))
                        .ok_or(LimitError::Unsupported)?,
                )
            } else {
                at_infinity(&f)
            };
        }
        if depends(point, Context::OO) || depends(point, Context::UNDEFINED) {
            return Err(LimitError::Unsupported);
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
            Direction::Both => {
                let (right, left) = (side(1)?, side(-1)?);
                if right == left {
                    return Ok(right);
                }
                match (infinity_part(&right), infinity_part(&left)) {
                    // Parameters are assumed non-zero, so `{$sign(a) oo != -sign(a) oo$}`
                    (Some(r), Some(l)) if (&r + &l).is_zero() => Err(LimitError::Undefined),
                    (Some(_), Some(_)) => Err(LimitError::Unknown),
                    (Some(_), None) | (None, Some(_)) => Err(LimitError::Undefined),
                    (None, None) => match const_sign(&(&right - &left))? {
                        Ordering::Equal => Ok(right),
                        _ => Err(LimitError::Undefined),
                    },
                }
            }
        }
    }
}

/// The sign `s` of an infinite limit `{$s oo$}`, which is `{$plus.minus 1$}` or contains `sign` of parameters, or
/// `None` for a finite limit.
fn infinity_part(term: &Expr) -> Option<Expr> {
    match term {
        Term::Symbol(_) if *term == infinity() => Some(one()),
        Term::Mul(mul) if mul.iter().any(|factor| *factor == infinity()) => {
            Some(term / &infinity())
        }
        _ => None,
    }
}

/// The constant `value`.
pub(crate) fn value(value: Rational) -> Expr {
    Term::Value(Value::new(value, R))
}

/// The symbol `x` as an expression.
pub(crate) const fn variable(x: Symbol) -> Expr {
    Term::Symbol(SymbolTerm::new(x, R))
}

/// `{$oo$}`.
const fn infinity() -> Expr {
    variable(Context::OO)
}

/// The function `ident(arg)`, normalized.
pub(crate) fn fun(ident: Symbol, arg: Expr) -> Expr {
    Term::Fun(Box::new(Fun::new(ident, vec![arg], R))).normalize()
}

/// The identifier and argument of a builtin function with one real argument.
fn unary(term: &Expr) -> Option<(Symbol, &Expr)> {
    match term {
        Term::Fun(fun) => match fun.get_args::<Real>().map(Vec::as_slice) {
            Some([arg]) => Some((fun.get_ident(), arg)),
            _ => None,
        },
        _ => None,
    }
}

/// Whether `term` contains the symbol `x`.
pub(crate) fn depends(term: &Expr, x: Symbol) -> bool {
    term.symbols().contains(&x)
}

/// `Some(Greater)` for `{$oo$}`, `Some(Less)` for `{$-oo$}`, `None` otherwise.
fn infinity_sign(term: &Expr) -> Option<Ordering> {
    if *term == infinity() {
        Some(Ordering::Greater)
    } else if *term == -infinity() {
        Some(Ordering::Less)
    } else {
        None
    }
}

/// Whether `term` is `{$oo$}` or `{$-oo$}`.
fn is_infinite(term: &Expr) -> bool {
    infinity_sign(term).is_some()
}

/// The sign of a constant term, from its numerical approximation. Fails if it contains symbols, other than
/// builtin constants.
fn const_sign(term: &Expr) -> LimitResult<Ordering> {
    match term {
        Term::Value(value) => Ok(value.value.sign()),
        _ if bounds::has_angle(term) => bounds::bounds_sign(term).ok_or(LimitError::Unknown),
        _ => approximate(term, DIGITS)
            .map(|value| value.sign())
            .ok_or(LimitError::Unknown),
    }
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

/// Rewrite powers with an exponent depending on `x` as `{$b^g = exp(g ln b)$}`, `{$tan u$}` as
/// `{$sin u / cos u$}`, `{$sign u$}` as `{$u / |u|$}`, `min` and `max` with `abs`, hyperbolic functions and their
/// inverses with `exp` and `ln`, and `asin` and `acos` with `atan`.
fn exp_log_form(term: &Expr, x: Symbol) -> LimitResult<Expr> {
    if !depends(term, x) {
        return Ok(term.clone());
    }
    Ok(match term {
        Term::Value(_) | Term::Symbol(_) => term.clone(),
        Term::Add(add) => add.iter().try_fold(Term::zero(R), |res, term| {
            Ok::<_, LimitError>(res + exp_log_form(term, x)?)
        })?,
        Term::Mul(mul) => mul
            .iter()
            .try_fold(value(mul.coefficient.clone()), |res, factor| {
                Ok::<_, LimitError>(res * exp_log_form(factor, x)?)
            })?,
        Term::Pow(pow) => {
            let base = exp_log_form(&pow.base, x)?;
            let exponant = exp_log_form(&pow.exponant, x)?;
            if depends(&exponant, x) {
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
                .map(|arg| exp_log_form(arg, x))
                .collect::<LimitResult<Vec<_>>>()?;
            match (f.get_ident(), args.as_slice()) {
                (Context::TAN, [u]) => fun(Context::SIN, u.clone()) / fun(Context::COS, u.clone()),
                (ident @ (Context::SINH | Context::COSH), [u]) => {
                    // `{$sinh u = (e^u - e^(-u))/2$}`, `{$cosh u = (e^u + e^(-u))/2$}`
                    let (exp, exp_opposite) = (fun(Context::EXP, u.clone()), fun(Context::EXP, -u));
                    let half = value(Rational::from_signeds(1, 2));
                    if ident == Context::SINH {
                        (exp - exp_opposite) * half
                    } else {
                        (exp + exp_opposite) * half
                    }
                }
                // `{$tanh u = (e^(2 u) - 1)/(e^(2 u) + 1)$}`
                (Context::TANH, [u]) => {
                    let exp = fun(Context::EXP, value(Rational::from(2)) * u.clone());
                    (&exp - &one()) / (exp + one())
                }
                // `{$"asinh" u = ln(u + sqrt(u^2 + 1))$}`, `{$"acosh" u = ln(u + sqrt(u^2 - 1))$}`
                (Context::ASINH, [u]) => fun(Context::LN, u + &sqrt(u * u + one())),
                (Context::ACOSH, [u]) => fun(Context::LN, u + &sqrt(u * u - one())),
                // `{$"atanh" u = ln((1 + u)/(1 - u))/2$}`
                (Context::ATANH, [u]) => {
                    fun(Context::LN, (one() + u.clone()) / (one() - u.clone()))
                        * value(Rational::from_signeds(1, 2))
                }
                (ident @ (Context::ASIN | Context::ACOS), [u]) => {
                    // `{$asin u = 2 atan(u/(1 + sqrt(1 - u^2)))$}`, `{$acos u = pi/2 - asin u$}`
                    let asin = value(Rational::from(2))
                        * fun(Context::ATAN, u / &(one() + sqrt(one() - u * u)));
                    if ident == Context::ASIN {
                        asin
                    } else {
                        variable(Context::PI) * value(Rational::from_signeds(1, 2)) - asin
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
                    let half = value(Rational::from_signeds(1, 2));
                    rest.iter().fold(first.clone(), |res, arg| {
                        let distance = fun(Context::ABS, &res - arg);
                        (res + arg.clone() + sign.clone() * distance) * half.clone()
                    })
                }
                (ident, _) => Term::Fun(Box::new(Fun::new(ident, args, R))).normalize(),
            }
        }
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
        Term::Add(add) => add
            .iter()
            .try_fold(Term::zero(R), |res, term| Some(res + eval_at(term, x, a)?)),
        Term::Mul(mul) => mul
            .iter()
            .try_fold(value(mul.coefficient.clone()), |res, factor| {
                Some(res * eval_at(factor, x, a)?)
            }),
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
        Term::Fun(_) => {
            let (ident, arg) = unary(term)?;
            let arg = eval_at(arg, x, a)?;
            match ident {
                Context::EXP | Context::SIN | Context::COS | Context::ABS | Context::ATAN => {
                    Some(fun(ident, arg))
                }
                Context::LN if positive(&arg) => Some(fun(ident, arg)),
                _ => None,
            }
        }
    }
}

/// The constant 1.
fn one() -> Expr {
    value(Rational::ONE)
}

/// `{$sqrt(u)$}`.
fn sqrt(u: Expr) -> Expr {
    u.pow(&value(Rational::from_signeds(1, 2)))
}
