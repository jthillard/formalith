//! Numerical approximation of real expressions, used by `approx`.
//!
//! Expressions are evaluated with fixed-point arithmetic on integers, an integer `m` standing for `{$m / 2^b$}`,
//! then rounded to a number of significant decimal digits. Each evaluation gives a [`Ball`], the approximation with
//! a bound of its error (an estimate for some algorithms, see [`Ball`]), and the working precision is increased until
//! the ball has enough significant bits, so cancellations don't give wrong digits or signs.

use std::{cell::RefCell, thread::LocalKey};

use malachite::{
    Integer, Natural, Rational,
    base::{
        num::{
            arithmetic::traits::{
                Abs, Ceiling, CeilingLogBase2, DivRound, DivisibleBy, Factorial, Floor,
                FloorLogBase2, FloorRoot, Pow, Reciprocal, Sign, UnsignedAbs,
            },
            basic::traits::{One, Zero},
            conversion::traits::RoundingFrom,
            logic::traits::SignificantBits,
        },
        rounding_modes::RoundingMode,
    },
};

use crate::{
    context::{Context, Symbol},
    term::{Add, Fun, Mul, Normalize, SymbolTerm, Term, Value, flags::Flags},
};

use super::{R, special::bernoulli};

type Real = R<Rational>;

/// Default number of significant digits of `approx`.
pub const DEFAULT_DIGITS: u64 = 15;
/// Maximum number of significant digits of `approx`.
pub const MAX_DIGITS: u64 = 10_000;
/// Arguments of `exp` above this bound are not evaluated, the result being too large.
const MAX_EXP_ARGUMENT: u64 = 100_000;
/// Integer exponents above this bound are not evaluated.
const MAX_EXPONENT: u64 = 10_000;
/// Roots of higher order are computed with `{$exp(ln(x) / n)$}`.
const MAX_ROOT: u64 = 64;
/// Bits added to the working precision, absorbing rounding errors.
const GUARD_BITS: u64 = 32;
/// Halvings of the argument of the Taylor series of `exp`, `sin` and `cos`, making them converge faster.
const HALVINGS: u64 = 8;

/// Minimum number of halvings of the step of the numerical integration.
const MIN_QUADRATURE_LEVELS: u64 = 3;
/// Maximum number of halvings of the step of the numerical integration.
const MAX_QUADRATURE_LEVELS: u64 = 10;
/// Bound of the parameter `s` of the nodes of the numerical integration.
const MAX_QUADRATURE_S: u64 = 6;
/// Largest natural number whose factorial is computed exactly.
const MAX_EXACT_FACTORIAL: u64 = 10_000;
/// Most terms of an infinite sum added.
const MAX_SUM_TERMS: i64 = 1000;
/// Consecutive terms below the precision ending an infinite sum.
const NEGLIGIBLE_TERMS: usize = 8;

thread_local! {
    /// `{$pi$}` at the last precisions used, see [`Fixed::cached`].
    static PI: RefCell<Vec<(u64, Integer)>> = const { RefCell::new(Vec::new()) };
    /// `{$ln 2$}` at the last precisions used.
    static LN2: RefCell<Vec<(u64, Integer)>> = const { RefCell::new(Vec::new()) };
}

/// The substitution used by the numerical integration, depending on the bounds.
enum Quadrature {
    /// Finite bounds `a` and `b`.
    Finite(Rational, Rational),
    /// From `a` to `{$oo$}`.
    Right(Rational),
    /// From `{$-oo$}` to `b`.
    Left(Rational),
    /// From `{$-oo$}` to `{$oo$}`.
    Whole,
}

/// Largest number of bits of the argument of `sin` and `cos` before its reduction modulo `{$2 pi$}`, which needs
/// that many more bits of `{$pi$}`.
const MAX_REDUCTION_BITS: u64 = 1 << 16;
/// Significant bits kept in radii, rounded up.
const RADIUS_BITS: u64 = 32;
/// The step of the differences estimating slopes is about `{$2^(-"SLOPE_STEP_BITS")$}` relative to the point.
const SLOPE_STEP_BITS: u64 = 24;

thread_local! {
    /// Whether the last evaluation failed because a ball was too wide, like `{$tan$}` of a ball containing a pole
    /// or `{$floor$}` of a ball containing an integer, so that a higher precision may succeed.
    static IMPRECISE: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

/// `None`, recording that the evaluation failed for lack of precision (see [`IMPRECISE`]).
fn imprecise<T>() -> Option<T> {
    IMPRECISE.set(true);
    None
}

/// A ball `{$[m - r, m + r]$}` containing a real number: the result of an evaluation with its error bound.
///
/// The elementary operations (`+`, `*`, powers, `exp`, `ln`, `sin`, `cos`, `tan`, the inverse trigonometric and
/// hyperbolic functions, roots, `rootof`, `pi`, `e`) bound their errors: the rounding errors of each primitive,
/// bounded per primitive (see [`Fixed::absolute_error`]), plus the error of their arguments times a bound of the
/// derivative on the ball. The radii of the other algorithms (numerical integration, infinite sums, the Gamma family,
/// `zeta`, the Lambert W function, `erf`, `Si`, `Ci`, `Ei`) are estimates, not bounds.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Ball {
    /// The center, the approximation.
    pub mid: Rational,
    /// The radius, non-negative.
    pub rad: Rational,
}

impl Ball {
    /// The exact value `mid`.
    #[must_use]
    pub const fn exact(mid: Rational) -> Self {
        Self {
            mid,
            rad: Rational::ZERO,
        }
    }

    fn new(mid: Rational, rad: Rational) -> Self {
        Self {
            mid,
            rad: round_up(rad),
        }
    }

    /// The lower bound `{$m - r$}`.
    #[must_use]
    pub fn lo(&self) -> Rational {
        &self.mid - &self.rad
    }

    /// The upper bound `{$m + r$}`.
    #[must_use]
    pub fn hi(&self) -> Rational {
        &self.mid + &self.rad
    }

    /// Whether 0 is in the ball.
    #[must_use]
    pub fn contains_zero(&self) -> bool {
        (&self.mid).abs() <= self.rad
    }

    /// The sign of the number, `None` when the ball contains 0 (and isn't exactly 0).
    #[must_use]
    pub fn sign(&self) -> Option<std::cmp::Ordering> {
        if self.rad == 0 {
            return Some(self.mid.sign());
        }
        (!self.contains_zero()).then(|| self.mid.sign())
    }

    /// An upper bound of the absolute value.
    fn magnitude(&self) -> Rational {
        (&self.mid).abs() + &self.rad
    }

    /// A lower bound of the absolute value, 0 when the ball contains 0.
    fn min_magnitude(&self) -> Rational {
        let res = (&self.mid).abs() - &self.rad;
        if res < 0 { Rational::ZERO } else { res }
    }

    fn add(&self, other: &Self) -> Self {
        Self::new(&self.mid + &other.mid, &self.rad + &other.rad)
    }

    fn mul(&self, other: &Self) -> Self {
        let rad = (&self.mid).abs() * &other.rad
            + (&other.mid).abs() * &self.rad
            + &self.rad * &other.rad;
        Self::new(&self.mid * &other.mid, rad)
    }

    /// `{$1/x$}`, `None` when the ball contains 0.
    fn reciprocal(&self) -> Option<Self> {
        if self.rad == 0 {
            return (self.mid != 0).then(|| Self::exact((&self.mid).reciprocal()));
        }
        let low = self.min_magnitude();
        if low == 0 {
            return imprecise();
        }
        // `{$|1/y - 1/m| <= r / (|m| (|m| - r))$}`
        let rad = &self.rad / ((&self.mid).abs() * low);
        Some(Self::new((&self.mid).reciprocal(), rad))
    }
}

/// `r` rounded up to [`RADIUS_BITS`] significant bits, so that radii don't grow huge denominators.
fn round_up(r: Rational) -> Rational {
    if r <= 0 {
        return Rational::ZERO;
    }
    // Small enough already
    if r.numerator_ref().significant_bits() + r.denominator_ref().significant_bits()
        <= 4 * RADIUS_BITS
    {
        return r;
    }
    let log = r.floor_log_base_2();
    let shift = i64::try_from(RADIUS_BITS).unwrap_or(32) - log;
    let scaled = if shift >= 0 {
        r << shift.unsigned_abs()
    } else {
        r >> shift.unsigned_abs()
    };
    let up = Rational::from(Ceiling::ceiling(scaled));
    if shift >= 0 {
        up >> shift.unsigned_abs()
    } else {
        up << shift.unsigned_abs()
    }
}

/// A slightly larger bound for a positive quantity computed numerically, used as a bound of a derivative.
fn upper(x: &Rational) -> Rational {
    x.abs() * Rational::from_signeds(17, 16) + (Rational::ONE >> 64_u64)
}

/// Fixed-point arithmetic, an integer `m` standing for `{$m / 2^"bits"$}`.
#[derive(Clone, Copy)]
struct Fixed {
    bits: u64,
}

impl Fixed {
    fn one(self) -> Integer {
        Integer::ONE << self.bits
    }
    // Paired with `to_rational`, at the precision of `self`
    #[allow(clippy::wrong_self_convention)]
    fn from_rational(self, x: &Rational) -> Integer {
        (x << self.bits).floor()
    }
    fn to_rational(self, m: Integer) -> Rational {
        Rational::from(m) >> self.bits
    }
    fn mul(self, a: &Integer, b: &Integer) -> Integer {
        (a * b) >> self.bits
    }
    fn div(self, a: &Integer, b: &Integer) -> Integer {
        (a << self.bits) / b
    }

    /// `{$arctan(1/n)$}`, or `{$"arctanh"(1/n)$}` if `hyperbolic`, by their Taylor series.
    fn arctan_inverse(self, n: u64, hyperbolic: bool) -> Integer {
        let n2 = Integer::from(n * n);
        let mut power = self.one() / Integer::from(n);
        let mut sum = Integer::ZERO;
        let mut k = 0_u64;
        while power != 0 {
            let term = &power / Integer::from(2 * k + 1);
            if hyperbolic || k % 2 == 0 {
                sum += term;
            } else {
                sum -= term;
            }
            power /= &n2;
            k += 1;
        }
        sum
    }

    /// `{$pi = 16 arctan(1/5) - 4 arctan(1/239)$}` (Machin's formula).
    fn pi(self) -> Integer {
        self.cached(&PI, || {
            self.arctan_inverse(5, false) * Integer::from(16)
                - self.arctan_inverse(239, false) * Integer::from(4)
        })
    }

    /// `{$ln(2) = 2 "arctanh"(1/3)$}`.
    fn ln2(self) -> Integer {
        self.cached(&LN2, || self.arctan_inverse(3, true) << 1_u64)
    }

    /// A constant at this precision, computed by `compute` once per thread and precision (the terms of sums and
    /// integrals use them again and again).
    fn cached(
        self,
        cache: &'static LocalKey<RefCell<Vec<(u64, Integer)>>>,
        compute: impl FnOnce() -> Integer,
    ) -> Integer {
        /// Number of precisions kept per constant.
        const CACHED_PRECISIONS: usize = 4;
        if let Some(value) = cache.with_borrow(|cache| {
            cache
                .iter()
                .find(|(bits, _)| *bits == self.bits)
                .map(|(_, value)| value.clone())
        }) {
            return value;
        }
        let value = compute();
        cache.with_borrow_mut(|cache| {
            if cache.len() >= CACHED_PRECISIONS {
                cache.remove(0);
            }
            cache.push((self.bits, value.clone()));
        });
        value
    }

    /// `{$"arctanh"(y)$}` for `{$|y| < 1$}`, by its Taylor series.
    fn arctanh(self, y: &Integer) -> Integer {
        let y2 = self.mul(y, y);
        let mut power = y.clone();
        let mut sum = Integer::ZERO;
        let mut k = 0_u64;
        while power != 0 {
            sum += &power / Integer::from(2 * k + 1);
            power = self.mul(&power, &y2);
            k += 1;
        }
        sum
    }

    /// `{$e^x$}`, writing `{$x = k ln(2) + r$}` with `{$|r| <= ln(2) / 2$}`.
    fn exp(self, x: &Integer) -> Option<Integer> {
        let ln2 = self.ln2();
        let k = x.div_round(&ln2, RoundingMode::Nearest).0;
        let r = x - &k * &ln2;
        // `{$e^r = (e^(r / 2^s))^(2^s)$}`
        let r = r >> HALVINGS;
        let mut sum = self.one();
        let mut term = self.one();
        let mut i = 1_u64;
        loop {
            term = self.mul(&term, &r) / Integer::from(i);
            if term == 0 {
                break;
            }
            sum += &term;
            i += 1;
        }
        for _ in 0..HALVINGS {
            sum = self.mul(&sum, &sum);
        }
        let k = i64::try_from(&k).ok()?;
        Some(if k >= 0 { sum << k } else { sum >> -k })
    }

    /// `{$ln(x)$}` for `{$x > 0$}`, writing `{$x = m 2^k$}` with `{$1 <= m < 2$}` and
    /// `{$ln(m) = 2 "arctanh"((m - 1) / (m + 1))$}`.
    fn ln(self, x: &Rational) -> Integer {
        let k = x.floor_log_base_2();
        let m = self.from_rational(&(x >> k));
        let y = self.div(&(&m - self.one()), &(&m + self.one()));
        (self.arctanh(&y) << 1_u64) + Integer::from(k) * self.ln2()
    }

    /// A bound of the rounding errors of the primitives at this precision, in units of the absolute or relative
    /// precision: the truncations of their series (at most one unit per term, and fewer terms than `bits`), amplified
    /// by the [`HALVINGS`] squarings or the halvings of `arctan`, and the errors of `{$pi$}` and `{$ln 2$}`.
    fn ulps(self) -> Rational {
        Rational::from((1_u64 << 20) + (self.bits << HALVINGS)) >> self.bits
    }

    /// The error bound of a primitive with an absolute precision (relative for large values), at the value `v`.
    fn absolute_error(self, v: &Rational) -> Rational {
        self.ulps() * v.abs().max(Rational::ONE)
    }

    /// The error bound of a primitive with a relative precision, like `exp` or roots, at the value `v`.
    fn relative_error(self, v: &Rational) -> Rational {
        self.ulps() * v.abs()
    }

    /// The estimated error of the algorithms without a bound (see [`Ball`]), at the value `v`.
    fn estimated_error(self, v: &Rational) -> Rational {
        (v.abs() + Rational::ONE) >> self.bits.saturating_sub(GUARD_BITS / 2)
    }

    /// `{$(sin(x), cos(x))$}`, reducing `x` modulo `{$2 pi$}` and using the double-angle formulas. The reduction
    /// uses `{$log_2 |x|$}` more bits of `{$pi$}`, since its error is multiplied by the number of periods, `None`
    /// beyond [`MAX_REDUCTION_BITS`].
    fn sin_cos(self, x: &Rational) -> Option<(Integer, Integer)> {
        let extra = if x.abs() >= 1 {
            u64::try_from(x.abs().floor_log_base_2()).ok()? + 2
        } else {
            0
        };
        if extra > MAX_REDUCTION_BITS {
            return None;
        }
        let wide = Self {
            bits: self.bits + extra,
        };
        let x = wide.from_rational(x);
        let two_pi = wide.pi() << 1_u64;
        let n = (&x).div_round(&two_pi, RoundingMode::Nearest).0;
        let r = (x - n * two_pi) >> (extra + HALVINGS);
        let r2 = self.mul(&r, &r);
        let (mut sin, mut cos) = (r.clone(), self.one());
        let (mut sin_term, mut cos_term) = (r, self.one());
        let mut i = 1_u64;
        while sin_term != 0 || cos_term != 0 {
            sin_term = -self.mul(&sin_term, &r2) / Integer::from((2 * i) * (2 * i + 1));
            cos_term = -self.mul(&cos_term, &r2) / Integer::from((2 * i - 1) * (2 * i));
            sin += &sin_term;
            cos += &cos_term;
            i += 1;
        }
        for _ in 0..HALVINGS {
            (sin, cos) = (
                self.mul(&sin, &cos) << 1_u64,
                self.mul(&cos, &cos) - self.mul(&sin, &sin),
            );
        }
        Some((sin, cos))
    }

    /// `{$root(n, x)$}`, `x` being negative only for odd `n`, with a relative precision of about
    /// `{$2^(-"bits")$}` for small `|x|`.
    fn root(self, x: &Rational, n: u64) -> Option<Rational> {
        if *x < 0 && n % 2 == 0 {
            return None;
        }
        if *x == 0 {
            return Some(Rational::ZERO);
        }
        // `{$root(n, |x|) >= 2^(-k)$}` for `{$|x| >= 2^(-n k)$}`
        let magnitude = x.abs();
        let log = magnitude.floor_log_base_2();
        let bits = self.bits
            + if log < 0 {
                log.unsigned_abs() / n + 1
            } else {
                0
            };
        let shifted: Integer = (magnitude << (n * bits)).floor();
        let root = Integer::from(shifted.unsigned_abs().floor_root(n));
        let root = Rational::from(root) >> bits;
        Some(if *x < 0 { -root } else { root })
    }

    /// `{$arctan(x)$}`, using `{$arctan(x) = plus.minus pi/2 - arctan(1/x)$}` for `{$|x| > 1$}`, then
    /// `{$arctan(y) = 2 arctan(y / (1 + sqrt(1 + y^2)))$}` to make the Taylor series converge faster.
    fn arctan(self, x: &Rational) -> Rational {
        // Odd, and the Taylor series needs a non-negative argument: shifts round down, so negative terms never
        // reach zero
        if *x < 0 {
            return -self.arctan(&-x);
        }
        if *x > 1 {
            let half_pi = self.to_rational(self.pi() >> 1_u64);
            return half_pi - self.arctan(&x.reciprocal());
        }
        let mut y = self.from_rational(x);
        for _ in 0..HALVINGS / 2 {
            // `{$sqrt(1 + y^2) 2^"bits" = sqrt((1 + y^2) 2^(2 "bits"))$}`
            let square = (self.one() + self.mul(&y, &y)) << self.bits;
            let sqrt = Integer::from(square.unsigned_abs().floor_root(2));
            y = self.div(&y, &(self.one() + sqrt));
        }
        let y2 = self.mul(&y, &y);
        let mut power = y;
        let mut sum = Integer::ZERO;
        let mut k = 0_u64;
        while power != 0 {
            let term = &power / Integer::from(2 * k + 1);
            if k % 2 == 0 {
                sum += term;
            } else {
                sum -= term;
            }
            power = self.mul(&power, &y2);
            k += 1;
        }
        self.to_rational(sum << (HALVINGS / 2))
    }

    /// `{$"erf"(x) = 2/sqrt(pi) sum_k (-1)^k x^(2 k + 1) / (k! (2 k + 1))$}`, or `{$"erfi"(x)$}` (`imaginary`)
    /// without the signs. The alternating series loses about `{$x^2 log_2 e$}` bits to cancellation, which are
    /// added to the working precision; `{$"erf"(x) = plus.minus 1$}` up to `{$2^(-1000)$}` for `{$|x| > 27$}`.
    fn erf(self, x: &Rational, imaginary: bool) -> Option<Rational> {
        if *x < 0 {
            return self.erf(&-x, imaginary).map(|y| -y);
        }
        let square = x * x;
        if !imaginary && square > 27 * 27 {
            return Some(Rational::ONE);
        }
        if square > MAX_EXP_ARGUMENT {
            return None;
        }
        let extra = if imaginary {
            0
        } else {
            u64::try_from(&(square * Rational::from(3) / Rational::from(2)).floor()).ok()? + 1
        };
        let fixed = Self {
            bits: self.bits + extra + GUARD_BITS,
        };
        let y = fixed.from_rational(x);
        let y2 = fixed.mul(&y, &y);
        let mut power = y;
        let mut sum = Integer::ZERO;
        let mut k = 0_u64;
        while power != 0 {
            let term = &power / Integer::from(2 * k + 1);
            if imaginary || k % 2 == 0 {
                sum += term;
            } else {
                sum -= term;
            }
            k += 1;
            power = fixed.mul(&power, &y2) / Integer::from(k);
        }
        // `{$sqrt(pi) 2^"bits" = sqrt(pi 2^(2 "bits"))$}`
        let sqrt_pi = Integer::from((fixed.pi() << fixed.bits).unsigned_abs().floor_root(2));
        Some(fixed.to_rational(fixed.div(&(sum << 1_u64), &sqrt_pi)))
    }

    /// The sine, cosine or exponential integral `{$"Si"(x)$}`, `{$"Ci"(x)$}` (for `{$x > 0$}`) or `{$"Ei"(x)$}`
    /// (for `{$x != 0$}`): their power series, with more bits for the cancellation of their terms of size up to
    /// `{$e^|x|$}`, or their asymptotic series when `{$e^(-|x|)$}` is below the precision.
    fn exponential_integral(self, ident: Symbol, x: &Rational) -> Option<Rational> {
        if ident == Context::SI && *x < 0 {
            return self.exponential_integral(ident, &-x).map(|y| -y);
        }
        if *x == 0 || (ident == Context::CI && *x < 0) {
            return (ident == Context::SI).then_some(Rational::ZERO);
        }
        let magnitude = x.abs();
        if magnitude > MAX_EXP_ARGUMENT {
            return None;
        }
        // `{$e^(-|x|) < 2^(-"bits")$}`
        if magnitude > Rational::from(self.bits + 2 * GUARD_BITS) * Rational::from_signeds(7, 10) {
            return self.asymptotic_exponential_integral(ident, x);
        }
        let extra =
            u64::try_from(&(&magnitude * Rational::from(3) / Rational::from(2)).ceiling()).ok()?;
        let fixed = Self {
            bits: self.bits + extra + GUARD_BITS,
        };
        let y = fixed.from_rational(x);
        let y2 = fixed.mul(&y, &y);
        let mut sum = Integer::ZERO;
        let mut k = 0_u64;
        if ident == Context::SI {
            // `{$sum_k (-1)^k x^(2k+1) / ((2k+1) (2k+1)!)$}`
            let mut power = y;
            while power != 0 {
                let term = &power / Integer::from(2 * k + 1);
                if k % 2 == 0 {
                    sum += term;
                } else {
                    sum -= term;
                }
                power = fixed.mul(&power, &y2) / Integer::from((2 * k + 2) * (2 * k + 3));
                k += 1;
            }
            return Some(fixed.to_rational(sum));
        }
        // `{$gamma + ln|x| + sum_(k >= 1) c_k$}`
        let mut power = fixed.one();
        loop {
            k += 1;
            if ident == Context::CI {
                // `{$c_k = (-1)^k x^(2k) / (2k (2k)!)$}`
                power = fixed.mul(&power, &y2) / Integer::from((2 * k - 1) * (2 * k));
                let term = &power / Integer::from(2 * k);
                if k % 2 == 0 {
                    sum += term;
                } else {
                    sum -= term;
                }
            } else {
                // `{$c_k = x^k / (k k!)$}`
                power = fixed.mul(&power, &y) / Integer::from(k);
                sum += &power / Integer::from(k);
            }
            if power == 0 {
                break;
            }
        }
        let euler_gamma = fixed.from_rational(&-fixed.digamma(&Rational::ONE)?);
        Some(fixed.to_rational(sum + euler_gamma + fixed.ln(&magnitude)))
    }

    /// `{$"Si"(x)$}`, `{$"Ci"(x)$}` or `{$"Ei"(x)$}` for a large `|x|`, `{$x > 0$}` for the first two, by their
    /// asymptotic series: `{$"Si"(x) = pi/2 - f(x) cos x - g(x) sin x$}`, `{$"Ci"(x) = f(x) sin x - g(x) cos x$}`
    /// with `{$f(x) ~ sum_k (-1)^k (2k)! / x^(2k+1)$}` and `{$g(x) ~ sum_k (-1)^k (2k+1)! / x^(2k+2)$}`, and
    /// `{$"Ei"(x) ~ e^x / x sum_k k! / x^k$}`.
    fn asymptotic_exponential_integral(self, ident: Symbol, x: &Rational) -> Option<Rational> {
        let fixed = Self {
            bits: self.bits + GUARD_BITS,
        };
        let inv = fixed.from_rational(&x.reciprocal());
        // The terms `{$t_k = t_(k-1) "ratio"(k) / x$}` from `{$t_1 = 1/x$}` while they decrease, `{$"ratio"(k)$}` giving
        // the factor and whether the sign changes
        let terms = |ratio: &dyn Fn(u64) -> (u64, bool)| {
            let mut term = inv.clone();
            let mut terms = vec![];
            for k in 1..=fixed.bits {
                let size = (&term).unsigned_abs();
                if size == 0
                    || terms
                        .last()
                        .is_some_and(|previous: &Integer| size > previous.unsigned_abs())
                {
                    break;
                }
                terms.push(term.clone());
                let (factor, flip) = ratio(k);
                term = fixed.mul(&term, &inv) * Integer::from(factor);
                if flip {
                    term = -term;
                }
            }
            terms
        };
        if ident == Context::EI {
            // `{$t_k = (k-1)! / x^k$}`
            let series: Integer = terms(&|k| (k, false)).into_iter().sum();
            let exp = fixed.exp(&fixed.from_rational(x))?;
            return Some(fixed.to_rational(fixed.mul(&exp, &series)));
        }
        // `{$t_k = (-1)^(floor((k-1)/2)) (k-1)! / x^k$}`, the odd ones being the terms of `f`, the even ones of `g`
        let (mut f, mut g) = (Integer::ZERO, Integer::ZERO);
        for (k, term) in terms(&|k| (k, k % 2 == 0)).into_iter().enumerate() {
            if k % 2 == 0 {
                f += term;
            } else {
                g += term;
            }
        }
        let (sin, cos) = fixed.sin_cos(x)?;
        let res = if ident == Context::SI {
            (fixed.pi() >> 1_u64) - fixed.mul(&f, &cos) - fixed.mul(&g, &sin)
        } else {
            fixed.mul(&f, &sin) - fixed.mul(&g, &cos)
        };
        Some(fixed.to_rational(res))
    }

    /// The shift `N` such that the asymptotic series of the Gamma family at `{$y = x + N >= Y$}` reach the precision,
    /// their smallest term being about `{$e^(-2 pi Y)$}`. `None` at the poles, non-positive integers.
    fn gamma_shift(self, x: &Rational, extra: u64) -> Option<u64> {
        if *x <= 0 && *x.denominator_ref() == 1 {
            return None;
        }
        let target = Rational::from(self.bits / 8 + 16 + extra);
        if *x >= target {
            Some(0)
        } else {
            u64::try_from(&(&target - x).ceiling()).ok()
        }
    }

    /// Sum the asymptotic series `{$sum_(k >= 1) c_k y^(-2 k)$}` scaled by `{$y^"shift"$}`, `{$c_k$}` given by
    /// `coefficient` (with the Bernoulli number `{$B_(2 k)$}`), stopping when the terms vanish or grow.
    fn asymptotic_sum(
        self,
        y: &Rational,
        start: &Rational,
        coefficient: impl Fn(u64, &Rational) -> Rational,
    ) -> Integer {
        // `{$y^(-2)$}`, then the powers `{$"start" y^(-2 k)$}`
        let inv_square = self.from_rational(&(y * y).reciprocal());
        let mut power = self.from_rational(start);
        let mut sum = Integer::ZERO;
        let mut previous: Option<Natural> = None;
        for k in 1..=self.bits {
            power = self.mul(&power, &inv_square);
            let Ok(index) = usize::try_from(2 * k) else {
                break;
            };
            let c = coefficient(k, &bernoulli(index));
            let term = (Rational::from(power.clone()) * c).floor();
            let size = (&term).unsigned_abs();
            if size == 0 || previous.as_ref().is_some_and(|previous| size > *previous) {
                break;
            }
            sum += term;
            previous = Some(size);
        }
        sum
    }

    /// The Hurwitz zeta function `{$zeta(s, x) = sum_(k >= 0) (x + k)^(-s)$}` for a rational `{$s > 1$}`, with
    /// `{$zeta(s, y) ~ y^(1 - s)/(s - 1) + y^(-s)/2 + sum_k B_(2 k)/(2 k)! s (s + 1) ... (s + 2 k - 2) y^(1 - s - 2 k)$}`.
    /// `x` is only negative for integer `s`.
    fn hurwitz_zeta(self, s: &Rational, x: &Rational) -> Option<Rational> {
        if *s <= 1 {
            return None;
        }
        let extra = u64::try_from(&s.ceiling()).ok()?;
        let n = self.gamma_shift(x, extra)?;
        // In fixed point: the exact terms have different denominators, whose sum grows with each one
        let mut sum = Integer::ZERO;
        for k in 0..n {
            sum += self.from_rational(&self.pow(&(x + Rational::from(k)), &-s)?);
        }
        let sum = self.to_rational(sum);
        let y = x + Rational::from(n);
        let power = self.pow(&y, &-s)?;
        let tail = &power * &y / (s - Rational::ONE) + &power / Rational::from(2);
        let start = &power * &y;
        let series = self.asymptotic_sum(&y, &start, |k, b| {
            // `{$B_(2 k)/(2 k)! s (s + 1) ... (s + 2 k - 2)$}`
            (0..2 * k - 1).fold(b.clone(), |c, j| c * (s + Rational::from(j)))
                / Rational::from(Natural::factorial(2 * k))
        });
        Some(sum + tail + self.to_rational(series))
    }

    /// The digamma function `{$psi(x) = psi(x + N) - sum_(k < N) 1/(x + k)$}`, with
    /// `{$psi(y) ~ ln y - 1/(2 y) - sum_k B_(2 k) / (2 k y^(2 k))$}`.
    fn digamma(self, x: &Rational) -> Option<Rational> {
        let n = self.gamma_shift(x, 0)?;
        // In fixed point: exact sums of `x` with many digits have huge denominators
        let shift = self.to_rational((0..n).fold(Integer::ZERO, |sum, k| {
            sum + self.from_rational(&(x + Rational::from(k)).reciprocal())
        }));
        let y = x + Rational::from(n);
        let series = self.asymptotic_sum(&y, &Rational::ONE, |k, b| -b / Rational::from(2 * k));
        Some(self.to_rational(self.ln(&y) + series) - (&y * Rational::from(2)).reciprocal() - shift)
    }

    /// The polygamma function `{$psi^((m))(x)$}`, `{$psi^((m))(x) = (-1)^(m + 1) m! zeta(m + 1, x)$}` for `{$m >= 1$}`.
    fn polygamma(self, m: u64, x: &Rational) -> Option<Rational> {
        if m == 0 {
            return self.digamma(x);
        }
        let res =
            self.hurwitz_zeta(&Rational::from(m + 1), x)? * Rational::from(Natural::factorial(m));
        Some(if m % 2 == 0 { -res } else { res })
    }

    /// `{$Gamma(x) = Gamma(x + N) / (x (x + 1) ... (x + N - 1))$}`, exact for small positive integers, with
    /// Stirling's series `{$ln Gamma(y) ~ (y - 1/2) ln y - y + ln(2 pi)/2 + sum_k B_(2 k) / (2 k (2 k - 1) y^(2 k - 1))$}`.
    fn gamma(self, x: &Rational) -> Option<Rational> {
        if let Ok(n) = u64::try_from(x)
            && (1..=MAX_EXPONENT).contains(&n)
        {
            return Some(Rational::from(Natural::factorial(n - 1)));
        }
        let n = self.gamma_shift(x, 0)?;
        // `{$x (x + 1) ... (x + N - 1)$}`
        let product = (0..n).fold(Rational::ONE, |product, k| {
            product * (x + Rational::from(k))
        });
        let y = x + Rational::from(n);
        let half = Rational::from_signeds(1, 2);
        let two_pi = Rational::from(self.pi() << 1_u64) >> self.bits;
        let ln_y = self.ln(&y);
        let main = (self.from_rational(&(&y - &half)) * &ln_y) >> self.bits;
        let series = self.asymptotic_sum(&y, &y, |k, b| b / Rational::from(2 * k * (2 * k - 1)));
        let ln_gamma = main - self.from_rational(&y) + (self.ln(&two_pi) >> 1_u64) + series;
        Some(self.to_rational(self.exp(&ln_gamma)?) / product)
    }

    /// `{$W_0(x)$}` for `{$x >= -1/e$}`, or with `principal` false `{$W_(-1)(x)$}` for `{$-1/e <= x < 0$}`, by
    /// Newton's iteration on `{$w e^w = x$}` from a float approximation, kept in the branch (`{$w >= -1$}` or
    /// `{$w <= -1$}`).
    fn lambert_w(self, x: &Rational, principal: bool) -> Option<Rational> {
        if *x == 0 {
            return principal.then_some(Rational::ZERO);
        }
        if !principal && *x > 0 {
            return None;
        }
        // `{$e x + 1 >= 0$}`
        let branch = self.exp_rational(&Rational::ONE)? * x + Rational::ONE;
        if branch < 0 {
            return None;
        }
        if branch == 0 {
            return Some(Rational::from(-1));
        }
        let float = |x: &Rational| f64::rounding_from(x, RoundingMode::Nearest).0;
        let x_float = float(x);
        let guess = if !principal {
            if x_float < -0.25 {
                // Series at the branch point `{$-1/e$}`, `{$p$}` changing sign
                let p = -(2. * float(&branch)).sqrt();
                p.mul_add(1. - p / 3. + 11. / 72. * p * p, -1.)
            } else {
                // `{$W_(-1)(x) ~ L_1 - L_2 + L_2 / L_1$}`, `{$L_1 = ln(-x)$}`, `{$L_2 = ln(-L_1)$}`
                let l1 = (-x_float).ln();
                let l2 = (-l1).ln();
                l1 - l2 + l2 / l1
            }
        } else if x_float < 1. {
            // Series at the branch point `{$-1/e$}`
            let p = (2. * float(&branch)).sqrt();
            p.mul_add(1. - p / 3. + 11. / 72. * p * p, -1.)
        } else if x_float < 3. {
            x_float.ln_1p()
        } else {
            // `{$W(x) ~ ln x - ln ln x + (ln ln x) / ln x$}`
            let ln = x_float.ln();
            ln - ln.ln() + ln.ln() / ln
        };
        if !guess.is_finite() {
            return None;
        }
        let target = self.from_rational(x);
        let mut w = self.from_rational(&Rational::try_from(guess).ok()?);
        let one = self.one();
        let minus_one = -&one;
        let in_branch = |w: &Integer| {
            if principal {
                *w > minus_one
            } else {
                *w < minus_one
            }
        };
        if !in_branch(&w) {
            w = &minus_one
                + if principal {
                    &one >> 4_u64
                } else {
                    -(&one >> 4_u64)
                };
        }
        if !principal && x_float >= -0.25 {
            // `{$w + ln(-w) = ln(-x)$}`: `{$w e^w = x$}` loses `x` to the absolute precision when it is tiny, while
            // `{$W_(-1)$}` depends on its relative precision
            let target = self.ln(&-x);
            for _ in 0..self.bits + 64 {
                let ln = self.ln(&self.to_rational(-&w));
                let step = self.div(&self.mul(&w, &(&w + &ln - &target)), &(&w + &one));
                let next = &w - &step;
                w = if in_branch(&next) {
                    next
                } else {
                    (&w + &minus_one) >> 1_u64
                };
                if step.unsigned_abs() <= 1u32 {
                    break;
                }
            }
            return Some(self.to_rational(w));
        }
        for _ in 0..self.bits + 64 {
            let exp = self.exp(&w)?;
            let derivative = self.mul(&exp, &(&w + &one));
            if derivative == 0 {
                break;
            }
            let step = self.div(&(self.mul(&w, &exp) - &target), &derivative);
            let next = &w - &step;
            // Newton's step may cross the branch point, halve the distance to it instead
            w = if in_branch(&next) {
                next
            } else {
                (&w + &minus_one) >> 1_u64
            };
            if step.unsigned_abs() <= 1u32 {
                break;
            }
        }
        Some(self.to_rational(w))
    }

    /// `{$arcsin(x)$}` for `{$|x| <= 1$}`, `{$arcsin(x) = arctan(x / sqrt(1 - x^2))$}`.
    fn arcsin(self, x: &Rational) -> Option<Rational> {
        let cos = self.root(&(Rational::ONE - x * x), 2)?;
        if cos == 0 {
            let half_pi = self.to_rational(self.pi() >> 1_u64);
            return (x.abs() == 1).then(|| if *x > 0 { half_pi } else { -half_pi });
        }
        Some(self.arctan(&(x / cos)))
    }

    /// Evaluate the hyperbolic functions and the inverse trigonometric and hyperbolic functions at `x`, `None`
    /// outside of their domain.
    fn eval_elementary(self, ident: Symbol, x: &Rational) -> Option<Rational> {
        let ln = |y: &Rational| (*y > 0).then(|| self.to_rational(self.ln(y)));
        let half = |y: Rational| y >> 1_u64;
        Some(match ident {
            Context::ATAN => self.arctan(x),
            Context::ERF => self.erf(x, false)?,
            Context::ERFI => self.erf(x, true)?,
            Context::SI | Context::CI | Context::EI => self.exponential_integral(ident, x)?,
            Context::ASIN => self.arcsin(x)?,
            Context::ACOS => self.to_rational(self.pi() >> 1_u64) - self.arcsin(x)?,
            Context::SINH | Context::COSH | Context::TANH => {
                let exp = self.exp_rational(x)?;
                if exp == 0 {
                    return None;
                }
                let inv = exp.clone().reciprocal();
                match ident {
                    Context::SINH => half(exp - inv),
                    Context::COSH => half(exp + inv),
                    _ => (&exp - &inv) / (exp + inv),
                }
            }
            // `{$"asinh"(x) = ln(x + sqrt(x^2 + 1))$}`, odd to avoid a cancellation for negative `x`
            Context::ASINH => {
                let res = ln(&(x.abs() + self.root(&(x * x + Rational::ONE), 2)?))?;
                if *x < 0 { -res } else { res }
            }
            Context::ACOSH if *x >= 1 => ln(&(x + self.root(&(x * x - Rational::ONE), 2)?))?,
            Context::ATANH if x.abs() < 1 => {
                half(ln(&((Rational::ONE + x) / (Rational::ONE - x)))?)
            }
            _ => return None,
        })
    }

    /// `{$e^x$}` for a rational `x`.
    fn exp_rational(self, x: &Rational) -> Option<Rational> {
        if x.abs() > MAX_EXP_ARGUMENT {
            return None;
        }
        // `{$e^x = 1 / e^(-x)$}`, as small values lose their relative precision in fixed point
        if *x < 0 {
            let exp = self.to_rational(self.exp(&self.from_rational(&-x))?);
            return (exp != 0).then(|| exp.reciprocal());
        }
        Some(self.to_rational(self.exp(&self.from_rational(x))?))
    }

    /// `{$b^e$}`, exact for integer exponents.
    fn pow(self, base: &Rational, exponant: &Rational) -> Option<Rational> {
        if *base == 0 {
            return (*exponant > 0).then_some(Rational::ZERO);
        }
        // `{$b^(-e) = (1/b)^e$}`, as roots of small values lose their precision in fixed point
        if *exponant < 0 {
            return self.pow(&base.reciprocal(), &-exponant);
        }
        let (num, den) = exponant.numerator_and_denominator_ref();
        if *num <= MAX_EXPONENT && *den <= MAX_ROOT {
            let num = i64::try_from(num).ok()?;
            let den = u64::try_from(den).ok()?;
            let power = Pow::pow(base.clone(), num);
            let res = if den == 1 {
                power
            } else {
                self.root(&power, den)?
            };
            return Some(if *exponant < 0 {
                Pow::pow(res, -1_i64)
            } else {
                res
            });
        }
        if *base < 0 {
            return None;
        }
        self.exp_rational(&(exponant * self.to_rational(self.ln(base))))
    }

    /// `{$e^u$}` for a rational `u`, as a rational with a relative precision of about `{$2^(-"bits")$}`, even
    /// for negative `u`.
    fn exp_signed(self, u: &Rational) -> Option<Rational> {
        if *u < 0 {
            return Some(self.exp_rational(&-u)?.reciprocal());
        }
        self.exp_rational(u)
    }

    /// `{$integral_a^b f dif x$}` with a double exponential quadrature, the trapezoidal rule in `s` after the
    /// substitution `{$x = (a + b) / 2 + (b - a) / 2 tanh(pi/2 sinh s)$}` (tanh-sinh), `{$x = a + exp(pi/2 sinh s)$}`
    /// for `{$b = oo$}` (exp-sinh, and `{$x = b - exp(pi/2 sinh s)$}` for `{$a = -oo$}`), and
    /// `{$x = sinh(pi/2 sinh s)$}` on `{$RR$}` (sinh-sinh). The step is halved until two results agree to half of
    /// the precision, the error being roughly squared at each step, so integrands must be smooth inside the
    /// interval. Slowly decaying oscillations, like `{$sin(x) / x$}` on `{$[0, oo)$}`, don't converge.
    fn integrate(
        self,
        f: &Term<Real>,
        x: Symbol,
        a: &Term<Real>,
        b: &Term<Real>,
    ) -> Option<Rational> {
        let oo = Term::Symbol(SymbolTerm::new(Context::OO, super::R));
        let infinity = |t: &Term<Real>| {
            if *t == oo {
                Some(1)
            } else if *t == -&oo {
                Some(-1)
            } else {
                None
            }
        };
        let (a_infinity, b_infinity) = (infinity(a), infinity(b));
        if a_infinity == Some(1) || b_infinity == Some(-1) {
            return if a == b {
                Some(Rational::ZERO)
            } else {
                self.integrate(f, x, b, a).map(|res| -res)
            };
        }
        let bound = |t: &Term<Real>| self.value(t);
        let kind = match (a_infinity, b_infinity) {
            (None, None) => Quadrature::Finite(bound(a)?, bound(b)?),
            (None, Some(_)) => Quadrature::Right(bound(a)?),
            (Some(_), None) => Quadrature::Left(bound(b)?),
            (Some(_), Some(_)) => Quadrature::Whole,
        };
        let eval =
            |node: Rational| self.value(&bind(f, x, &Term::Value(Value::new(node, super::R))));
        let pi = self.to_rational(self.pi());
        let half_pi = &pi >> 1_u64;
        // `{$f(x(s)) x'(s)$}`, plus the symmetric node for finite intervals
        let point = |s: &Rational| -> Option<Rational> {
            let es = self.exp_signed(s)?;
            let inverse = (&es).reciprocal();
            let (sinh, cosh) = ((&es - &inverse) >> 1_u64, (es + inverse) >> 1_u64);
            let u = &half_pi * sinh;
            Some(match &kind {
                Quadrature::Finite(a, b) => {
                    // `{$q = e^(2u)$}`, nodes `{$b - (b - a) / (q + 1)$}` and `{$a + (b - a) / (q + 1)$}`
                    let q = self.exp_signed(&(u << 1_u64))?;
                    let length = b - a;
                    let d = &length / (&q + Rational::ONE);
                    let weight = &length * &pi * cosh * &q / Pow::pow(q + Rational::ONE, 2_u64);
                    if *s == 0 {
                        eval(a + d)? * weight
                    } else {
                        (eval(b - &d)? + eval(a + d)?) * weight
                    }
                }
                Quadrature::Right(a) => {
                    let e = self.exp_signed(&u)?;
                    eval(a + &e)? * e * &half_pi * cosh
                }
                Quadrature::Left(b) => {
                    let e = self.exp_signed(&u)?;
                    eval(b - &e)? * e * &half_pi * cosh
                }
                Quadrature::Whole => {
                    let e = self.exp_signed(&u)?;
                    let inverse = (&e).reciprocal();
                    eval((&e - &inverse) >> 1_u64)? * ((e + inverse) >> 1_u64) * &half_pi * cosh
                }
            })
        };
        let symmetric = matches!(kind, Quadrature::Finite(..));
        let mut sum = Integer::ZERO;
        let mut previous: Option<Rational> = None;
        let tolerance = Rational::ONE >> (self.bits / 2);
        for level in 0..=MAX_QUADRATURE_LEVELS {
            let h = Rational::ONE >> level;
            let (first, step) = if level == 0 { (0, 1) } else { (1, 2) };
            let directions: &[i64] = if symmetric { &[1] } else { &[1, -1] };
            for &direction in directions {
                let mut zeros = 0;
                let mut k = if level == 0 && direction == -1 {
                    1
                } else {
                    first
                };
                loop {
                    let s = Rational::from(direction * k) * &h;
                    if (&s).abs() > MAX_QUADRATURE_S {
                        break;
                    }
                    // Far nodes may overflow, like `{$exp(-x^2)$}` for a huge `x`, once the terms vanished
                    let Some(term) = point(&s) else {
                        if zeros > 0 {
                            break;
                        }
                        return None;
                    };
                    let term = self.from_rational(&term);
                    if term == 0 {
                        zeros += 1;
                        if zeros >= 2 {
                            break;
                        }
                    } else {
                        zeros = 0;
                    }
                    sum += term;
                    k += step;
                }
            }
            let res = self.to_rational(sum.clone()) * &h;
            if let Some(previous) = &previous
                && level >= MIN_QUADRATURE_LEVELS
                && (&res - previous).abs() < tolerance
            {
                return Some(res);
            }
            previous = Some(res);
        }
        None
    }

    /// `{$sum_(k = a)^oo f$}` by its partial sums, until [`NEGLIGIBLE_TERMS`] consecutive terms are below the
    /// precision. `None` when they don't become negligible after [`MAX_SUM_TERMS`] terms, outside of the disk of
    /// convergence of a series. The radius bounds the errors of the terms added, but the tail is only estimated.
    fn infinite_sum(self, f: &Term<Real>, k: Symbol, a: &Term<Real>) -> Option<Ball> {
        let a = Integer::try_from(&self.value(a)?).ok()?;
        let mut sum = Integer::ZERO;
        let mut rad = Rational::ZERO;
        let mut negligible = 0;
        for j in 0..MAX_SUM_TERMS {
            let index = Term::Value(Value::new(Rational::from(&a + Integer::from(j)), super::R));
            let term = self.evaluate(&bind(f, k, &index))?;
            rad += &term.rad;
            let term = self.from_rational(&term.mid);
            // Rounded down, tiny negative terms are -1
            if (&term).unsigned_abs() <= 1u32 {
                negligible += 1;
                if negligible >= NEGLIGIBLE_TERMS {
                    let sum = self.to_rational(sum);
                    // One unit per term rounded down, and the estimated tail
                    let rounding = Rational::from(j + 1) >> self.bits;
                    let tail = self.estimated_error(&sum);
                    return Some(Ball::new(sum, rad + rounding + tail));
                }
            } else {
                negligible = 0;
            }
            sum += term;
        }
        None
    }

    /// `{$sum_(k = a)^b f$}` for integer bounds, at most [`MAX_SUM_TERMS`] terms.
    fn finite_sum(self, f: &Term<Real>, k: Symbol, a: &Term<Real>, b: &Term<Real>) -> Option<Ball> {
        let (a, b) = (self.value(a)?, self.value(b)?);
        let (a, b) = (Integer::try_from(&a).ok()?, Integer::try_from(&b).ok()?);
        if &b - &a >= MAX_SUM_TERMS {
            return None;
        }
        let mut sum = Integer::ZERO;
        let mut rad = Rational::ZERO;
        let mut count = 0_u64;
        let mut index = a;
        while index <= b {
            let value = Term::Value(Value::new(Rational::from(&index), super::R));
            let term = self.evaluate(&bind(f, k, &value))?;
            rad += &term.rad;
            sum += self.from_rational(&term.mid);
            count += 1;
            index += Integer::from(1);
        }
        // One unit per term rounded down
        Some(Ball::new(
            self.to_rational(sum),
            rad + (Rational::from(count) >> self.bits),
        ))
    }

    /// The value of a term at the center of its ball, for the algorithms estimating their own errors.
    fn value(self, term: &Term<Real>) -> Option<Rational> {
        self.evaluate(term).map(|ball| ball.mid)
    }

    /// `f` at the center of `x`, a primitive whose rounding errors are bounded by `error` at its value, plus the
    /// radius of `x` times `slope`, a bound of `{$|f'|$}` on the ball given the value at its center (only called
    /// when `x` isn't exact).
    fn unary(
        x: &Ball,
        f: impl FnOnce(&Rational) -> Option<Rational>,
        error: impl FnOnce(&Rational) -> Rational,
        slope: impl FnOnce(&Rational) -> Option<Rational>,
    ) -> Option<Ball> {
        let v = f(&x.mid)?;
        let mut rad = error(&v);
        if x.rad != 0 {
            let Some(slope) = slope(&v) else {
                return imprecise();
            };
            rad += slope * &x.rad;
        }
        Some(Ball::new(v, rad))
    }

    /// `f`, an algorithm without an error bound (see [`Ball`]), at the center of `x`: its estimated error, plus for an
    /// inexact `x` its radius times twice the slope of `f` at the center, estimated by a difference at a low
    /// precision, `f` being smooth there.
    fn estimated(self, x: &Ball, f: impl Fn(Self, &Rational) -> Option<Rational>) -> Option<Ball> {
        let v = f(self, &x.mid)?;
        let mut rad = self.estimated_error(&v);
        if x.rad != 0 {
            let low = Self {
                bits: 2 * SLOPE_STEP_BITS,
            };
            // A point at a small distance, rounded to the low precision so that exact operations on it are cheap
            let step = (&x.mid).abs().max(Rational::ONE) >> SLOPE_STEP_BITS;
            let point = low.to_rational(low.from_rational(&(&x.mid + step.max(x.rad.clone()))));
            let h = &point - &x.mid;
            let Some(near) = f(low, &point) else {
                return imprecise();
            };
            let slope = (near - &v).abs() / h;
            rad += upper(&slope) * &x.rad * Rational::from(2);
        }
        Some(Ball::new(v, rad))
    }

    /// `f` like [`Self::estimated`], but with twice the largest variation to the bounds of `x`, for a function
    /// whose slope varies a lot on the ball.
    fn estimated_at_bounds(
        self,
        x: &Ball,
        f: impl Fn(&Rational) -> Option<Rational>,
    ) -> Option<Ball> {
        let v = f(&x.mid)?;
        let mut rad = self.estimated_error(&v);
        if x.rad != 0 {
            let (Some(lo), Some(hi)) = (f(&x.lo()), f(&x.hi())) else {
                return imprecise();
            };
            rad += (&lo - &v).abs().max((&hi - &v).abs()) << 1_u64;
        }
        Some(Ball::new(v, rad))
    }

    /// Whether the ball contains a pole of `{$Gamma$}`, a non-positive integer.
    fn has_gamma_pole(x: &Ball) -> bool {
        let first = Rational::from(Ceiling::ceiling(x.lo()));
        first <= 0 && first <= x.hi()
    }

    /// `{$e^x$}`, with a relative error.
    fn exp_ball(self, x: &Ball) -> Option<Ball> {
        if x.rad > Rational::from_signeds(1, 2) {
            return imprecise();
        }
        // `{$|e^(m + d) - e^m| <= e^m (e^r - 1) <= 2 r e^m$}` for `{$|d| <= r <= 1/2$}`
        Self::unary(
            x,
            |m| self.exp_rational(m),
            |v| self.relative_error(v),
            |v| Some(upper(v) << 1_u64),
        )
    }

    /// `{$ln(x)$}` for a positive `x`.
    fn ln_ball(self, x: &Ball) -> Option<Ball> {
        if x.mid <= 0 {
            return None;
        }
        if x.lo() <= 0 && x.rad != 0 {
            return imprecise();
        }
        Self::unary(
            x,
            |m| Some(self.to_rational(self.ln(m))),
            |v| self.absolute_error(v),
            |_| Some(x.lo().reciprocal()),
        )
    }

    /// `{$x^n$}` for a natural `n`, exact for an exact `x`.
    fn int_pow(x: &Ball, n: u64) -> Ball {
        let mid = Pow::pow(x.mid.clone(), n);
        if x.rad == 0 || n == 0 {
            return Ball::exact(mid);
        }
        // `{$|y^n - m^n| <= n M^(n - 1) r$}`, `M` bounding `|y|`
        let magnitude = round_up(x.magnitude());
        let rad = Rational::from(n) * Pow::pow(magnitude, n - 1) * &x.rad;
        Ball::new(mid, rad)
    }

    /// `{$root(n, x)$}`, `x` being negative only for odd `n`, with a relative error for an exact `x`. Roots are
    /// monotone, so an inexact `x` gives the roots of its bounds, the lower one clamped to 0 for even roots.
    fn root_ball(self, x: &Ball, n: u64) -> Option<Ball> {
        if x.rad == 0 {
            let v = self.root(&x.mid, n)?;
            let rad = self.relative_error(&v);
            return Some(Ball::new(v, rad));
        }
        let low = x.min_magnitude();
        if low > 0 {
            // `{$|root(n, y)'| = |root(n, y)| / (n |y|) <= |root(n, m)| / (n (|m| - r)) (|m| / (|m| - r))$}`, roots
            // growing slower than `y`
            let v = self.root(&x.mid, n)?;
            let slope = upper(&v) * (&x.mid).abs() / (Rational::from(n) * &low * &low);
            let rad = self.relative_error(&v) + slope * &x.rad;
            return Some(Ball::new(v, rad));
        }
        let (mut lo, hi) = (x.lo(), x.hi());
        if n % 2 == 0 && lo < 0 {
            if hi < 0 {
                return None;
            }
            lo = Rational::ZERO;
        }
        let (a, b) = (self.root(&lo, n)?, self.root(&hi, n)?);
        let a = &a - self.relative_error(&a);
        let b = &b + self.relative_error(&b);
        Some(Ball::new((&a + &b) >> 1_u64, (b - a) >> 1_u64))
    }

    /// `{$b^e$}`, exact for an exact base and a small integer exponent.
    fn pow_ball(self, base: &Ball, exponant: &Ball) -> Option<Ball> {
        if base.rad == 0 && base.mid == 0 {
            return (exponant.lo() > 0).then(|| Ball::exact(Rational::ZERO));
        }
        // `{$b^e = exp(e ln b)$}`
        let general = || self.exp_ball(&self.ln_ball(base)?.mul(exponant));
        if exponant.rad != 0 {
            return general();
        }
        let e = &exponant.mid;
        if *e < 0 {
            return self.pow_ball(base, &Ball::exact(-e))?.reciprocal();
        }
        let (num, den) = e.numerator_and_denominator_ref();
        if *num <= MAX_EXPONENT && *den <= MAX_ROOT {
            let power = Self::int_pow(base, u64::try_from(num).ok()?);
            let den = u64::try_from(den).ok()?;
            return if den == 1 {
                Some(power)
            } else {
                self.root_ball(&power, den)
            };
        }
        general()
    }

    /// `{$sin$}`, `{$cos$}` or `{$tan$}` of `x`.
    fn trig_ball(self, ident: Symbol, x: &Ball) -> Option<Ball> {
        let (sin, cos) = self.sin_cos(&x.mid)?;
        let (sin, cos) = (self.to_rational(sin), self.to_rational(cos));
        let error = self.absolute_error(&Rational::ONE);
        match ident {
            Context::SIN => Some(Ball::new(sin, error + &x.rad)),
            Context::COS => Some(Ball::new(cos, error + &x.rad)),
            _ => {
                // `{$|cos| >= d$}` on the ball and at the approximation
                let d = (&cos).abs() - &error - &x.rad;
                if d <= 0 {
                    return imprecise();
                }
                // The error of the quotient of the approximations, then of the argument (`{$tan' = 1/cos^2$}`)
                let quotient = &error * (Rational::ONE + ((&sin).abs() + &error) / &d) / &d;
                let rad = quotient + &x.rad / (&d * &d);
                Some(Ball::new(sin / cos, rad))
            }
        }
    }

    /// The hyperbolic functions and the inverse trigonometric and hyperbolic functions, `erf`, `erfi`, `Si`, `Ci`
    /// and `Ei` of `x`, `None` outside of their domain.
    fn elementary_ball(self, ident: Symbol, x: &Ball) -> Option<Ball> {
        let f = |m: &Rational| self.eval_elementary(ident, m);
        let absolute = |v: &Rational| self.absolute_error(v);
        let estimated = |v: &Rational| self.estimated_error(v);
        let one = |_: &Rational| Some(Rational::ONE);
        let reach = x.magnitude();
        // `{$1 - (|m| + r)^2$}`, positive when the ball is inside `{$(-1, 1)$}`
        let inside = || {
            let s = Rational::ONE - &reach * &reach;
            (s > 0).then_some(s)
        };
        match ident {
            Context::ATAN | Context::TANH | Context::ASINH => Self::unary(x, f, absolute, one),
            // `{$1/sqrt(1 - y^2) <= 1/(1 - y^2)$}`
            Context::ASIN | Context::ACOS => {
                Self::unary(x, f, absolute, |_| inside().map(Reciprocal::reciprocal))
            }
            Context::ATANH => Self::unary(x, f, absolute, |_| inside().map(Reciprocal::reciprocal)),
            Context::ACOSH => Self::unary(x, f, absolute, |_| {
                // `{$1/sqrt(y^2 - 1)$}`, at most `{$1/(y^2 - 1)$}` below 1
                let lo = x.lo();
                let t = &lo * &lo - Rational::ONE;
                (lo > 1).then(|| {
                    if t >= 1 {
                        Rational::ONE
                    } else {
                        t.reciprocal()
                    }
                })
            }),
            // `{$|sinh|, cosh <= cosh(|m| + r) <= e^r cosh m <= 2 (|v| + 1)$}` for `{$r <= 1/2$}`
            Context::SINH | Context::COSH => Self::unary(
                x,
                f,
                |v| absolute(v) << 1_u64,
                |v| {
                    (x.rad <= Rational::from_signeds(1, 2))
                        .then(|| upper(&(v.abs() + Rational::ONE)) << 1_u64)
                },
            ),
            // `{$2/sqrt(pi) < 2$}`
            Context::ERF => Self::unary(x, f, estimated, |_| Some(Rational::from(2))),
            Context::ERFI => Self::unary(x, f, estimated, |_| {
                let square = round_up(&reach * &reach);
                Some(upper(&self.exp_rational(&square)?) << 1_u64)
            }),
            // `{$|sin(y)/y| <= 1$}`
            Context::SI => Self::unary(x, f, estimated, one),
            Context::CI => Self::unary(x, f, estimated, |_| {
                let lo = x.lo();
                (lo > 0).then(|| lo.reciprocal())
            }),
            Context::EI => Self::unary(x, f, estimated, |_| {
                let low = x.min_magnitude();
                (low > 0).then_some(())?;
                Some(upper(&self.exp_rational(&round_up(reach.clone()))?) / low)
            }),
            _ => None,
        }
    }

    /// Evaluate a term without symbols, other than builtin constants, as a ball containing its value.
    fn evaluate(self, term: &Term<Real>) -> Option<Ball> {
        match term {
            Term::Value(value) => Some(Ball::exact(value.value.clone())),
            Term::Symbol(symbol) => match symbol.symbol {
                Context::PI => {
                    let pi = self.to_rational(self.pi());
                    let rad = self.absolute_error(&pi);
                    Some(Ball::new(pi, rad))
                }
                Context::E => self.exp_ball(&Ball::exact(Rational::ONE)),
                // `{$gamma = -psi(1)$}`
                Context::EULER_GAMMA => self.estimated(&Ball::exact(Rational::ONE), |fixed, x| {
                    Some(-fixed.digamma(x)?)
                }),
                _ => None,
            },
            Term::Add(add) => add
                .iter()
                .try_fold(Ball::exact(Rational::ZERO), |sum, term| {
                    Some(sum.add(&self.evaluate(term)?))
                }),
            Term::Mul(mul) => mul
                .iter()
                .try_fold(Ball::exact(mul.coefficient.clone()), |product, factor| {
                    Some(product.mul(&self.evaluate(factor)?))
                }),
            Term::Pow(pow) => {
                self.pow_ball(&self.evaluate(&pow.base)?, &self.evaluate(&pow.exponant)?)
            }
            Term::Fun(fun) => self.evaluate_function(fun.as_ref()),
        }
    }

    /// Evaluate a function of terms without symbols, see [`Self::evaluate`].
    #[allow(clippy::too_many_lines)]
    fn evaluate_function(self, fun: &dyn crate::term::Function<Real>) -> Option<Ball> {
        let args = fun.get_args::<Real>()?;
        let set = fun.get_set();
        // The value of the builtin at values, by normalization
        let at = |ident: Symbol, values: Vec<Rational>| -> Option<Rational> {
            let args = values
                .into_iter()
                .map(|v| Term::Value(Value::new(v, set)))
                .collect();
            match Term::Fun(Box::new(Fun::new(ident, args, set))).normalize() {
                Term::Value(value) => Some(value.value),
                _ => None,
            }
        };
        match (fun.get_ident(), args.as_slice()) {
            (Context::EXP, [x]) => self.exp_ball(&self.evaluate(x)?),
            (Context::LN, [x]) => self.ln_ball(&self.evaluate(x)?),
            (ident @ (Context::SIN | Context::COS | Context::TAN), [x]) => {
                self.trig_ball(ident, &self.evaluate(x)?)
            }
            (ident, args) if ident == Context::real_root() => {
                let v = super::rootof::approximate(args, self.bits)?;
                Some(Ball::new(v, Rational::ONE >> self.bits))
            }
            (Context::LAMBERTW, [x]) => self.lambert_ball(&self.evaluate(x)?, true),
            (Context::LAMBERTW, [x, k]) => match self.evaluate(k)? {
                k if k.rad == 0 && k.mid == 0 => self.lambert_ball(&self.evaluate(x)?, true),
                k if k.rad == 0 && k.mid == -1 => self.lambert_ball(&self.evaluate(x)?, false),
                _ => None,
            },
            (ident, [x]) if ident == Context::lambertw_m1() => {
                self.lambert_ball(&self.evaluate(x)?, false)
            }
            (Context::GAMMA, [x]) => {
                let x = self.evaluate(x)?;
                if x.rad == 0
                    && let Ok(n) = u64::try_from(&x.mid)
                    && (1..=MAX_EXPONENT).contains(&n)
                {
                    return Some(Ball::exact(Rational::from(Natural::factorial(n - 1))));
                }
                if x.rad != 0 && Self::has_gamma_pole(&x) {
                    return imprecise();
                }
                self.estimated(&x, Self::gamma)
            }
            (Context::FACTORIAL, [x]) => {
                let x = self.evaluate(x)?;
                // Exact for natural numbers, like the terms of series
                if x.rad == 0
                    && let Ok(n) = u64::try_from(&x.mid)
                    && n <= MAX_EXACT_FACTORIAL
                {
                    return Some(Ball::exact(Rational::from(Natural::factorial(n))));
                }
                let shifted = x.add(&Ball::exact(Rational::ONE));
                if shifted.rad != 0 && Self::has_gamma_pole(&shifted) {
                    return imprecise();
                }
                self.estimated(&shifted, Self::gamma)
            }
            (Context::BINOMIAL, [n, k]) => {
                let (n, k) = (self.evaluate(n)?, self.evaluate(k)?);
                if n.rad == 0
                    && k.rad == 0
                    && *n.mid.denominator_ref() == 1
                    && *k.mid.denominator_ref() == 1
                {
                    // Exact, also when `{$Gamma$}` has poles
                    return at(Context::BINOMIAL, vec![n.mid, k.mid]).map(Ball::exact);
                }
                // `{$binom(n, k) = Gamma(n + 1) / (Gamma(k + 1) Gamma(n - k + 1))$}`
                let one = Rational::ONE;
                let binomial = |n: &Rational, k: &Rational| {
                    Some(
                        self.gamma(&(n + &one))?
                            / (self.gamma(&(k + &one))? * self.gamma(&(n - k + &one))?),
                    )
                };
                let v = binomial(&n.mid, &k.mid)?;
                let mut rad = self.estimated_error(&v);
                // Twice the largest variations in `n` and in `k`
                let mut points = vec![];
                if n.rad != 0 {
                    points.extend([(n.lo(), k.mid.clone()), (n.hi(), k.mid.clone())]);
                }
                if k.rad != 0 {
                    points.extend([(n.mid.clone(), k.lo()), (n.mid, k.hi())]);
                }
                for (a, b) in points {
                    rad += (binomial(&a, &b)? - &v).abs() << 1_u64;
                }
                Some(Ball::new(v, rad))
            }
            (Context::POLYGAMMA, [m, x]) => {
                let m = self.evaluate(m)?;
                if m.rad != 0 {
                    return None;
                }
                let m = u64::try_from(&m.mid).ok()?;
                let x = self.evaluate(x)?;
                if x.rad != 0 && Self::has_gamma_pole(&x) {
                    return imprecise();
                }
                self.estimated(&x, |fixed, x| fixed.polygamma(m, x))
            }
            (Context::ZETA, [s]) => {
                let s = self.evaluate(s)?;
                if s.rad == 0 && *s.mid.denominator_ref() == 1 && s.mid <= 0 {
                    // Exact values from the Bernoulli numbers
                    return at(Context::ZETA, vec![s.mid]).map(Ball::exact);
                }
                self.estimated(&s, |fixed, s| fixed.hurwitz_zeta(s, &Rational::ONE))
            }
            (Context::INTEGRATE, [f, Term::Symbol(x), a, b]) => {
                let v = self.integrate(f, x.symbol, a, b)?;
                // The step is halved until two results agree to half of the precision
                let rad = ((&v).abs() + Rational::ONE) >> (self.bits / 2).saturating_sub(2);
                Some(Ball::new(v, rad))
            }
            (ident, [f, Term::Symbol(k), a, _]) if ident == Context::held_sum() => {
                self.infinite_sum(f, k.symbol, a)
            }
            // The finite sums in the general terms of products of series
            (Context::SUM, [f, Term::Symbol(k), a, b]) => self.finite_sum(f, k.symbol, a, b),
            (
                ident @ (Context::ASIN
                | Context::ACOS
                | Context::ATAN
                | Context::SINH
                | Context::COSH
                | Context::TANH
                | Context::ASINH
                | Context::ACOSH
                | Context::ATANH
                | Context::ERF
                | Context::ERFI
                | Context::SI
                | Context::CI
                | Context::EI),
                [x],
            ) => self.elementary_ball(ident, &self.evaluate(x)?),
            (ident, args) => {
                // Other builtins, like `abs` or `floor`, are evaluated on the values of their arguments
                let balls = args
                    .iter()
                    .map(|arg| self.evaluate(arg))
                    .collect::<Option<Vec<_>>>()?;
                let mids = balls.iter().map(|ball| ball.mid.clone()).collect();
                if balls.iter().all(|ball| ball.rad == 0) {
                    return at(ident, mids).map(Ball::exact);
                }
                match (ident, balls.as_slice()) {
                    // Steps, monotone: constant on the ball when equal at its bounds, unknown near a jump
                    (Context::FLOOR | Context::CEIL | Context::SIGN, [x]) => {
                        let (lo, hi) = (at(ident, vec![x.lo()])?, at(ident, vec![x.hi()])?);
                        if lo == hi {
                            Some(Ball::exact(lo))
                        } else {
                            imprecise()
                        }
                    }
                    // 1-Lipschitz
                    (Context::ABS | Context::MIN | Context::MAX, _) => {
                        let rad = balls.iter().map(|ball| ball.rad.clone()).max()?;
                        Some(Ball::new(at(ident, mids)?, rad))
                    }
                    _ => None,
                }
            }
        }
    }

    /// `{$W_0(x)$}`, or `{$W_(-1)(x)$}` without `principal`, see [`Self::lambert_w`]. Its error is estimated from
    /// the values at the bounds of `x` widened by the relative precision, since it grows near the branch point
    /// `{$-1/e$}`, and `{$W_(-1)$}` of tiny arguments depends on their relative precision.
    fn lambert_ball(self, x: &Ball, principal: bool) -> Option<Ball> {
        if x.rad == 0 && x.mid == 0 {
            return principal.then(|| Ball::exact(Rational::ZERO));
        }
        let precision = (&x.mid).abs() >> self.bits.saturating_sub(GUARD_BITS);
        let widened = Ball {
            mid: x.mid.clone(),
            rad: (&x.rad).max(&precision).clone(),
        };
        self.estimated_at_bounds(&widened, |x| self.lambert_w(x, principal))
    }
}

/// `term` with the symbol `x` replaced by `value`, also in exponents, without normalizing: normalizing powers like
/// `{$x^x$}` of exact nodes with huge denominators would be too expensive, and [`Fixed::evaluate`] doesn't need it.
fn bind(term: &Term<Real>, x: Symbol, value: &Term<Real>) -> Term<Real> {
    if !term.symbols().contains(&x) {
        return term.clone();
    }
    let set = term.get_set();
    match term {
        Term::Value(_) => term.clone(),
        Term::Symbol(_) => value.clone(),
        Term::Add(add) => Term::Add(Add::new(
            add.iter().map(|t| bind(t, x, value)).collect(),
            set,
        )),
        Term::Mul(mul) => Term::Mul(Mul::new(
            mul.coefficient.clone(),
            mul.iter().map(|t| bind(t, x, value)).collect(),
            set,
        )),
        Term::Pow(pow) => Term::Pow(crate::term::Pow::new(
            bind(&pow.base, x, value),
            bind(&pow.exponant, x, value),
            set,
        )),
        Term::Fun(fun) => fun.get_args::<Real>().map_or_else(
            || term.clone(),
            |args| {
                Term::Fun(Box::new(Fun::new(
                    fun.get_ident(),
                    args.iter().map(|t| bind(t, x, value)).collect(),
                    set,
                )))
            },
        ),
    }
}

/// Number of bits needed to get `digits` significant decimal digits.
const fn bits_for_digits(digits: u64) -> u64 {
    // `{$log_2(10) < 3.3220$}`
    digits * 33_220 / 10_000 + 1
}

/// The number of significant bits of the center of a ball which is known to be non-zero, `{$log_2 |m| - log_2 r$}`
/// rounded down, `None` for an exact ball.
fn significant_bits(ball: &Ball) -> Option<i64> {
    (ball.rad != 0).then(|| (&ball.mid).abs().floor_log_base_2() - (&ball.rad).ceiling_log_base_2())
}

/// Approximate a term without symbols, other than builtin constants, to `digits` significant digits. Return `None`
/// if the term contains symbols or can't be evaluated, like `{$ln(-1)$}`, and 0 when it is indistinguishable from
/// zero at the maximum precision.
///
/// The working precision is raised until the [`Ball`] of the evaluation excludes 0 and has the needed relative
/// precision, so a non-zero result has the sign of the term, and its digits are right up to the last one (rounded)
/// for the operations bounding their errors (see [`Ball`]). At the maximum precision, a ball excluding 0 without
/// enough precision gives only its certain digits.
pub fn approximate(term: &Term<Real>, digits: u64) -> Option<Rational> {
    let needed = bits_for_digits(digits) + GUARD_BITS / 2;
    // Each term of a held sum is evaluated at the working precision, and more terms are needed as it grows, so a
    // sum below `{$2^(-4 "needed")$}` is zero, like `{$sum (-1)^k pi^(2k + 1)/(2k + 1)!$}`
    let max_bits = if has_held_sum(term) {
        4 * needed
    } else {
        4 * needed + 4096
    };
    let needed_signed = i64::try_from(needed).ok()?;
    let mut bits = needed + GUARD_BITS;
    loop {
        IMPRECISE.set(false);
        let Some(ball) = Fixed { bits }.evaluate(term) else {
            // Too wide balls, like `{$tan$}` near a pole, may be evaluated at a higher precision
            if IMPRECISE.get() && bits < max_bits {
                bits = (2 * bits).min(max_bits);
                continue;
            }
            return None;
        };
        if ball.rad == 0 {
            return Some(round_significant(&ball.mid, digits));
        }
        if ball.contains_zero() {
            // Maybe below the precision, like `{$e^(-70) < 2^(-100)$}`
            if bits >= max_bits {
                // Indistinguishable from zero at the maximum precision, like `{$sin(pi)$}`
                return Some(Rational::ZERO);
            }
            bits = (2 * bits).min(max_bits);
            continue;
        }
        let significant = significant_bits(&ball)?;
        if significant >= needed_signed {
            return Some(round_significant(&ball.mid, digits));
        }
        if bits >= max_bits {
            // Only the certain digits, `{$log_10 2 > 0.3$}`
            let certain = u64::try_from(significant.max(1) * 3 / 10).ok()?.max(1);
            return Some(round_significant(&ball.mid, certain.min(digits)));
        }
        let missing = u64::try_from(needed_signed - significant).ok()?;
        bits = (bits + missing + GUARD_BITS).min(max_bits);
    }
}

/// Whether `term` contains a held sum, the whole series of `series(f, x, a, oo)`.
fn has_held_sum(term: &Term<Real>) -> bool {
    match term {
        Term::Value(_) | Term::Symbol(_) => false,
        Term::Add(add) => add.iter().any(has_held_sum),
        Term::Mul(mul) => mul.iter().any(has_held_sum),
        Term::Pow(pow) => has_held_sum(&pow.base) || has_held_sum(&pow.exponant),
        Term::Fun(fun) => {
            fun.get_ident() == Context::held_sum()
                || fun
                    .get_args::<Real>()
                    .is_some_and(|args| args.iter().any(has_held_sum))
        }
    }
}

/// Evaluate a term like [`approximate`], but in a single evaluation at a precision of about `{$2^(-"bits")$}`, as a
/// [`Ball`] containing its value, which is faster when the value may be zero.
pub fn enclose(term: &Term<Real>, bits: u64) -> Option<Ball> {
    Fixed {
        bits: bits + GUARD_BITS,
    }
    .evaluate(term)
}

/// The center of [`enclose`], an approximation without error bound, for heuristics whose results are checked.
pub fn approximate_fixed(term: &Term<Real>, bits: u64) -> Option<Rational> {
    enclose(term, bits).map(|ball| ball.mid)
}

/// An approximated value, printed as a decimal number.
pub(super) fn approximate_value(value: Rational) -> Term<Real> {
    let mut res = Term::Value(Value::new(value, super::R));
    res.set_approximate(true);
    res
}

/// A set whose terms are approximated by [`approximate_term`], from the approximations of their constants.
pub trait Approximate: crate::field::Ring<ExponantSet = Self> {
    /// The approximation of a constant `term` to `digits` significant digits (in each part), `None` when it isn't
    /// a constant or can't be approximated.
    fn approximate_constant(term: &Term<Self>, digits: u64) -> Option<Term<Self>>;
    /// A coefficient of a product rounded to `digits` significant digits.
    fn round_coefficient(
        coefficient: &<Self::ProductCoefficientSet as crate::field::Set>::Element,
        digits: u64,
    ) -> <Self::ProductCoefficientSet as crate::field::Set>::Element;
    /// Whether `value` is an integer, kept exact as an exponent.
    fn is_integer(value: &Self::Element) -> bool;
}

impl Approximate for Real {
    fn approximate_constant(term: &Term<Self>, digits: u64) -> Option<Term<Self>> {
        approximate(term, digits).map(approximate_value)
    }

    fn round_coefficient(coefficient: &Rational, digits: u64) -> Rational {
        round_significant(coefficient, digits)
    }

    fn is_integer(value: &Rational) -> bool {
        *value.denominator_ref() == 1
    }
}

/// Evaluate `{$"approx"(x, "digits")$}` (see [`approximate_term`]), `None` for invalid arguments.
pub fn eval_approx<T: Approximate>(args: &[Term<T>]) -> Option<Term<T>> {
    profile_scope!("approx");
    let (x, digits) = match args {
        [x] => (x, DEFAULT_DIGITS),
        [x, Term::Value(digits)] => (x, u64::try_from(digits.set.to_i64(&digits.value)?).ok()?),
        _ => return None,
    };
    (1..=MAX_DIGITS)
        .contains(&digits)
        .then(|| approximate_term(x, digits))
}

/// Approximate the numerical parts of `term` to `digits` significant digits, keeping symbols, like
/// `{$x + 1.41421356237310$}` for `{$x + sqrt(2)$}`. Integer exponents are kept exact.
pub fn approximate_term<T: Approximate>(term: &Term<T>, digits: u64) -> Term<T> {
    if let Some(res) = T::approximate_constant(term, digits) {
        return res;
    }
    let set = term.get_set();
    match term {
        Term::Value(_) | Term::Symbol(_) => term.clone(),
        Term::Add(add) => Term::Add(Add::new(
            add.iter()
                .map(|term| approximate_term(term, digits))
                .collect(),
            set,
        ))
        .normalize(),
        Term::Mul(mul) => {
            let mut res = Mul::new(
                T::round_coefficient(&mul.coefficient, digits),
                mul.iter()
                    .map(|factor| approximate_term(factor, digits))
                    .collect(),
                set,
            );
            res.set_approximate(true);
            Term::Mul(res).normalize()
        }
        Term::Pow(pow) => {
            let exponant: &Term<T> = &pow.exponant;
            let exponant = match exponant {
                Term::Value(value) if T::is_integer(&value.value) => exponant.clone(),
                _ => approximate_term(exponant, digits),
            };
            approximate_term(&pow.base, digits).pow(&exponant)
        }
        Term::Fun(fun) => fun.get_args::<T>().map_or_else(
            || term.clone(),
            |args| {
                let args = args
                    .iter()
                    .enumerate()
                    .map(|(i, arg)| {
                        // The order of `{$psi^((m))$}` stays an integer
                        if i == 0 && fun.get_ident() == Context::POLYGAMMA {
                            arg.clone()
                        } else {
                            approximate_term(arg, digits)
                        }
                    })
                    .collect();
                Term::Fun(Box::new(Fun::new(fun.get_ident(), args, set))).normalize()
            },
        ),
    }
}

fn power_of_ten(exponant: i64) -> Rational {
    Pow::pow(Rational::from(10), exponant)
}

/// `{$10^k$}` as a natural number.
fn natural_power_of_ten(k: u64) -> Natural {
    Natural::from(10_u32).pow(k)
}

/// The exponent `e` of the first decimal digit of `{$n / d > 0$}`, `{$10^e <= n / d < 10^(e + 1)$}`. In integers
/// only: the values of `approx` may have millions of digits, and `Rational` arithmetic reduces its results by gcds.
fn decimal_exponent(n: &Natural, d: &Natural) -> i64 {
    // `{$log_2(n / d) - 1 < floor(log_2 n) - floor(log_2 d) < log_2(n / d) + 1$}`, `{$log_10(2) approx 0.30103$}`,
    // then fix the estimate
    let log = i64::try_from(n.floor_log_base_2()).unwrap_or(i64::MAX)
        - i64::try_from(d.floor_log_base_2()).unwrap_or(i64::MAX);
    let mut exponant = log * 30_103 / 100_000;
    // `{$10^|e|$}`
    let mut power = natural_power_of_ten(exponant.unsigned_abs());
    let at_most = |e: i64, power: &Natural| {
        if e >= 0 {
            power * d <= *n
        } else {
            *d <= n * power
        }
    };
    let ten = Natural::from(10_u32);
    while !at_most(exponant, &power) {
        if exponant > 0 {
            power /= &ten;
        } else {
            power *= &ten;
        }
        exponant -= 1;
    }
    loop {
        let next = if exponant >= 0 {
            &power * &ten
        } else {
            &power / &ten
        };
        if !at_most(exponant + 1, &next) {
            return exponant;
        }
        exponant += 1;
        power = next;
    }
}

/// Round `|x|` to `digits` significant digits, returning the digits as an integer `m` and the exponent `e` of the
/// first digit: `{$|x| approx m 10^(e - "digits" + 1)$}`. `x` must be non-zero.
fn decimal_digits(x: &Rational, digits: u64) -> (Natural, i64) {
    let (n, d) = x.numerator_and_denominator_ref();
    let mut exponant = decimal_exponent(n, d);
    let digits = i64::try_from(digits).unwrap_or(i64::MAX);
    // `{$floor(|x| 10^k + 1/2) = floor((2 n 10^k + d) / (2 d))$}`, or with `{$k < 0$}`
    // `{$floor((2 n + d 10^(-k)) / (2 d 10^(-k)))$}`
    let k = digits - 1 - exponant;
    let power = natural_power_of_ten(k.unsigned_abs());
    let (numerator, denominator) = if k >= 0 {
        (n * power, d.clone())
    } else {
        (n.clone(), d * power)
    };
    let mut mantissa = ((numerator << 1_u64) + &denominator) / (denominator << 1_u64);
    if mantissa == natural_power_of_ten(u64::try_from(digits).unwrap_or(0)) {
        // Rounded up to the next power of ten, like `{$9.99 approx 10.0$}`
        mantissa /= Natural::from(10_u32);
        exponant += 1;
    }
    (mantissa, exponant)
}

/// Round `x` to `digits` significant digits.
pub fn round_significant(x: &Rational, digits: u64) -> Rational {
    if *x == 0 {
        return Rational::ZERO;
    }
    let (mantissa, exponant) = decimal_digits(x, digits);
    let res = Rational::from(mantissa)
        * power_of_ten(exponant - i64::try_from(digits).unwrap_or(i64::MAX) + 1);
    if *x < 0 { -res } else { res }
}

/// Number of significant digits of `x` if it is a decimal number with at most [`MAX_DIGITS`] digits.
fn significant_digits(x: &Rational) -> Option<u64> {
    let mut den = x.denominator_ref().clone();
    let twos = den.trailing_zeros().unwrap_or(0);
    den >>= twos;
    let mut fives = 0;
    while (&den).divisible_by(Natural::from(5_u32)) {
        den /= Natural::from(5_u32);
        fives += 1;
        if fives > MAX_DIGITS {
            return None;
        }
    }
    if den != 1 || twos > MAX_DIGITS {
        return None;
    }
    // `{$|x| 10^t$}`, an integer, in integers only (see `decimal_exponent`)
    let mut integer =
        x.numerator_ref() * natural_power_of_ten(twos.max(fives)) / x.denominator_ref();
    if integer == 0 {
        return Some(0);
    }
    // Printing a huge integer to count its trailing zeros is slow, divide them out first
    let length = u64::try_from(decimal_exponent(&integer, &Natural::ONE)).ok()? + 1;
    if length > MAX_DIGITS {
        let power = natural_power_of_ten(length - MAX_DIGITS);
        if !(&integer).divisible_by(&power) {
            return None;
        }
        integer /= power;
    }
    let integer = integer.to_string();
    let digits = integer.trim_end_matches('0').len();
    u64::try_from(digits)
        .ok()
        .filter(|&digits| digits <= MAX_DIGITS)
}

/// The precision of an approximated value, the number of digits it was computed with, at least
/// [`DEFAULT_DIGITS`].
pub(super) fn precision(x: &Rational) -> u64 {
    significant_digits(x).map_or(DEFAULT_DIGITS, |digits| digits.max(DEFAULT_DIGITS))
}

/// Print an approximated value as a decimal number, in scientific notation if it is very large or very small. Every
/// digit of a decimal number is printed, other numbers are rounded to [`DEFAULT_DIGITS`] digits.
pub fn format_decimal(x: &Rational, typst: bool) -> String {
    if *x == 0 {
        return "0.0".to_owned();
    }
    let digits = significant_digits(x).unwrap_or(DEFAULT_DIGITS).max(1);
    let (mantissa, exponant) = decimal_digits(x, digits);
    let mantissa = mantissa.to_string();
    let mantissa = mantissa.trim_end_matches('0');
    let sign = if *x < 0 { "-" } else { "" };
    if (-5..16).contains(&exponant) {
        #[allow(clippy::option_if_let_else)]
        let (integer, fraction) = if let Ok(exponant) = usize::try_from(exponant) {
            if mantissa.len() <= exponant + 1 {
                let zeros = "0".repeat(exponant + 1 - mantissa.len());
                (format!("{mantissa}{zeros}"), "0".to_owned())
            } else {
                let (integer, fraction) = mantissa.split_at(exponant + 1);
                (integer.to_owned(), fraction.to_owned())
            }
        } else {
            let zeros = "0".repeat(usize::try_from(-exponant - 1).unwrap_or(0));
            ("0".to_owned(), format!("{zeros}{mantissa}"))
        };
        return format!("{sign}{integer}.{fraction}");
    }
    let (first, rest) = mantissa.split_at(1);
    let rest = if rest.is_empty() { "0" } else { rest };
    if typst {
        format!("{sign}{first}.{rest} times 10^({exponant})")
    } else {
        format!("{sign}{first}.{rest}e{exponant}")
    }
}
