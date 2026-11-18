//! Numerical approximation of real expressions, used by `approx`.
//!
//! Expressions are evaluated with fixed-point arithmetic on integers, an integer `m` standing for `{$m / 2^b$}`,
//! then rounded to a number of significant decimal digits. The working precision is increased until the result
//! has enough significant bits, which isn't a guarantee: the last digits can be wrong after a cancellation.

use malachite::{
    Integer, Natural, Rational,
    base::{
        num::{
            arithmetic::traits::{
                Abs, DivRound, DivisibleBy, Floor, FloorLogBase2, FloorRoot, Pow, UnsignedAbs,
            },
            basic::traits::{One, Zero},
        },
        rounding_modes::RoundingMode,
    },
};

use crate::{
    context::Context,
    term::{Add, Fun, Mul, Normalize, Term, Value, flags::Flags},
};

use super::R;

type Real = R<Rational>;

/// Default number of significant digits of `approx`.
pub(super) const DEFAULT_DIGITS: u64 = 15;
/// Maximum number of significant digits of `approx`.
pub(super) const MAX_DIGITS: u64 = 10_000;
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

/// Fixed-point arithmetic, an integer `m` standing for `{$m / 2^"bits"$}`.
#[derive(Clone, Copy)]
struct Fixed {
    bits: u64,
}

impl Fixed {
    fn one(self) -> Integer {
        Integer::ONE << self.bits
    }
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
        self.arctan_inverse(5, false) * Integer::from(16)
            - self.arctan_inverse(239, false) * Integer::from(4)
    }

    /// `{$ln(2) = 2 "arctanh"(1/3)$}`.
    fn ln2(self) -> Integer {
        self.arctan_inverse(3, true) << 1_u64
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

    /// `{$(sin(x), cos(x))$}`, reducing `x` modulo `{$2 pi$}` and using the double-angle formulas.
    fn sin_cos(self, x: &Integer) -> (Integer, Integer) {
        let two_pi = self.pi() << 1_u64;
        let n = x.div_round(&two_pi, RoundingMode::Nearest).0;
        let r = (x - n * two_pi) >> HALVINGS;
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
        (sin, cos)
    }

    /// `{$root(n, x)$}`, `x` being negative only for odd `n`.
    fn root(self, x: &Rational, n: u64) -> Option<Rational> {
        if *x < 0 && n % 2 == 0 {
            return None;
        }
        let shifted: Integer = (x.abs() << (n * self.bits)).floor();
        let root = Integer::from(shifted.unsigned_abs().floor_root(n));
        let root = self.to_rational(root);
        Some(if *x < 0 { -root } else { root })
    }

    /// `{$e^x$}` for a rational `x`.
    fn exp_rational(self, x: &Rational) -> Option<Rational> {
        if x.abs() > MAX_EXP_ARGUMENT {
            return None;
        }
        Some(self.to_rational(self.exp(&self.from_rational(x))?))
    }

    /// `{$b^e$}`, exact for integer exponents.
    fn pow(self, base: &Rational, exponant: &Rational) -> Option<Rational> {
        if *base == 0 {
            return (*exponant > 0).then_some(Rational::ZERO);
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

    /// Evaluate a term without symbols, other than builtin constants.
    fn evaluate(self, term: &Term<Real>) -> Option<Rational> {
        match term {
            Term::Value(value) => Some(value.value.clone()),
            Term::Symbol(symbol) => match symbol.symbol {
                Context::PI => Some(self.to_rational(self.pi())),
                Context::E => Some(self.to_rational(self.exp(&self.one())?)),
                _ => None,
            },
            Term::Add(add) => add
                .iter()
                .try_fold(Rational::ZERO, |sum, term| Some(sum + self.evaluate(term)?)),
            Term::Mul(mul) => mul
                .iter()
                .try_fold(mul.coefficient.clone(), |product, factor| {
                    Some(product * self.evaluate(factor)?)
                }),
            Term::Pow(pow) => self.pow(&self.evaluate(&pow.base)?, &self.evaluate(&pow.exponant)?),
            Term::Fun(fun) => {
                let args = fun.get_args::<Real>()?;
                match (fun.get_ident(), args.as_slice()) {
                    (Context::EXP, [x]) => self.exp_rational(&self.evaluate(x)?),
                    (Context::LN, [x]) => {
                        let x = self.evaluate(x)?;
                        (x > 0).then(|| self.to_rational(self.ln(&x)))
                    }
                    (ident @ (Context::SIN | Context::COS | Context::TAN), [x]) => {
                        let (sin, cos) = self.sin_cos(&self.from_rational(&self.evaluate(x)?));
                        match ident {
                            Context::SIN => Some(self.to_rational(sin)),
                            Context::COS => Some(self.to_rational(cos)),
                            _ => (cos != 0).then(|| self.to_rational(self.div(&sin, &cos))),
                        }
                    }
                    (ident, args) => {
                        // Other builtins, like `abs` or `floor`, are evaluated on approximated arguments
                        let set = fun.get_set();
                        let args = args
                            .iter()
                            .map(|arg| Some(Term::Value(Value::new(self.evaluate(arg)?, set))))
                            .collect::<Option<_>>()?;
                        match Term::Fun(Box::new(Fun::new(ident, args, set))).normalize() {
                            Term::Value(value) => Some(value.value),
                            _ => None,
                        }
                    }
                }
            }
        }
    }
}

/// Number of bits needed to get `digits` significant decimal digits.
fn bits_for_digits(digits: u64) -> u64 {
    // `{$log_2(10) < 3.3220$}`
    digits * 33_220 / 10_000 + 1
}

/// Approximate a term without symbols, other than builtin constants, to `digits` significant digits. Return `None`
/// if the term contains symbols or can't be evaluated, like `{$ln(-1)$}`.
pub(crate) fn approximate(term: &Term<Real>, digits: u64) -> Option<Rational> {
    let needed = bits_for_digits(digits) + GUARD_BITS / 2;
    let max_bits = 4 * needed + 4096;
    let mut bits = needed + GUARD_BITS;
    loop {
        let value = Fixed { bits }.evaluate(term)?;
        if value == 0 {
            return Some(value);
        }
        // The evaluation is accurate to about `{$2^(-"bits")$}`, check the number of significant bits
        let significant = i64::try_from(bits).ok()? + (&(&value).abs()).floor_log_base_2();
        if significant >= i64::try_from(needed).ok()? {
            return Some(round_significant(&value, digits));
        }
        if bits >= max_bits {
            // Indistinguishable from zero at the maximum precision, like `{$sin(pi)$}`
            return Some(Rational::ZERO);
        }
        let missing = u64::try_from(i64::try_from(needed).ok()? - significant).ok()?;
        bits = (bits + missing + GUARD_BITS).min(max_bits);
    }
}

/// Approximate a term like [`approximate`], but in a single evaluation with an absolute error of about
/// `{$2^(-"bits")$}`, which is faster when the value may be zero.
pub(crate) fn approximate_fixed(term: &Term<Real>, bits: u64) -> Option<Rational> {
    Fixed {
        bits: bits + GUARD_BITS,
    }
    .evaluate(term)
}

/// An approximated value, printed as a decimal number.
pub(super) fn approximate_value(value: Rational) -> Term<Real> {
    let mut res = Term::Value(Value::new(value, super::R));
    res.set_approximate(true);
    res
}

/// Approximate the numerical parts of `term` to `digits` significant digits, keeping symbols, like
/// `{$x + 1.41421356237310$}` for `{$x + sqrt(2)$}`. Integer exponents are kept exact.
pub(super) fn approximate_term(term: &Term<Real>, digits: u64) -> Term<Real> {
    if let Some(value) = approximate(term, digits) {
        return approximate_value(value);
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
                round_significant(&mul.coefficient, digits),
                mul.iter()
                    .map(|factor| approximate_term(factor, digits))
                    .collect(),
                set,
            );
            res.set_approximate(true);
            Term::Mul(res).normalize()
        }
        Term::Pow(pow) => {
            let exponant: &Term<Real> = &pow.exponant;
            let exponant = match exponant {
                Term::Value(value) if *value.value.denominator_ref() == 1 => exponant.clone(),
                _ => approximate_term(exponant, digits),
            };
            approximate_term(&pow.base, digits).pow(&exponant)
        }
        Term::Fun(fun) => fun.get_args::<Real>().map_or_else(
            || term.clone(),
            |args| {
                let args = args
                    .iter()
                    .map(|arg| approximate_term(arg, digits))
                    .collect();
                Term::Fun(Box::new(Fun::new(fun.get_ident(), args, set))).normalize()
            },
        ),
    }
}

fn power_of_ten(exponant: i64) -> Rational {
    Pow::pow(Rational::from(10), exponant)
}

/// Round `|x|` to `digits` significant digits, returning the digits as an integer `m` and the exponent `e` of the
/// first digit: `{$|x| approx m 10^(e - "digits" + 1)$}`. `x` must be non-zero.
fn decimal_digits(x: &Rational, digits: u64) -> (Natural, i64) {
    let x = x.abs();
    // `{$log_10(2) approx 0.30103$}`, then fix the estimate
    let mut exponant = x.floor_log_base_2() * 30_103 / 100_000;
    while power_of_ten(exponant) > x {
        exponant -= 1;
    }
    while power_of_ten(exponant + 1) <= x {
        exponant += 1;
    }
    let digits = i64::try_from(digits).unwrap_or(i64::MAX);
    let scaled = x * power_of_ten(digits - 1 - exponant) + Rational::from_signeds(1, 2);
    let mut mantissa = scaled.floor().unsigned_abs();
    if mantissa == Natural::from(10_u32).pow(u64::try_from(digits).unwrap_or(0)) {
        // Rounded up to the next power of ten, like `{$9.99 approx 10.0$}`
        mantissa /= Natural::from(10_u32);
        exponant += 1;
    }
    (mantissa, exponant)
}

/// Round `x` to `digits` significant digits.
pub(super) fn round_significant(x: &Rational, digits: u64) -> Rational {
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
    let integer = (x.abs() * power_of_ten(i64::try_from(twos.max(fives)).ok()?)).floor();
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
pub(super) fn format_decimal(x: &Rational, typst: bool) -> String {
    if *x == 0 {
        return "0.0".to_owned();
    }
    let digits = significant_digits(x).unwrap_or(DEFAULT_DIGITS).max(1);
    let (mantissa, exponant) = decimal_digits(x, digits);
    let mantissa = mantissa.to_string();
    let mantissa = mantissa.trim_end_matches('0');
    let sign = if *x < 0 { "-" } else { "" };
    if (-5..16).contains(&exponant) {
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
