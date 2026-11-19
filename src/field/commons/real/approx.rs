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
                Abs, Ceiling, DivRound, DivisibleBy, Factorial, Floor, FloorLogBase2, FloorRoot,
                Pow, Reciprocal, UnsignedAbs,
            },
            basic::traits::{One, Zero},
            conversion::traits::RoundingFrom,
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

/// Minimum number of halvings of the step of the numerical integration.
const MIN_QUADRATURE_LEVELS: u64 = 3;
/// Maximum number of halvings of the step of the numerical integration.
const MAX_QUADRATURE_LEVELS: u64 = 10;
/// Bound of the parameter `s` of the nodes of the numerical integration.
const MAX_QUADRATURE_S: u64 = 6;

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

    /// The shift `N` such that the asymptotic series of the Gamma family at `{$y = x + N >= Y$}` reach the precision,
    /// their smallest term being about `{$e^(-2 pi Y)$}`, and the product `{$x (x + 1) ... (x + N - 1)$}`.
    /// `None` at the poles, non-positive integers.
    fn gamma_shift(self, x: &Rational, extra: u64) -> Option<(u64, Rational)> {
        if *x <= 0 && *x.denominator_ref() == 1 {
            return None;
        }
        let target = Rational::from(self.bits / 8 + 16 + extra);
        let n = if *x >= target {
            0
        } else {
            u64::try_from(&(&target - x).ceiling()).ok()?
        };
        let product = (0..n).fold(Rational::ONE, |product, k| {
            product * (x + Rational::from(k))
        });
        Some((n, product))
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
        let (n, _) = self.gamma_shift(x, extra)?;
        let mut sum = Rational::ZERO;
        for k in 0..n {
            sum += self.pow(&(x + Rational::from(k)), &-s)?;
        }
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
        let (n, _) = self.gamma_shift(x, 0)?;
        let shift = (0..n).fold(Rational::ZERO, |sum, k| {
            sum + (x + Rational::from(k)).reciprocal()
        });
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
            && n >= 1
            && n <= MAX_EXPONENT
        {
            return Some(Rational::from(Natural::factorial(n - 1)));
        }
        let (n, product) = self.gamma_shift(x, 0)?;
        let y = x + Rational::from(n);
        let half = Rational::from_signeds(1, 2);
        let two_pi = Rational::from(self.pi() << 1_u64) >> self.bits;
        let ln_y = self.ln(&y);
        let main = self.from_rational(&(&y - &half)) * &ln_y >> self.bits;
        let series = self.asymptotic_sum(&y, &y, |k, b| b / Rational::from(2 * k * (2 * k - 1)));
        let ln_gamma = main - self.from_rational(&y) + (self.ln(&two_pi) >> 1_u64) + series;
        Some(self.to_rational(self.exp(&ln_gamma)?) / product)
    }

    /// `{$W_0(x)$}` for `{$x >= -1/e$}`, by Newton's iteration on `{$w e^w = x$}` from a float approximation.
    fn lambert_w(self, x: &Rational) -> Option<Rational> {
        if *x == 0 {
            return Some(Rational::ZERO);
        }
        // `{$e x + 1 >= 0$}`
        let branch = self.exp_rational(&Rational::ONE)? * x + Rational::ONE;
        if branch < 0 {
            return None;
        }
        let float = |x: &Rational| f64::rounding_from(x, RoundingMode::Nearest).0;
        let x_float = float(x);
        let guess = if x_float < 1. {
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
        for _ in 0..self.bits + 64 {
            let exp = self.exp(&w)?;
            let derivative = self.mul(&exp, &(&w + &one));
            if derivative == 0 {
                break;
            }
            let step = self.div(&(self.mul(&w, &exp) - &target), &derivative);
            w -= &step;
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
        let bound = |t: &Term<Real>| self.evaluate(t);
        let kind = match (a_infinity, b_infinity) {
            (None, None) => Quadrature::Finite(bound(a)?, bound(b)?),
            (None, Some(_)) => Quadrature::Right(bound(a)?),
            (Some(_), None) => Quadrature::Left(bound(b)?),
            (Some(_), Some(_)) => Quadrature::Whole,
        };
        let eval =
            |node: Rational| self.evaluate(&bind(f, x, &Term::Value(Value::new(node, super::R))));
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

    /// Evaluate a term without symbols, other than builtin constants.
    fn evaluate(self, term: &Term<Real>) -> Option<Rational> {
        match term {
            Term::Value(value) => Some(value.value.clone()),
            Term::Symbol(symbol) => match symbol.symbol {
                Context::PI => Some(self.to_rational(self.pi())),
                Context::E => Some(self.to_rational(self.exp(&self.one())?)),
                // `{$gamma = -psi(1)$}`
                Context::EULER_GAMMA => Some(-self.digamma(&Rational::ONE)?),
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
                    (Context::LAMBERTW, [x]) => self.lambert_w(&self.evaluate(x)?),
                    (Context::GAMMA, [x]) => self.gamma(&self.evaluate(x)?),
                    (Context::FACTORIAL, [x]) => self.gamma(&(self.evaluate(x)? + Rational::ONE)),
                    (Context::BINOMIAL, [n, k]) => {
                        let (n, k) = (self.evaluate(n)?, self.evaluate(k)?);
                        if let (Ok(n), Ok(k)) = (Integer::try_from(&n), Integer::try_from(&k)) {
                            // Exact, also when `{$Gamma$}` has poles
                            let args = vec![
                                Term::Value(Value::new(Rational::from(n), fun.get_set())),
                                Term::Value(Value::new(Rational::from(k), fun.get_set())),
                            ];
                            return match Term::Fun(Box::new(Fun::new(
                                Context::BINOMIAL,
                                args,
                                fun.get_set(),
                            )))
                            .normalize()
                            {
                                Term::Value(value) => Some(value.value),
                                _ => None,
                            };
                        }
                        // `{$binom(n, k) = Gamma(n + 1) / (Gamma(k + 1) Gamma(n - k + 1))$}`
                        let one = Rational::ONE;
                        Some(
                            self.gamma(&(&n + &one))?
                                / (self.gamma(&(&k + &one))? * self.gamma(&(n - k + one))?),
                        )
                    }
                    (Context::POLYGAMMA, [m, x]) => {
                        let m = u64::try_from(&self.evaluate(m)?).ok()?;
                        self.polygamma(m, &self.evaluate(x)?)
                    }
                    (Context::ZETA, [s]) => {
                        let s = self.evaluate(s)?;
                        if *s.denominator_ref() == 1 && s <= 0 {
                            // Exact values from the Bernoulli numbers
                            let set = fun.get_set();
                            let arg = vec![Term::Value(Value::new(s, set))];
                            return match Term::Fun(Box::new(Fun::new(Context::ZETA, arg, set)))
                                .normalize()
                            {
                                Term::Value(value) => Some(value.value),
                                _ => None,
                            };
                        }
                        self.hurwitz_zeta(&s, &Rational::ONE)
                    }
                    (Context::INTEGRATE, [f, Term::Symbol(x), a, b]) => {
                        self.integrate(f, x.symbol, a, b)
                    }
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
                        | Context::ERFI),
                        [x],
                    ) => self.eval_elementary(ident, &self.evaluate(x)?),
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
        Term::Fun(fun) => match fun.get_args::<Real>() {
            Some(args) => Term::Fun(Box::new(Fun::new(
                fun.get_ident(),
                args.iter().map(|t| bind(t, x, value)).collect(),
                set,
            ))),
            None => term.clone(),
        },
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
