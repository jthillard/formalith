//! Fast floating point evaluation of real expressions, used to plot them.
//!
//! A [`Term`] is compiled once into a [`Numeric`] tree, whose symbols are indices in a slice of `f64` values, then
//! evaluated at many points without normalization. The tree is plain data (serializable with the `serde` feature),
//! so it can be evaluated far from the terms it comes from, like in another thread or wasm instance.

use malachite::{
    Rational,
    base::{num::conversion::traits::RoundingFrom, rounding_modes::RoundingMode},
};

use super::expr::Real;
use crate::{
    context::{Context, Symbol},
    term::{Term, relation::Relation},
};

/// A real expression evaluated with `f64`, see [`Numeric::compile`].
#[derive(Clone, Debug, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum Numeric {
    /// A constant.
    Const(f64),
    /// The variable at this index of the values given to [`Numeric::eval`].
    Var(usize),
    /// A sum.
    Add(Vec<Numeric>),
    /// A product.
    Mul(Vec<Numeric>),
    /// A power `base^exponent`.
    Pow(Box<Numeric>, Box<Numeric>),
    /// A rational power `{$x^(p/q)$}`, real for negative `x` when `q` is odd.
    RationalPow(Box<Numeric>, i64, u64),
    /// A function applied to its arguments.
    Fun(NumFn, Vec<Numeric>),
    /// A part which can't be evaluated numerically, like an unevaluated integral, with its name.
    Unsupported(String),
}

/// The functions a [`Numeric`] can apply.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[allow(missing_docs)]
pub enum NumFn {
    Exp,
    Ln,
    Sin,
    Cos,
    Tan,
    Asin,
    Acos,
    Atan,
    Sinh,
    Cosh,
    Tanh,
    Asinh,
    Acosh,
    Atanh,
    Abs,
    Sign,
    Floor,
    Ceil,
    Min,
    Max,
    Erf,
    Erfi,
    Gamma,
    /// `polygamma(m, x)`
    Polygamma,
    Zeta,
    Factorial,
    Binomial,
    LambertW,
    Si,
    Ci,
    Ei,
    /// `piecewise(c1, v1, c2, v2, ..., default)`
    Piecewise,
    /// A comparison of its two arguments, 1 if it holds, 0 otherwise.
    Lt,
    Le,
    Gt,
    Ge,
    Eq,
    Ne,
}

impl NumFn {
    /// The function of a builtin with its number of arguments.
    fn from_builtin(ident: Symbol, arity: usize) -> Option<Self> {
        let fun = match ident {
            Context::EXP => Self::Exp,
            Context::LN => Self::Ln,
            Context::SIN => Self::Sin,
            Context::COS => Self::Cos,
            Context::TAN => Self::Tan,
            Context::ASIN => Self::Asin,
            Context::ACOS => Self::Acos,
            Context::ATAN => Self::Atan,
            Context::SINH => Self::Sinh,
            Context::COSH => Self::Cosh,
            Context::TANH => Self::Tanh,
            Context::ASINH => Self::Asinh,
            Context::ACOSH => Self::Acosh,
            Context::ATANH => Self::Atanh,
            Context::ABS => Self::Abs,
            Context::SIGN => Self::Sign,
            Context::FLOOR => Self::Floor,
            Context::CEIL => Self::Ceil,
            Context::MIN if arity > 0 => return Some(Self::Min),
            Context::MAX if arity > 0 => return Some(Self::Max),
            Context::ERF => Self::Erf,
            Context::ERFI => Self::Erfi,
            Context::GAMMA => Self::Gamma,
            Context::ZETA => Self::Zeta,
            Context::FACTORIAL => Self::Factorial,
            Context::LAMBERTW => Self::LambertW,
            Context::SI => Self::Si,
            Context::CI => Self::Ci,
            Context::EI => Self::Ei,
            Context::POLYGAMMA if arity == 2 => return Some(Self::Polygamma),
            Context::BINOMIAL if arity == 2 => return Some(Self::Binomial),
            Context::PIECEWISE if arity >= 2 => return Some(Self::Piecewise),
            _ => {
                return match Relation::from_symbol(ident)? {
                    _ if arity != 2 => None,
                    Relation::Less => Some(Self::Lt),
                    Relation::LessEqual => Some(Self::Le),
                    Relation::Greater => Some(Self::Gt),
                    Relation::GreaterEqual => Some(Self::Ge),
                    Relation::Equal => Some(Self::Eq),
                    Relation::NotEqual => Some(Self::Ne),
                };
            }
        };
        (arity == 1).then_some(fun)
    }

    /// Apply the function to `args`, `NaN` outside of its domain.
    fn apply(self, args: &[f64]) -> f64 {
        let x = args.first().copied().unwrap_or(f64::NAN);
        let y = args.get(1).copied().unwrap_or(f64::NAN);
        let truth = |holds: bool| {
            if x.is_nan() || y.is_nan() {
                f64::NAN
            } else {
                f64::from(u8::from(holds))
            }
        };
        match self {
            Self::Exp => x.exp(),
            Self::Ln => x.ln(),
            Self::Sin => x.sin(),
            Self::Cos => x.cos(),
            Self::Tan => x.tan(),
            Self::Asin => x.asin(),
            Self::Acos => x.acos(),
            Self::Atan => x.atan(),
            Self::Sinh => x.sinh(),
            Self::Cosh => x.cosh(),
            Self::Tanh => x.tanh(),
            Self::Asinh => x.asinh(),
            Self::Acosh => x.acosh(),
            Self::Atanh => x.atanh(),
            Self::Abs => x.abs(),
            Self::Sign if x == 0. => 0.,
            Self::Sign => x.signum(),
            Self::Floor => x.floor(),
            Self::Ceil => x.ceil(),
            Self::Min => args.iter().copied().fold(f64::INFINITY, f64::min),
            Self::Max => args.iter().copied().fold(f64::NEG_INFINITY, f64::max),
            Self::Erf => libm::erf(x),
            Self::Erfi => erfi(x),
            Self::Gamma => gamma(x),
            Self::Factorial => gamma(x + 1.),
            Self::Polygamma => polygamma(x, y),
            Self::Zeta => zeta(x),
            Self::Binomial => binomial(x, y),
            Self::LambertW => lambert_w(x),
            Self::Si | Self::Ci | Self::Ei => exponential_integral(self, x),
            Self::Piecewise => args
                .chunks(2)
                .find_map(|chunk| match chunk {
                    [condition, value] if *condition == 1. => Some(*value),
                    [condition, _] if condition.is_nan() => Some(f64::NAN),
                    [default] => Some(*default),
                    _ => None,
                })
                .unwrap_or(f64::NAN),
            Self::Lt => truth(x < y),
            Self::Le => truth(x <= y),
            Self::Gt => truth(x > y),
            Self::Ge => truth(x >= y),
            Self::Eq => truth(x == y),
            Self::Ne => truth(x != y),
        }
    }
}

/// Round a rational to the nearest `f64`.
fn to_f64(value: &Rational) -> f64 {
    f64::rounding_from(value, RoundingMode::Nearest).0
}

impl Numeric {
    /// Compile `term`, whose symbols `vars[i]` become [`Numeric::Var`]`(i)`.
    ///
    /// Other symbols and functions without a numerical form become [`Numeric::Unsupported`].
    ///
    /// ```
    /// use formalith::{field::real::{R, numeric::Numeric}, parse, symbol};
    ///
    /// let f = Numeric::compile(&parse!("x^2 + sin(pi*x)", R), &[symbol!("x")]);
    /// assert!((f.eval(&[2.]) - 4.).abs() < 1e-12);
    /// assert!(f.eval(&[f64::NAN]).is_nan());
    /// ```
    #[must_use]
    pub fn compile(term: &Term<Real>, vars: &[Symbol]) -> Self {
        let compile_all =
            |terms: &[Term<Real>]| terms.iter().map(|term| Self::compile(term, vars)).collect();
        match term {
            Term::Value(value) => Self::Const(to_f64(&value.value)),
            Term::Symbol(symbol) => match symbol.symbol {
                Context::PI => Self::Const(std::f64::consts::PI),
                Context::E => Self::Const(std::f64::consts::E),
                Context::EULER_GAMMA => Self::Const(EULER_GAMMA),
                Context::OO => Self::Const(f64::INFINITY),
                Context::UNDEFINED => Self::Const(f64::NAN),
                symbol => vars
                    .iter()
                    .position(|var| *var == symbol)
                    .map_or_else(|| Self::Unsupported(symbol.name().to_owned()), Self::Var),
            },
            Term::Add(add) => Self::Add(compile_all(&add.terms)),
            Term::Mul(mul) => {
                let mut factors: Vec<Self> = compile_all(&mul.factors);
                if mul.coefficient != 1 {
                    factors.insert(0, Self::Const(to_f64(&mul.coefficient)));
                }
                Self::Mul(factors)
            }
            Term::Pow(pow) => {
                let base = Box::new(Self::compile(&pow.base, vars));
                if let Term::Value(exponent) = &**pow.exponant {
                    let (num, den) = exponent.value.numerator_and_denominator_ref();
                    if let (Ok(num), Ok(den)) = (i64::try_from(num), u64::try_from(den)) {
                        let num = if exponent.value < 0 { -num } else { num };
                        return Self::RationalPow(base, num, den);
                    }
                }
                Self::Pow(base, Box::new(Self::compile(&pow.exponant, vars)))
            }
            // The remainder of a series is left out, so that its terms can be drawn
            Term::Fun(fun) if fun.get_ident() == Context::LITTLE_O => Self::Const(0.),
            Term::Fun(fun) => {
                let name = || Self::Unsupported(fun.get_ident_as_str().to_owned());
                let Some(args) = fun.get_args::<Real>() else {
                    return name();
                };
                NumFn::from_builtin(fun.get_ident(), args.len())
                    .map_or_else(name, |numeric| Self::Fun(numeric, compile_all(args)))
            }
        }
    }

    /// The name of the first part which can't be evaluated, like `integrate`.
    #[must_use]
    pub fn unsupported(&self) -> Option<&str> {
        match self {
            Self::Const(_) | Self::Var(_) => None,
            Self::Add(terms) | Self::Mul(terms) | Self::Fun(_, terms) => {
                terms.iter().find_map(Self::unsupported)
            }
            Self::Pow(base, exponent) => base.unsupported().or_else(|| exponent.unsupported()),
            Self::RationalPow(base, ..) => base.unsupported(),
            Self::Unsupported(name) => Some(name),
        }
    }

    /// Evaluate the expression with the values `vars` of its variables, `NaN` where it is undefined.
    #[must_use]
    pub fn eval(&self, vars: &[f64]) -> f64 {
        match self {
            Self::Const(value) => *value,
            Self::Var(i) => vars.get(*i).copied().unwrap_or(f64::NAN),
            Self::Add(terms) => terms.iter().map(|term| term.eval(vars)).sum(),
            Self::Mul(factors) => factors.iter().map(|factor| factor.eval(vars)).product(),
            Self::Pow(base, exponent) => base.eval(vars).powf(exponent.eval(vars)),
            Self::RationalPow(base, num, den) => rational_pow(base.eval(vars), *num, *den),
            Self::Fun(fun, args) => {
                let args: Vec<f64> = args.iter().map(|arg| arg.eval(vars)).collect();
                fun.apply(&args)
            }
            Self::Unsupported(_) => f64::NAN,
        }
    }
}

/// The Euler-Mascheroni constant.
const EULER_GAMMA: f64 = 0.577_215_664_901_532_9;

/// `{$x^(p/q)$}`, the real root for negative `x` and odd `q`.
fn rational_pow(x: f64, num: i64, den: u64) -> f64 {
    if den == 1 {
        return i32::try_from(num).map_or_else(|_| x.powf(num as f64), |n| x.powi(n));
    }
    let exponent = num as f64 / den as f64;
    if x < 0. && den % 2 == 1 {
        let sign = if num % 2 == 0 { 1. } else { -1. };
        sign * (-x).powf(exponent)
    } else {
        x.powf(exponent)
    }
}

/// `{$Gamma(x)$}`, infinite at its poles.
fn gamma(x: f64) -> f64 {
    if x <= 0. && x.fract() == 0. {
        f64::NAN
    } else {
        libm::tgamma(x)
    }
}

/// Bernoulli numbers `{$B_2, B_4, ..., B_14$}`.
const BERNOULLI: [f64; 7] = [
    1. / 6.,
    -1. / 30.,
    1. / 42.,
    -1. / 30.,
    5. / 66.,
    -691. / 2730.,
    7. / 6.,
];

/// `{$psi^((m))(x)$}`, by the recurrence up to `x >= 10` then the asymptotic series.
fn polygamma(m: f64, mut x: f64) -> f64 {
    if m < 0. || m.fract() != 0. || m > 100. || (x <= 0. && x.fract() == 0.) || !x.is_finite() {
        return f64::NAN;
    }
    #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
    let m = m as u32;
    let factorial = |n: u32| (1..=n).map(f64::from).product::<f64>();
    let sign = if m % 2 == 0 { 1. } else { -1. };
    let mut shift = 0.;
    let mut steps = 0;
    while x < 10. {
        // `{$psi^((m))(x) = psi^((m))(x + 1) - (-1)^m m! / x^(m+1)$}`
        shift -= sign * factorial(m) / x.powi(m as i32 + 1);
        x += 1.;
        steps += 1;
        if steps > 100_000 {
            return f64::NAN;
        }
    }
    let mut series = if m == 0 {
        x.ln() - 0.5 / x
    } else {
        factorial(m - 1) / x.powi(m as i32) + factorial(m) / (2. * x.powi(m as i32 + 1))
    };
    for (k, bernoulli) in (1..).zip(BERNOULLI) {
        let term = if m == 0 {
            -bernoulli / (2. * f64::from(k) * x.powi(2 * k))
        } else {
            bernoulli * factorial(2 * k as u32 + m - 1)
                / (factorial(2 * k as u32) * x.powi(2 * k + m as i32))
        };
        series += term;
    }
    if m > 0 && m % 2 == 0 {
        series = -series;
    }
    series + shift
}

/// `{$zeta(s)$}`, by Euler-Maclaurin summation for `s >= 1/2` and the functional equation otherwise.
fn zeta(s: f64) -> f64 {
    if s == 1. || s.is_nan() {
        return f64::NAN;
    }
    if s == 0. {
        // The functional equation would need `zeta(1)`
        return -0.5;
    }
    if s < 0.5 {
        if s < 0. && (s / 2.).fract() == 0. {
            return 0.;
        }
        // `{$zeta(s) = 2^s pi^(s-1) sin(pi s / 2) Gamma(1 - s) zeta(1 - s)$}`
        let pi = std::f64::consts::PI;
        return 2f64.powf(s)
            * pi.powf(s - 1.)
            * (pi * s / 2.).sin()
            * libm::tgamma(1. - s)
            * zeta(1. - s);
    }
    let n: f64 = 12.;
    let mut sum: f64 = (1..12).map(|k| f64::from(k).powf(-s)).sum();
    sum += n.powf(1. - s) / (s - 1.) + 0.5 * n.powf(-s);
    // `{$sum_k B_(2k) / (2k)! s (s+1) ... (s+2k-2) N^(-s-2k+1)$}`
    let mut rising = s;
    let mut factorial = 2.;
    for (k, bernoulli) in (1..).zip(BERNOULLI) {
        sum += bernoulli / factorial * rising * n.powf(-s - f64::from(2 * k) + 1.);
        let k = f64::from(k);
        rising *= (s + 2. * k - 1.) * (s + 2. * k);
        factorial *= (2. * k + 1.) * (2. * k + 2.);
    }
    sum
}

/// `{$binom(n, k)$}`, exact on integers.
fn binomial(n: f64, k: f64) -> f64 {
    if k.fract() == 0. && n.fract() == 0. && (0. ..=1000.).contains(&k) {
        if k > n && n >= 0. {
            return 0.;
        }
        let mut res = 1.;
        let mut i = 0.;
        while i < k {
            res *= (n - i) / (i + 1.);
            i += 1.;
        }
        return res.round();
    }
    gamma(n + 1.) / (gamma(k + 1.) * gamma(n - k + 1.))
}

/// The imaginary error function `{$"erfi"(x) = -i "erf"(i x)$}`.
fn erfi(x: f64) -> f64 {
    let sqrt_pi = std::f64::consts::PI.sqrt();
    if x.abs() < 5. {
        // `{$2/sqrt(pi) sum x^(2n+1) / (n! (2n+1))$}`
        let mut term = x;
        let mut sum = x;
        let mut n = 0.;
        while term.abs() > 1e-17 * sum.abs() {
            n += 1.;
            term *= x * x / n;
            sum += term / (2. * n + 1.);
        }
        2. / sqrt_pi * sum
    } else {
        // `{$e^(x^2) / (x sqrt(pi)) (1 + 1/(2x^2) + 3/(4x^4) + ...)$}`
        let inv = 1. / (2. * x * x);
        let mut term = 1.;
        let mut sum = 1.;
        for n in 1..20 {
            term *= f64::from(2 * n - 1) * inv;
            sum += term;
        }
        (x * x).exp() / (x * sqrt_pi) * sum
    }
}

/// `{$"Si"(x)$}`, `{$"Ci"(x)$}` or `{$"Ei"(x)$}`, by their power series for small `|x|` (whose terms cancel up to
/// `{$e^|x|$}`), by continued fractions of `{$E_1$}` for `{$"Si"$}`, `{$"Ci"$}` and `{$"Ei"$}` of negative
/// arguments otherwise, and by the asymptotic series for `{$"Ei"$}` of large positive arguments. `NaN` for
/// `{$"Ci"(x)$}` with `{$x <= 0$}`.
fn exponential_integral(fun: NumFn, x: f64) -> f64 {
    /// Below this bound, the power series loses at most 2 digits; above it, the continued fractions converge fast.
    const SERIES_BOUND: f64 = 4.;
    if x.is_nan() || (fun == NumFn::Ci && x <= 0.) {
        return f64::NAN;
    }
    if fun == NumFn::Si && x < 0. {
        return -exponential_integral(fun, -x);
    }
    if x == 0. {
        return if fun == NumFn::Si {
            0.
        } else {
            f64::NEG_INFINITY
        };
    }
    if x.is_infinite() {
        return match fun {
            NumFn::Si => std::f64::consts::FRAC_PI_2,
            NumFn::Ei if x > 0. => x,
            _ => 0.,
        };
    }
    // `{$"Ei"$}` has no cancellation for positive `x`, and `{$"Ei"(x) = -E_1(-x)$}` converges fast from 1
    let bound = match fun {
        NumFn::Ei if x > 0. => 40.,
        NumFn::Ei => 1.,
        _ => SERIES_BOUND,
    };
    if x.abs() < bound {
        let mut sum = 0.;
        let mut power = 1.;
        for k in 1..500 {
            let k = f64::from(k);
            let term = match fun {
                // `{$x^(2k-1) / ((2k-1) (2k-1)!)$}` with alternating signs
                NumFn::Si => {
                    power *= x / (2. * k - 1.);
                    let term = power / (2. * k - 1.);
                    power *= x / (2. * k);
                    if k % 2. == 0. { -term } else { term }
                }
                // `{$(-1)^k x^(2k) / (2k (2k)!)$}`
                NumFn::Ci => {
                    power *= -x * x / ((2. * k - 1.) * (2. * k));
                    power / (2. * k)
                }
                // `{$x^k / (k k!)$}`
                _ => {
                    power *= x / k;
                    power / k
                }
            };
            sum += term;
            if term.abs() <= 1e-17 * sum.abs() {
                break;
            }
        }
        return if fun == NumFn::Si {
            sum
        } else {
            sum + EULER_GAMMA + x.abs().ln()
        };
    }
    match fun {
        NumFn::Si | NumFn::Ci => {
            // `{$E_1(i x) = -"Ci"(x) + i ("Si"(x) - pi/2)$}`
            let (re, im) = e1_imaginary(x);
            return if fun == NumFn::Si {
                std::f64::consts::FRAC_PI_2 + im
            } else {
                -re
            };
        }
        _ if x < 0. => return -e1(-x),
        _ => {}
    }
    // `{$"Ei"(x) ~ e^x sum (k - 1)! / x^k$}`, while the terms decrease
    let mut ei = 0.;
    let mut term = 1. / x;
    for k in 1..200 {
        ei += term;
        let next = term * f64::from(k) / x;
        if next.abs() >= term.abs() {
            break;
        }
        term = next;
    }
    x.exp() * ei
}

/// `{$E_1(x) = integral_x^oo e^(-t) / t dif t$}` for `{$x >= 1$}`, by its continued fraction (modified Lentz's
/// method).
fn e1(x: f64) -> f64 {
    let tiny = 1e-300;
    let mut b = x + 1.;
    let mut c = 1. / tiny;
    let mut d = 1. / b;
    let mut h = d;
    for i in 1..200 {
        let a = -f64::from(i) * f64::from(i);
        b += 2.;
        d = 1. / (a * d + b);
        c = b + a / c;
        let delta = c * d;
        h *= delta;
        if (delta - 1.).abs() < 1e-16 {
            break;
        }
    }
    h * (-x).exp()
}

/// `{$E_1(i x)$}` for `{$x >= 2$}` as its real and imaginary parts, by its continued fraction (modified Lentz's
/// method, as `cisi` in Numerical Recipes).
fn e1_imaginary(x: f64) -> (f64, f64) {
    let mul = |(a, b): (f64, f64), (c, d): (f64, f64)| (a * c - b * d, a * d + b * c);
    let inv = |(a, b): (f64, f64)| {
        let n = a * a + b * b;
        (a / n, -b / n)
    };
    let tiny = 1e-300;
    let mut b = (1., x);
    let mut c = (1. / tiny, 0.);
    let mut d = inv(b);
    let mut h = d;
    for i in 2..200 {
        let a = -f64::from(i - 1) * f64::from(i - 1);
        b.0 += 2.;
        d = inv((a * d.0 + b.0, a * d.1 + b.1));
        let a_over_c = mul((a, 0.), inv(c));
        c = (b.0 + a_over_c.0, b.1 + a_over_c.1);
        let delta = mul(c, d);
        h = mul(h, delta);
        if (delta.0 - 1.).abs() + delta.1.abs() < 1e-16 {
            break;
        }
    }
    mul((x.cos(), -x.sin()), h)
}

/// The principal branch `{$W_0(x)$}` of the Lambert W function, by Halley's iteration.
fn lambert_w(x: f64) -> f64 {
    let branch = -1. / std::f64::consts::E;
    if x.is_nan() || x < branch {
        return f64::NAN;
    }
    if x == f64::INFINITY {
        return x;
    }
    let mut w = if x < 1. {
        let p = (2. * (std::f64::consts::E * x + 1.)).max(0.).sqrt();
        -1. + p - p * p / 3.
    } else {
        let l = x.ln_1p();
        l - (l.max(1.)).ln() * 0.5
    };
    for _ in 0..50 {
        let e = w.exp();
        let f = w * e - x;
        let denominator = e * (w + 1.) - (w + 2.) * f / (2. * w + 2.);
        if denominator == 0. || !denominator.is_finite() {
            break;
        }
        let next = w - f / denominator;
        if (next - w).abs() <= 1e-15 * (1. + next.abs()) {
            return next;
        }
        w = next;
    }
    w
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{field::real::R, parse, symbol};

    fn eval(input: &str, x: f64) -> f64 {
        Numeric::compile(&parse!(input, R), &[symbol!("x")]).eval(&[x])
    }

    fn assert_close(a: f64, b: f64) {
        assert!((a - b).abs() <= 1e-9 * (1. + b.abs()), "{a} != {b}");
    }

    #[test]
    fn test_elementary() {
        assert_close(eval("sin(x)^2 + cos(x)^2", 0.7), 1.);
        assert_close(eval("exp(x) * ln(x) / x", 2.), 2f64.exp() * 2f64.ln() / 2.);
        assert_close(
            eval("atan(x) + asinh(x)", 0.5),
            0.5f64.atan() + 0.5f64.asinh(),
        );
        assert!(eval("sqrt(x)", -1.).is_nan());
        assert_close(eval("x^(1/3)", -8.), -2.);
        assert_close(eval("x^(2/3)", -8.), 4.);
        assert_close(eval("abs(x) + floor(x)", -1.5), -0.5);
    }

    #[test]
    fn test_special() {
        assert_close(eval("gamma(x)", 5.), 24.);
        assert_close(eval("factorial(x)", 0.5), std::f64::consts::PI.sqrt() / 2.);
        assert_close(eval("binomial(x, 2)", 5.), 10.);
        assert_close(eval("polygamma(0, x)", 1.), -EULER_GAMMA);
        assert_close(
            eval("polygamma(1, x)", 1.),
            std::f64::consts::PI.powi(2) / 6.,
        );
        assert_close(eval("polygamma(2, x)", 1.), -2.404_113_806_319_188_5);
        assert_close(eval("zeta(x)", 3.), 1.202_056_903_159_594_3);
        assert_close(eval("zeta(x)", -1.), -1. / 12.);
        assert_close(eval("zeta(x)", 0.), -0.5);
        assert_close(eval("zeta(x)", 0.5), -1.460_354_508_809_586_8);
        assert_close(eval("lambertw(x)", 1.), 0.567_143_290_409_783_8);
        assert_close(eval("lambertw(x)", -0.2), -0.259_171_101_819_073_7);
        assert_close(eval("lambertw(x)", 100.), 3.385_630_140_290_050_4);
        assert_close(eval("erf(x)", 1.), 0.842_700_792_949_714_9);
        assert_close(eval("erfi(x)", 1.), 1.650_425_758_797_542_9);
        assert_close(eval("erfi(x)", 6.), 4.112_751_455_828_239e14);
        assert_close(eval("erfi(x)", 4.9), 3_149_283_850.004_450_8);
    }

    #[test]
    fn test_exponential_integrals() {
        // Reference values, on both sides of the bound between the power and asymptotic series
        let close = |a: f64, b: f64| assert!((a - b).abs() <= 1e-7 * (1. + b.abs()), "{a} != {b}");
        close(eval("Si(x)", 1.), 0.946_083_070_367_183);
        close(eval("Si(x)", -2.), -1.605_412_976_802_695);
        close(eval("Si(x)", 15.), 1.618_194_443_708_369);
        close(eval("Si(x)", 100.), 1.562_225_466_889_056);
        close(eval("Ci(x)", 1.), 0.337_403_922_900_968);
        close(eval("Ci(x)", 20.), 0.044_419_820_845_353);
        close(eval("Ci(x)", 100.), -0.005_148_825_142_610);
        close(eval("Ei(x)", 1.), 1.895_117_816_355_937);
        close(eval("Ei(x)", -1.), -0.219_383_934_395_520);
        close(eval("Ei(x)", 50.), 1.058_563_689_713_169e20);
        close(
            eval("Ei(x)", -20.) * 1e10,
            -9.835_525_290_649_882e-11 * 1e10,
        );
        assert!(eval("Ci(x)", -1.).is_nan());
    }

    #[test]
    fn test_exponential_integrals_to_full_precision() {
        // On both sides of the switch from the power series to the continued fractions
        let precise = |a: f64, b: f64| {
            assert!((a - b).abs() <= 1e-13 * b.abs(), "{a} != {b}");
        };
        for (x, si, ci) in [
            (0.5, 0.493_107_418_043_067, -0.177_784_078_806_613),
            (3.9, 1.776_501_360_447_81, -0.123_499_349_207_815),
            (4.1, 1.738_743_626_491_77, -0.156_165_391_828_121),
            (10., 1.658_347_594_218_87, -0.045_456_433_004_455_4),
            (16.67, 1.607_755_678_174_73, -0.046_855_141_548_840_4),
            (30., 1.566_756_540_030_35, -0.033_032_417_282_071_1),
        ] {
            precise(eval("Si(x)", x), si);
            precise(eval("Ci(x)", x), ci);
        }
        for (x, ei) in [
            (-0.5, -0.559_773_594_776_161),
            (-1.5, -0.100_019_582_406_633),
            (-5., -0.001_148_295_591_275_33),
            (-30., -3.021_552_010_688_81e-15),
        ] {
            precise(eval("Ei(x)", x), ei);
        }
    }

    #[test]
    fn test_piecewise() {
        let input = "piecewise(x < 0, -x, x < 1, x^2, 1)";
        assert_close(eval(input, -2.), 2.);
        assert_close(eval(input, 0.5), 0.25);
        assert_close(eval(input, 3.), 1.);
    }

    #[test]
    fn test_unsupported() {
        let f = Numeric::compile(&parse!("integrate(exp(x^3), x)", R), &[symbol!("x")]);
        assert_eq!(f.unsupported(), Some("integrate"));
        assert!(f.eval(&[1.]).is_nan());
        let f = Numeric::compile(&parse!("a*x", R), &[symbol!("x")]);
        assert_eq!(f.unsupported(), Some("a"));
        let f = Numeric::compile(&parse!("a*x", R), &[symbol!("x"), symbol!("a")]);
        assert_close(f.eval(&[2., 3.]), 6.);
    }
}
