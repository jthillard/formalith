//! The Gamma function family: exact values of `gamma`, `beta`, `digamma`, `polygamma` and `zeta`, and the
//! Bernoulli numbers they need.

use std::sync::RwLock;

use malachite::{
    Natural, Rational,
    base::num::{
        arithmetic::traits::{Abs, BinomialCoefficient, Factorial, Pow},
        basic::traits::{One, Zero},
    },
};

use super::R;
use crate::{
    context::{Context, Symbol},
    term::{Fun, Normalize, SymbolTerm, Term},
};

/// Largest `n` for which harmonic sums `{$H_n^((s))$}` are evaluated exactly.
const MAX_HARMONIC: u64 = 10_000;
/// Largest order `m` of `{$psi^((m))$}` and argument `s` of `{$zeta(s)$}` evaluated exactly.
const MAX_ORDER: u64 = 1000;

/// The Bernoulli numbers computed so far, `{$B_0, B_1, ...$}`.
static BERNOULLI: RwLock<Vec<Rational>> = RwLock::new(Vec::new());

/// The Bernoulli number `{$B_n$}`, with `{$B_1 = -1/2$}`.
pub(crate) fn bernoulli(n: usize) -> Rational {
    if let Some(b) = BERNOULLI.read().expect("Bernoulli numbers lock").get(n) {
        return b.clone();
    }
    let mut numbers = BERNOULLI.write().expect("Bernoulli numbers lock");
    // `{$B_m = -1/(m + 1) sum_(k < m) binom(m + 1, k) B_k$}`
    while numbers.len() <= n {
        let m = numbers.len() as u64;
        let b = if m == 0 {
            Rational::ONE
        } else if m > 1 && m % 2 == 1 {
            Rational::ZERO
        } else {
            let sum = numbers
                .iter()
                .enumerate()
                .fold(Rational::ZERO, |sum, (k, b)| {
                    if *b == 0 {
                        return sum;
                    }
                    let binomial = Natural::binomial_coefficient(
                        Natural::from(m + 1),
                        Natural::from(k as u64),
                    );
                    sum + Rational::from(binomial) * b
                });
            -sum / Rational::from(m + 1)
        };
        numbers.push(b);
    }
    numbers[n].clone()
}

/// The generalized harmonic number `{$H_n^((s)) = sum_(k = 1)^n 1/k^s$}`.
fn harmonic(n: u64, s: u64) -> Rational {
    (1..=n).fold(Rational::ZERO, |sum, k| {
        sum + Rational::from(k).pow(s).pow(-1_i64)
    })
}

/// `{$(-1)^(m + 1) m!$}`, the factor of `{$zeta(m + 1)$}` in `{$psi^((m))(1)$}`.
fn polygamma_factor(m: u64) -> Rational {
    let factorial = Rational::from(Natural::factorial(m));
    if m % 2 == 0 { -factorial } else { factorial }
}

impl R<Rational> {
    /// Evaluate the functions of the Gamma family, `None` when nothing applies:
    /// - `{$Gamma(q) = (q - 1)!$}` for integers and half-integers,
    /// - `{$B(a, b) = (Gamma(a) Gamma(b)) / Gamma(a + b)$}` and `{$psi(u) = "polygamma"(0, u)$}`, always rewritten,
    /// - `{$psi^((m))(q)$}` for integers and half-integers, with `{$gamma$}`, `{$ln 2$}` and `{$zeta(m + 1)$}`,
    /// - `{$zeta(n)$}` for integers `n` except odd `{$n >= 3$}`, from the Bernoulli numbers.
    pub(super) fn eval_gamma_family(
        self,
        ident: Symbol,
        args: &[Term<Self>],
    ) -> Option<Term<Self>> {
        match (ident, args) {
            (Context::GAMMA, [Term::Value(q)]) => self.eval_factorial(&(&q.value - Rational::ONE)),
            (Context::BETA, [a, b]) => Some(
                self.call(Context::GAMMA, vec![a.clone()])
                    * self.call(Context::GAMMA, vec![b.clone()])
                    / self.call(Context::GAMMA, vec![a + b]),
            ),
            (Context::DIGAMMA, [u]) => {
                Some(self.call(Context::POLYGAMMA, vec![Term::zero(self), u.clone()]))
            }
            (Context::POLYGAMMA, [Term::Value(m), Term::Value(q)]) => {
                let m = u64::try_from(&m.value).ok().filter(|m| *m <= MAX_ORDER)?;
                self.eval_polygamma(m, &q.value)
            }
            (Context::ZETA, [Term::Value(s)]) => self.eval_zeta(&s.value),
            _ => None,
        }
    }

    /// Build the function `ident(args)`, normalized.
    fn call(self, ident: Symbol, args: Vec<Term<Self>>) -> Term<Self> {
        Term::Fun(Box::new(Fun::new(ident, args, self))).normalize()
    }

    /// `{$psi^((m))(q)$}` for an integer or half-integer `q`, `None` at the poles `{$q <= 0$}` integer.
    fn eval_polygamma(self, m: u64, q: &Rational) -> Option<Term<Self>> {
        let gamma = Term::Symbol(SymbolTerm::new(Context::EULER_GAMMA, self));
        let zeta = || self.call(Context::ZETA, vec![self.value(Rational::from(m + 1))]);
        if let Ok(n) = u64::try_from(q) {
            if n == 0 || n > MAX_HARMONIC {
                return None;
            }
            // `{$psi(n) = -gamma + H_(n - 1)$}`,
            // `{$psi^((m))(n) = (-1)^(m + 1) m! (zeta(m + 1) - H_(n - 1)^((m + 1)))$}`
            let harmonic = self.value(harmonic(n - 1, m + 1));
            return Some(if m == 0 {
                harmonic - gamma
            } else {
                self.value(polygamma_factor(m)) * (zeta() - harmonic)
            });
        }
        let half = Rational::from_signeds(1, 2);
        let n = i64::try_from(&(q - &half)).ok()?;
        if n.unsigned_abs() > MAX_HARMONIC {
            return None;
        }
        // `{$psi(1/2) = -gamma - 2 ln 2$}`, `{$psi^((m))(1/2) = (-1)^(m + 1) m! (2^(m + 1) - 1) zeta(m + 1)$}`
        let at_half = if m == 0 {
            -gamma
                - self.value(Rational::from(2))
                    * self.call(Context::LN, vec![self.value(Rational::from(2))])
        } else {
            let scale = polygamma_factor(m) * (Rational::from(2_u32).pow(m + 1) - Rational::ONE);
            self.value(scale) * zeta()
        };
        // `{$psi^((m))(t + 1) = psi^((m))(t) + (-1)^m m! / t^(m + 1)$}`
        let term = |k: i64| (Rational::from(k) + &half).pow(m + 1).pow(-1_i64);
        let shift = if n >= 0 {
            (0..n).fold(Rational::ZERO, |sum, k| sum + term(k))
        } else {
            -(n..0).fold(Rational::ZERO, |sum, k| sum + term(k))
        };
        Some(at_half - self.value(polygamma_factor(m) * shift))
    }

    /// `{$zeta(n)$}` for an integer `n`: `{$zeta(2 k) = (-1)^(k + 1) B_(2 k) (2 pi)^(2 k) / (2 (2 k)!)$}`,
    /// `{$zeta(-n) = (-1)^n B_(n + 1) / (n + 1)$}`, `None` for odd `{$n >= 1$}`.
    fn eval_zeta(self, s: &Rational) -> Option<Term<Self>> {
        let n = i64::try_from(s)
            .ok()
            .filter(|n| n.unsigned_abs() <= MAX_ORDER)?;
        if n > 0 {
            if n % 2 == 1 {
                return None;
            }
            let n = n.unsigned_abs();
            let index = usize::try_from(n).ok()?;
            let coefficient = bernoulli(index).abs() * Rational::from(2_u32).pow(n - 1)
                / Rational::from(Natural::factorial(n));
            let pi = Term::Symbol(SymbolTerm::new(Context::PI, self));
            return Some(self.value(coefficient) * pi.pow(&self.value(Rational::from(n))));
        }
        let m = n.unsigned_abs();
        let b = bernoulli(usize::try_from(m + 1).ok()?) / Rational::from(m + 1);
        Some(self.value(if m % 2 == 0 { b } else { -b }))
    }
}
