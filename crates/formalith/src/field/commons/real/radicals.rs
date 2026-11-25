//! Constant radical expressions: sums of rational multiples of roots of positive values, whose inverses are
//! rationalized (`{$1/(1 + sqrt(2)) = sqrt(2) - 1$}`) and whose products are expanded
//! (`{$sqrt(2) (sqrt(2) + 1) = sqrt(2) + 2$}`), so that equal constants have a single form.

use std::collections::BTreeMap;

use malachite::{
    Natural, Rational,
    base::num::{
        arithmetic::traits::{Gcd, Lcm},
        basic::traits::{One, Zero},
    },
};

use super::{
    expr::{Expr, one, value, zero},
    primes,
};
use crate::{
    polynom::dense::Poly,
    term::{self, Term, flags::Flags},
};

/// Largest number of terms of the expansion of a product, past which it stays a product.
const MAX_TERMS: usize = 256;
/// Largest number of distinct primes under the square roots of a sum whose inverse is computed, its rationalized
/// form having up to `{$2^n$}` terms.
const MAX_PRIMES: usize = 6;
/// Largest order of the radical of a sum in a single radical whose inverse is computed.
const MAX_ORDER: u64 = 64;

/// A term `{$c b^q$}` of a radical sum, `{$b = 1$}` and `{$q = 0$}` for a rational term.
struct Radical {
    coefficient: Rational,
    base: Rational,
    exponant: Rational,
}

/// The term `{$c b^q$}` of a radical sum, with `{$b > 0$}` and a non-integer `q`, or a rational.
fn radical(term: &Expr) -> Option<Radical> {
    let power = |term: &Expr| match term {
        Term::Pow(pow) => match (&*pow.base, &**pow.exponant) {
            (Term::Value(base), Term::Value(exponant))
                if base.value > 0 && exponant.value.denominator_ref() != &1u32 =>
            {
                Some((base.value.clone(), exponant.value.clone()))
            }
            _ => None,
        },
        _ => None,
    };
    match term {
        Term::Value(c) => Some(Radical {
            coefficient: c.value.clone(),
            base: Rational::ONE,
            exponant: Rational::ZERO,
        }),
        Term::Mul(mul) => match mul.iter().collect::<Vec<_>>().as_slice() {
            [factor] => power(factor).map(|(base, exponant)| Radical {
                coefficient: mul.coefficient.clone(),
                base,
                exponant,
            }),
            _ => None,
        },
        _ => power(term).map(|(base, exponant)| Radical {
            coefficient: Rational::ONE,
            base,
            exponant,
        }),
    }
}

/// Whether `term` is a product of roots of positive values, possibly times a rational.
fn is_radical_monomial(term: &Expr) -> bool {
    let is_root = |term: &Expr| {
        matches!(term, Term::Pow(pow) if matches!(
            (&*pow.base, &**pow.exponant),
            (Term::Value(base), Term::Value(_)) if base.value > 0
        ))
    };
    if term.is_approximate() {
        return false;
    }
    match term {
        Term::Value(_) => true,
        Term::Mul(mul) => mul.iter().all(is_root),
        _ => is_root(term),
    }
}

/// Whether `add` is a sum of rational multiples of products of roots of positive values.
fn is_radical_sum(add: &term::Add<super::Real>) -> bool {
    !add.is_approximate() && add.iter().all(is_radical_monomial)
}

/// A factor of a product expanded by [`expand_product`]: a root of a positive value, a radical sum or a positive
/// integer power of one, with the sum and its exponent.
enum Factor<'a> {
    Root,
    Sum(&'a term::Add<super::Real>, usize),
}

fn factor(term: &Expr) -> Option<Factor<'_>> {
    match term {
        Term::Add(add) if is_radical_sum(add) => Some(Factor::Sum(add, 1)),
        Term::Pow(pow) => match (&*pow.base, &**pow.exponant) {
            (Term::Add(add), Term::Value(n)) if is_radical_sum(add) => {
                let n = usize::try_from(&n.value).ok().filter(|n| *n >= 1)?;
                Some(Factor::Sum(add, n))
            }
            _ => is_radical_monomial(term).then_some(Factor::Root),
        },
        _ => None,
    }
}

/// The terms of a sum, or the term itself.
fn terms(term: &Expr) -> Vec<Expr> {
    match term {
        Term::Add(add) => add.iter().cloned().collect(),
        _ => vec![term.clone()],
    }
}

/// The expansion of the product of `factors`, constant radical expressions given by their terms and their
/// exponent, `None` when it would have more than [`MAX_TERMS`] terms. The products of terms are products of roots,
/// so they don't come back here.
fn expand(factors: &[(Vec<Expr>, usize)]) -> Option<Expr> {
    let mut res = vec![one()];
    for (base, n) in factors {
        for _ in 0..*n {
            if res.len() * base.len() > MAX_TERMS {
                return None;
            }
            let sum = res
                .iter()
                .flat_map(|a| base.iter().map(move |b| a * b))
                .fold(zero(), |res, t| res + t);
            res = terms(&sum);
        }
    }
    Some(res.into_iter().fold(zero(), |res, t| res + t))
}

/// The expansion of the constant radical factors of a product, when one of them is a sum and there is another one or
/// it is a power, with the content of the sum moved to the coefficient: `{$sqrt(2) (sqrt(2) + 1) = sqrt(2) + 2$}`,
/// `{$(8 - 4 sqrt(3))/4 = 2 - sqrt(3)$}`, `{$x (sqrt(3) + 1)^2 = 2 (sqrt(3) + 2) x$}`, and a lone `-1` distributed,
/// `{$-(sqrt(2) - 1) = 1 - sqrt(2)$}`. Other factors are kept.
pub(super) fn expand_product(mul: &term::Mul<super::Real>) -> Option<Expr> {
    if mul.is_approximate() {
        return None;
    }
    let (radicals, rest): (Vec<&Expr>, Vec<&Expr>) = mul
        .iter()
        .partition(|factor| self::factor(factor).is_some());
    let factors: Vec<(Vec<Expr>, usize, bool)> = radicals
        .iter()
        .map(|f| match self::factor(f) {
            Some(Factor::Sum(add, n)) => (add.iter().cloned().collect(), n, true),
            _ => (vec![(*f).clone()], 1, false),
        })
        .collect();
    let sums: Vec<usize> = factors
        .iter()
        .filter(|(_, _, sum)| *sum)
        .map(|(_, n, _)| *n)
        .collect();
    let expanded = !sums.is_empty() && (factors.len() >= 2 || sums.iter().any(|n| *n >= 2));
    let product = if expanded {
        let factors: Vec<_> = factors
            .into_iter()
            .map(|(terms, n, _)| (terms, n))
            .collect();
        expand(&factors)?
    } else if let [factor] = radicals.as_slice()
        && sums == [1]
    {
        (*factor).clone()
    } else {
        return None;
    };
    let (content, product) = content_out(&product);
    let opposite = rest.is_empty() && mul.coefficient == -1;
    if !expanded && content == 1u32 && !opposite {
        return None;
    }
    let coefficient = &mul.coefficient * content;
    if rest.is_empty() && coefficient == 1u32 {
        return Some(product);
    }
    if rest.is_empty() && coefficient == -1 {
        // `{$-(sqrt(2) - 1) = 1 - sqrt(2)$}`
        return Some(terms(&product).iter().fold(zero(), |res, t| res - t));
    }
    Some(
        rest.into_iter()
            .fold(value(coefficient) * product, |res, f| res * f),
    )
}

/// `(c, s)` with `{$t = c s$}`, `c` the positive content of the rational coefficients of the terms of `t`.
fn content_out(term: &Expr) -> (Rational, Expr) {
    let coefficient = |t: &Expr| match t {
        Term::Value(v) => v.value.clone(),
        Term::Mul(mul) => mul.coefficient.clone(),
        _ => Rational::ONE,
    };
    let content = content(terms(term).iter().map(coefficient));
    if content == 0u32 || content == 1u32 {
        return (Rational::ONE, term.clone());
    }
    let res = terms(term)
        .iter()
        .fold(zero(), |res, t| res + t * &value(Rational::ONE / &content));
    (content, res)
}

/// The positive gcd of rationals, 0 for none.
fn content(coefficients: impl Iterator<Item = Rational>) -> Rational {
    let (numerator, denominator) = coefficients.fold(
        (Natural::ZERO, Natural::ONE),
        |(numerator, denominator), c| {
            (
                numerator.gcd(c.numerator_ref()),
                denominator.lcm(c.denominator_ref()),
            )
        },
    );
    Rational::from_naturals(numerator, denominator)
}

/// The integer power `{$s^n$}` of a radical sum `s`, expanded for `{$n >= 2$}`, rationalized for `{$n < 0$}`:
/// `{$(1 + sqrt(2))^2 = 3 + 2 sqrt(2)$}`, `{$1/(1 + sqrt(2)) = sqrt(2) - 1$}`. `None` when it can't be computed,
/// or would be too big.
pub(super) fn power(add: &term::Add<super::Real>, n: &Rational) -> Option<Expr> {
    if n.denominator_ref() != &1u32 || !is_radical_sum(add) {
        return None;
    }
    if *n >= 2 {
        let n = usize::try_from(n).ok()?;
        return expand(&[(add.iter().cloned().collect(), n)]);
    }
    if *n >= 0 {
        return None;
    }
    let inverse = inverse(add)?;
    if *n == -1 {
        Some(inverse)
    } else {
        let k = -n;
        (k <= 8).then(|| inverse.pow(&value(k)))
    }
}

/// The inverse of a non-zero radical sum: square roots of any number of integers, or roots of a single integer.
fn inverse(add: &term::Add<super::Real>) -> Option<Expr> {
    let radicals: Vec<Radical> = add.iter().map(radical).collect::<Option<_>>()?;
    let integer = |q: &Rational| q.denominator_ref() == &1u32;
    if !radicals.iter().all(|r| integer(&r.base)) {
        return None;
    }
    if radicals
        .iter()
        .all(|r| r.exponant == 0 || r.exponant == Rational::from_signeds(1, 2))
    {
        return inverse_quadratic(&radicals);
    }
    // Roots of powers of a single integer, `{$root(3, 4) = 2^(2/3)$}`
    let mut radicals = radicals;
    for r in radicals.iter_mut().filter(|r| r.exponant != 0) {
        let (root, k) = perfect_power(r.base.numerator_ref())?;
        r.base = Rational::from(root);
        r.exponant *= Rational::from(k);
    }
    let mut bases = radicals.iter().filter(|r| r.exponant != 0).map(|r| &r.base);
    let base = bases.next()?.clone();
    if bases.any(|b| *b != base) {
        return None;
    }
    inverse_single(&radicals, &base)
}

/// `{$n = r^k$}` with `k` the largest possible, as `(r, k)`. `None` if `n` can't be factored.
fn perfect_power(n: &Natural) -> Option<(Natural, u64)> {
    let factors = primes::factor(n)?;
    let k = factors.iter().fold(0, |k, (_, e)| k.gcd(*e));
    if k <= 1 {
        return Some((n.clone(), 1));
    }
    let root = factors
        .iter()
        .fold(Natural::ONE, |res, (p, e)| res * primes_pow(p, e / k));
    Some((root, k))
}

/// A sum `{$sum_m c_m sqrt(m)$}` over square-free naturals `m`.
type Quadratic = BTreeMap<Natural, Rational>;

fn quadratic_mul(a: &Quadratic, b: &Quadratic) -> Quadratic {
    let mut res = Quadratic::new();
    for (m, c) in a {
        for (n, d) in b {
            // `{$sqrt(m) sqrt(n) = g sqrt((m/g) (n/g))$}`, square-free since `m/g` and `n/g` are coprime
            let g = m.gcd(n);
            let product = (m / &g) * (n / &g);
            *res.entry(product).or_insert(Rational::ZERO) += c * d * Rational::from(g);
        }
    }
    res.retain(|_, c| *c != 0u32);
    res
}

/// The inverse of `{$sum_i c_i sqrt(m_i)$}`, by multiplying it by its conjugates for each prime `p` of the `{$m_i$}`:
/// writing it `{$A + sqrt(p) B$}`, `{$(A + sqrt(p) B)(A - sqrt(p) B) = A^2 - p B^2$}` has no `{$sqrt(p)$}`, and isn't
/// zero since `{$sqrt(p)$}` isn't in the field of the square roots of the other primes.
fn inverse_quadratic(radicals: &[Radical]) -> Option<Expr> {
    let mut sum = Quadratic::new();
    let mut all_primes: Vec<Natural> = vec![];
    for r in radicals {
        let (mut m, mut c) = (Natural::ONE, r.coefficient.clone());
        if r.exponant != 0 {
            for (p, e) in primes::factor(r.base.numerator_ref())? {
                // `{$sqrt(p^e) = p^(floor(e/2)) sqrt(p^(e mod 2))$}`
                c *= Rational::from(primes_pow(&p, e / 2));
                if e % 2 == 1 {
                    m *= &p;
                    if !all_primes.contains(&p) {
                        all_primes.push(p);
                    }
                }
            }
        }
        *sum.entry(m).or_insert(Rational::ZERO) += c;
    }
    sum.retain(|_, c| *c != 0u32);
    if all_primes.len() > MAX_PRIMES || sum.is_empty() {
        return None;
    }
    let mut conjugate = Quadratic::from([(Natural::ONE, Rational::ONE)]);
    for p in &all_primes {
        let conjugate_by_p: Quadratic = sum
            .iter()
            .map(|(m, c)| {
                let divisible = (m % p) == 0u32;
                (m.clone(), if divisible { -c } else { c.clone() })
            })
            .collect();
        if conjugate_by_p == sum {
            continue;
        }
        sum = quadratic_mul(&sum, &conjugate_by_p);
        conjugate = quadratic_mul(&conjugate, &conjugate_by_p);
    }
    let [(m, d)] = sum.into_iter().collect::<Vec<_>>().try_into().ok()?;
    if m != 1u32 || d == 0u32 {
        return None;
    }
    Some(with_content(conjugate.into_iter().map(|(m, c)| {
        (c / &d, Rational::from(m), Rational::from_signeds(1, 2))
    })))
}

fn primes_pow(p: &Natural, e: u64) -> Natural {
    (0..e).fold(Natural::ONE, |res, _| res * p)
}

/// The inverse of `{$sum_i c_i r^(q_i)$}`, a polynomial `{$P(alpha)$}` in `{$alpha = r^(1/n)$}`, `n` being the lcm of
/// the denominators of the `{$q_i$}`: `{$P^(-1)$}` modulo `{$x^n - r$}`, when they are coprime.
fn inverse_single(radicals: &[Radical], base: &Rational) -> Option<Expr> {
    let n = radicals
        .iter()
        .fold(Natural::ONE, |n, r| n.lcm(r.exponant.denominator_ref()));
    let n = u64::try_from(&n).ok().filter(|n| *n <= MAX_ORDER)?;
    let order = usize::try_from(n).ok()?;
    let mut coefficients = vec![Rational::ZERO; order];
    for r in radicals {
        // `{$0 <= q < 1$}` once normalized, but a sum may hold other powers
        let j = &r.exponant * Rational::from(n);
        let j = usize::try_from(&j).ok().filter(|j| *j < order)?;
        coefficients[j] += &r.coefficient;
    }
    let p = Poly::new(coefficients);
    let modulus = Poly::monomial(Rational::ONE, order).sub(&Poly::constant(base.clone()));
    if p.is_zero() || p.gcd(&modulus) != Poly::one() {
        return None;
    }
    let inverse = p.inverse_mod(&modulus);
    Some(with_content(
        inverse
            .coefficients()
            .iter()
            .enumerate()
            .filter(|(_, c)| **c != 0u32)
            .map(|(j, c)| {
                let j = u64::try_from(j).unwrap_or_else(|_| unreachable!());
                (c.clone(), base.clone(), Rational::from_unsigneds(j, n))
            }),
    ))
}

/// The sum `{$sum_i c_i b_i^(q_i)$}` with its positive content out, `{$(sqrt(6) - sqrt(2))/4$}` rather than
/// `{$sqrt(6)/4 - sqrt(2)/4$}`.
fn with_content(terms: impl Iterator<Item = (Rational, Rational, Rational)>) -> Expr {
    let terms: Vec<_> = terms.collect();
    let content = content(terms.iter().map(|(c, _, _)| c.clone()));
    if content == 0u32 {
        return zero();
    }
    let sum = terms.into_iter().fold(zero(), |res, (c, base, exponant)| {
        let root = if exponant == 0 {
            value(Rational::ONE)
        } else {
            value(base).pow(&value(exponant))
        };
        res + value(c / &content) * root
    });
    value(content) * sum
}
