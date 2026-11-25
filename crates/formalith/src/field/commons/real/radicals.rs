//! Constant radical expressions: sums of rational multiples of products of roots of positive values, possibly
//! nested, whose inverses are rationalized (`{$1/(1 + sqrt(2)) = sqrt(2) - 1$}`,
//! `{$1/(sqrt(2) + root(3, 3))$}` in the tower of the radicals) and whose products are expanded
//! (`{$sqrt(2) (sqrt(2) + 1) = sqrt(2) + 2$}`), so that equal constants have a single form.

use std::{cmp::Ordering, collections::BTreeMap};

use malachite::{
    Integer, Natural, Rational,
    base::num::{
        arithmetic::traits::{Gcd, Lcm, Pow},
        basic::traits::{One, Zero},
    },
};

use super::{
    expr::{Expr, constant_sign, one, value, zero},
    primes,
};
use crate::{
    polynom::fraction::solve_linear_unique,
    term::{self, Term, flags::Flags},
};

/// Largest number of terms of the expansion of a product, past which it stays a product.
const MAX_TERMS: usize = 256;
/// Largest dimension of the tower of the radicals of a sum whose inverse is computed (the product of the orders of
/// its generators), its rationalized form having up to that many terms.
const MAX_DIMENSION: usize = 64;
/// Largest absolute value of an integer exponent in the tower.
const MAX_EXPONENT: i64 = 64;

/// Whether `term` is a product of roots of positive values, and of nested roots (see [`is_root`]) when `nested`,
/// possibly times a rational.
fn is_radical_monomial(term: &Expr, nested: bool) -> bool {
    if term.is_approximate() {
        return false;
    }
    match term {
        Term::Value(_) => true,
        Term::Mul(mul) => mul.iter().all(|f| is_root(f, nested)),
        _ => is_root(term, nested),
    }
}

/// Whether `term` is a root of a positive value, or when `nested` a nested root `{$s^(p/q)$}` of a positive radical
/// sum `s`.
fn is_root(term: &Expr, nested: bool) -> bool {
    let Term::Pow(pow) = term else {
        return false;
    };
    match (&*pow.base, &**pow.exponant) {
        (Term::Value(base), Term::Value(_)) => base.value > 0,
        (Term::Add(add), Term::Value(e)) => {
            nested
                && e.value.denominator_ref() != &1u32
                && is_radical_sum(add, true)
                && constant_sign(&pow.base) == Some(Ordering::Greater)
        }
        _ => false,
    }
}

/// Whether `add` is a sum of rational multiples of products of roots of positive values, and of nested roots when
/// `nested`.
fn is_radical_sum(add: &term::Add<super::Real>, nested: bool) -> bool {
    !add.is_approximate() && add.iter().all(|t| is_radical_monomial(t, nested))
}

/// A factor of a product expanded by [`expand_product`]: a root of a positive value, a radical sum or a positive
/// integer power of one, with the sum and its exponent.
enum Factor<'a> {
    Root,
    Sum(&'a term::Add<super::Real>, usize),
}

fn factor(term: &Expr) -> Option<Factor<'_>> {
    match term {
        Term::Add(add) if is_radical_sum(add, false) => Some(Factor::Sum(add, 1)),
        Term::Pow(pow) => match (&*pow.base, &**pow.exponant) {
            (Term::Add(add), Term::Value(n))
                if n.value.denominator_ref() == &1u32 && is_radical_sum(add, false) =>
            {
                let n = usize::try_from(&n.value).ok().filter(|n| *n >= 1)?;
                Some(Factor::Sum(add, n))
            }
            _ => is_radical_monomial(term, false).then_some(Factor::Root),
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
/// `{$-(sqrt(2) - 1) = 1 - sqrt(2)$}`. Other factors are kept. The product is computed in the tower of the radicals,
/// or term by term when it is too big.
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
        if let Some(product) = tower_product(&radicals) {
            product
        } else {
            let factors: Vec<_> = factors
                .into_iter()
                .map(|(terms, n, _)| (terms, n))
                .collect();
            expand(&factors)?
        }
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
pub fn content(coefficients: impl Iterator<Item = Rational>) -> Rational {
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
    if n.denominator_ref() != &1u32 || !is_radical_sum(add, *n < 0) {
        return None;
    }
    if *n >= 2 {
        let n = usize::try_from(n).ok()?;
        let sum = Term::Add(add.clone());
        return tower_product(&vec![&sum; n])
            .or_else(|| expand(&[(add.iter().cloned().collect(), n)]));
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

/// The inverse of a non-zero radical sum, computed in the tower of its radicals.
fn inverse(add: &term::Add<super::Real>) -> Option<Expr> {
    let sum = Term::Add(add.clone());
    let tower = Tower::new(&[&sum])?;
    let element = tower.element(&sum)?;
    let (content, sum) = content_out(&tower.term(&tower.inverse(&element)?));
    Some(value(content) * sum)
}

/// The product of `factors` computed in the tower of their radicals, so that its monomials have a single form
/// (`{$root(3, 2) root(6, 32) = 2 root(6, 2)$}`, which normalization doesn't merge). `None` when the tower is too
/// big.
fn tower_product(factors: &[&Expr]) -> Option<Expr> {
    let tower = Tower::new(factors)?;
    let product = factors
        .iter()
        .try_fold(tower.constant(Rational::ONE), |res, f| {
            Some(tower.times(&res, &tower.element(f)?))
        })?;
    Some(tower.term(&product))
}

/// Primes whose exponents in the value bases of a [`Tower`] are `{$k_p w$}`, as `w` and the `{$(p, k_p)$}`.
type Group = (Vec<i64>, Vec<(Integer, i64)>);

/// An element of a [`Tower`], by its coordinates in the basis of the monomials `{$product_k y_k^(e_k)$}` with
/// `{$e_k < q_k$}`, the monomial of index `{$sum_k e_k s_k$}` (`{$s_k = product_(j < k) q_j$}`).
type Element = Vec<Rational>;

/// The tower `{$QQ[y_1, ..., y_n] / (y_1^(q_1) - b_1, ..., y_n^(q_n) - b_n)$}` of the radicals of a constant
/// expression, like `holonomic/algebraic.rs` over `{$K(w)$}`. The value bases give one generator per group of
/// primes whose exponents in the bases are proportional (`{$sqrt(2) + root(3, 3)$}` has the generators 2 and 3,
/// `{$root(64, 6)$}` the generator 6), and each nested radical `{$s^(p/q)$}` of a positive radical sum `s` one more.
///
/// Evaluating the generators at the radicals is a ring homomorphism to `{$RR$}`, so an inverse found in the tower
/// is the inverse of the radical expression, even when the tower isn't a field. The value generators being coprime
/// and not perfect powers, their monomials are linearly independent over `{$QQ$}`, so that forms without nested
/// radicals are canonical.
struct Tower {
    /// The generators: positive rationals, then nested radical sums, inner ones first.
    generators: Vec<Expr>,
    /// The orders `{$q_k$}`.
    orders: Vec<usize>,
    /// `{$s_k = product_(j < k) q_j$}`.
    strides: Vec<usize>,
    dim: usize,
    /// The bases `{$b_k$}` as elements of the previous levels.
    bases: Vec<Element>,
    /// The value bases, as products `{$product_k G_k^(e_k)$}` of the value generators, given by `{$(k, e_k)$}`.
    values: Vec<(Rational, Vec<(usize, i64)>)>,
}

impl Tower {
    /// The tower of the radicals of `terms`, `None` if one isn't a constant radical expression, if they have no
    /// radical, or if the tower is too big.
    fn new(terms: &[&Expr]) -> Option<Self> {
        let mut values = vec![];
        let mut nested = vec![];
        for term in terms {
            collect(term, &mut values, &mut nested)?;
        }
        // The exponent of each prime in each value base
        let mut primes: BTreeMap<Integer, Vec<i64>> = BTreeMap::new();
        for (i, (base, _)) in values.iter().enumerate() {
            for (p, e) in primes::factor_rational(base)? {
                primes.entry(p).or_insert_with(|| vec![0; values.len()])[i] = e;
            }
        }
        // `{$v_p = k_p w$}` with `w` primitive, its first non-zero entry positive: the primes with the same `w`
        // make the generator `{$G = product_p p^(k_p/d)$}`, `d` the gcd of the `{$k_p$}`, so that `{$b_i = G^(d w_i)$}`
        let mut groups: Vec<Group> = vec![];
        for (p, v) in primes {
            let g = v.iter().fold(0, |g: u64, e| g.gcd(e.unsigned_abs()));
            let g = i64::try_from(g).ok()?;
            let k = if *v.iter().find(|e| **e != 0)? < 0 {
                -g
            } else {
                g
            };
            let w: Vec<i64> = v.iter().map(|e| e / k).collect();
            match groups.iter_mut().find(|(u, _)| *u == w) {
                Some((_, group)) => group.push((p, k)),
                None => groups.push((w, vec![(p, k)])),
            }
        }
        let mut generators = vec![];
        let mut orders = vec![];
        let mut decompositions = vec![vec![]; values.len()];
        for (j, (w, group)) in groups.iter().enumerate() {
            let d = group
                .iter()
                .fold(0, |d: u64, (_, k)| d.gcd(k.unsigned_abs()));
            let d = i64::try_from(d).ok()?;
            let generator = group.iter().fold(Rational::ONE, |res, (p, k)| {
                res * Rational::from(p).pow(k / d)
            });
            let mut order = Natural::ONE;
            for (i, (_, exponants)) in values.iter().enumerate() {
                let e = d * w[i];
                if e != 0 {
                    decompositions[i].push((j, e));
                }
                for q in exponants {
                    order = order.lcm((q * Rational::from(e)).denominator_ref());
                }
            }
            generators.push(value(generator));
            orders.push(usize::try_from(&order).ok()?);
        }
        for (s, q) in &nested {
            generators.push(s.clone());
            orders.push(*q);
        }
        let mut strides = vec![];
        let mut dim = 1usize;
        for &q in &orders {
            strides.push(dim);
            dim = dim.checked_mul(q)?;
            if dim > MAX_DIMENSION {
                return None;
            }
        }
        if dim == 1 {
            return None;
        }
        let mut tower = Self {
            generators,
            orders,
            strides,
            dim,
            bases: vec![],
            values: values
                .into_iter()
                .zip(decompositions)
                .map(|((base, _), decomposition)| (base, decomposition))
                .collect(),
        };
        for k in 0..tower.generators.len() {
            // A nested base only has radicals of the previous levels
            let base = match &tower.generators[k] {
                Term::Value(g) => tower.constant(g.value.clone()),
                s => tower.element(&s.clone())?,
            };
            tower.bases.push(base);
        }
        Some(tower)
    }

    fn zero(&self) -> Element {
        vec![Rational::ZERO; self.dim]
    }

    fn constant(&self, c: Rational) -> Element {
        let mut res = self.zero();
        res[0] = c;
        res
    }

    /// The exponents of the monomial of index `i`.
    fn exponents(&self, i: usize) -> Vec<usize> {
        self.strides
            .iter()
            .zip(&self.orders)
            .map(|(&s, &q)| i / s % q)
            .collect()
    }

    /// `{$product_k y_k^(e_k)$}` for any natural exponents, reduced with `{$y_k^(q_k) = b_k$}`.
    fn monomial(&self, exponents: &[usize]) -> Element {
        // The highest level to reduce: the reduction only raises exponents of lower levels, so it terminates
        let Some(k) = (0..exponents.len())
            .rev()
            .find(|&k| exponents[k] >= self.orders[k])
        else {
            let mut res = self.zero();
            let i = exponents
                .iter()
                .zip(&self.strides)
                .map(|(&e, &s)| e * s)
                .sum::<usize>();
            res[i] = Rational::ONE;
            return res;
        };
        let mut rest = exponents.to_vec();
        rest[k] -= self.orders[k];
        self.times_monomial(&self.bases[k], &rest)
    }

    /// `a` times `{$product_k y_k^(e_k)$}`.
    fn times_monomial(&self, a: &Element, exponents: &[usize]) -> Element {
        let mut res = self.zero();
        for (i, c) in a.iter().enumerate() {
            if *c == 0u32 {
                continue;
            }
            let sum: Vec<usize> = self
                .exponents(i)
                .iter()
                .zip(exponents)
                .map(|(e, f)| e + f)
                .collect();
            add_scaled(&mut res, &self.monomial(&sum), c);
        }
        res
    }

    fn times(&self, a: &Element, b: &Element) -> Element {
        let mut res = self.zero();
        for (j, c) in b.iter().enumerate() {
            if *c != 0u32 {
                add_scaled(&mut res, &self.times_monomial(a, &self.exponents(j)), c);
            }
        }
        res
    }

    /// The inverse of `a`, `None` if it is a zero divisor.
    fn inverse(&self, a: &Element) -> Option<Element> {
        // `{$a v = 1$}`, the columns of the matrix of the multiplication by `a` being the products `{$a e_j$}`
        let columns: Vec<Element> = (0..self.dim)
            .map(|j| self.times_monomial(a, &self.exponents(j)))
            .collect();
        let rows = (0..self.dim)
            .map(|i| {
                let mut row: Vec<Rational> = columns.iter().map(|c| c[i].clone()).collect();
                row.push(if i == 0 {
                    Rational::ONE
                } else {
                    Rational::ZERO
                });
                row
            })
            .collect();
        solve_linear_unique(rows, self.dim)
    }

    /// `{$a^n$}`, `None` for a non-invertible `a` and a negative `n`.
    fn pow(&self, a: &Element, n: i64) -> Option<Element> {
        let base = if n < 0 { self.inverse(a)? } else { a.clone() };
        let mut res = self.constant(Rational::ONE);
        for _ in 0..n.unsigned_abs() {
            res = self.times(&res, &base);
        }
        Some(res)
    }

    /// `term` as an element of the tower, `None` if it divides by a zero divisor.
    fn element(&self, term: &Expr) -> Option<Element> {
        match term {
            Term::Value(c) => Some(self.constant(c.value.clone())),
            Term::Add(add) => add.iter().try_fold(self.zero(), |mut res, t| {
                add_scaled(&mut res, &self.element(t)?, &Rational::ONE);
                Some(res)
            }),
            Term::Mul(mul) => mul
                .iter()
                .try_fold(self.constant(mul.coefficient.clone()), |res, t| {
                    Some(self.times(&res, &self.element(t)?))
                }),
            Term::Pow(pow) => {
                let Term::Value(e) = &**pow.exponant else {
                    return None;
                };
                if let Term::Value(b) = &*pow.base {
                    return self.value_power(&b.value, &e.value);
                }
                if let Ok(n) = i64::try_from(&e.value) {
                    let n = Some(n).filter(|n| n.abs() <= MAX_EXPONENT)?;
                    return self.pow(&self.element(&pow.base)?, n);
                }
                // `{$s^(p/r) = y^(p q/r)$}`
                let k = self.generators.iter().position(|s| s == &*pow.base)?;
                let n = &e.value * Rational::from(self.orders[k]);
                let n = i64::try_from(&n).ok().filter(|n| n.abs() <= MAX_EXPONENT)?;
                let mut exponents = vec![0; self.orders.len()];
                exponents[k] = usize::try_from(n.unsigned_abs()).ok()?;
                let y = self.monomial(&exponents);
                if n < 0 { self.inverse(&y) } else { Some(y) }
            }
            Term::Symbol(_) | Term::Fun(_) => None,
        }
    }

    /// `{$b^q = product_k G_k^(q e_k)$}` for a value base `b`, each `{$G_k^(q e_k) = y_k^(m_k)$}` being written
    /// `{$G_k^a y_k^r$}` with `{$m_k = a q_k + r$}`, `{$0 <= r < q_k$}`.
    fn value_power(&self, b: &Rational, q: &Rational) -> Option<Element> {
        let (_, decomposition) = self.values.iter().find(|(base, _)| base == b)?;
        let mut coefficient = Rational::ONE;
        let mut exponents = vec![0; self.orders.len()];
        for &(k, e) in decomposition {
            let order = i64::try_from(self.orders[k]).ok()?;
            let m = i64::try_from(&(q * Rational::from(e * order))).ok()?;
            let Term::Value(g) = &self.generators[k] else {
                return None;
            };
            coefficient *= g.value.clone().pow(m.div_euclid(order));
            exponents[k] = usize::try_from(m.rem_euclid(order)).ok()?;
        }
        let mut res = self.zero();
        add_scaled(&mut res, &self.monomial(&exponents), &coefficient);
        Some(res)
    }

    /// The element `a` as a sum of rational multiples of monomials in the radicals.
    fn term(&self, a: &Element) -> Expr {
        a.iter()
            .enumerate()
            .filter(|(_, c)| **c != 0u32)
            .fold(zero(), |res, (i, c)| {
                let monomial = self
                    .exponents(i)
                    .iter()
                    .enumerate()
                    .filter(|(_, e)| **e != 0)
                    .fold(one(), |res, (k, &e)| {
                        let exponant = Rational::from(e) / Rational::from(self.orders[k]);
                        res * self.generators[k].pow(&value(exponant))
                    });
                res + value(c.clone()) * monomial
            })
    }
}

/// `{$a <- a + c b$}`.
fn add_scaled(a: &mut Element, b: &Element, c: &Rational) {
    for (x, y) in a.iter_mut().zip(b) {
        if *y != 0u32 {
            *x += y * c;
        }
    }
}

/// Collects the value bases of the radicals of `term` with their exponents, and its nested radicals `{$s^(p/q)$}`
/// of positive radical sums `s`, inner ones first, with the lcm of the `q`. `None` if `term` isn't a constant
/// radical expression.
fn collect(
    term: &Expr,
    values: &mut Vec<(Rational, Vec<Rational>)>,
    nested: &mut Vec<(Expr, usize)>,
) -> Option<()> {
    match term {
        Term::Value(_) => Some(()),
        Term::Add(add) => add.iter().try_for_each(|t| collect(t, values, nested)),
        Term::Mul(mul) => mul.iter().try_for_each(|t| collect(t, values, nested)),
        Term::Pow(pow) => {
            let Term::Value(e) = &**pow.exponant else {
                return None;
            };
            match &*pow.base {
                Term::Value(b) if b.value > 0 => {
                    match values.iter_mut().find(|(base, _)| *base == b.value) {
                        Some((_, exponants)) => exponants.push(e.value.clone()),
                        None => values.push((b.value.clone(), vec![e.value.clone()])),
                    }
                    Some(())
                }
                base @ Term::Add(_) => {
                    collect(base, values, nested)?;
                    let q = usize::try_from(e.value.denominator_ref()).ok()?;
                    if q != 1 {
                        if constant_sign(base) != Some(Ordering::Greater) {
                            return None;
                        }
                        match nested.iter_mut().find(|(s, _)| s == base) {
                            Some((_, order)) => *order = order.lcm(q),
                            None => nested.push((base.clone(), q)),
                        }
                    }
                    Some(())
                }
                _ => None,
            }
        }
        Term::Symbol(_) | Term::Fun(_) => None,
    }
}
