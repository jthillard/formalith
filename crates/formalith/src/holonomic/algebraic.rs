//! Algebraic functions of `w`: rational functions and rational powers of them, possibly nested, computed in the
//! tower `{$A = K(w)[y_1, ..., y_n] / (y_1^(q_1) - b_1, ..., y_n^(q_n) - b_n)$}` with one generator `{$y_k$}` per
//! radical `{$b_k^(1/q_k)$}`, `{$b_k$}` an element of the previous levels, and `K` the field of the parameters.
//!
//! The derivation `{$D(y_k) = D(b_k) / (q_k b_k) y_k$}` respects the relations, so evaluating the generators at
//! the radicals is a differential ring homomorphism: a linear relation between `{$f, D f, D^2 f, ...$}` in `A` is
//! a differential equation of `f`, and an element which is zero in `A` is identically zero (a non-zero one may
//! still be zero, when the bases have relations of their own).

use malachite::{Integer, Rational};

use crate::{
    context::Symbol,
    field::real::expr::{Expr, depends, map_tree, subs, value, zero},
    polynom::{dense::Coefficient, fraction::solve_linear_unique},
    sum::field::Params,
    term::Term,
};

use super::{
    dfinite::analytic_non_zero,
    ore::{self, Kind, Operator},
    ratfun::RatFun,
};

/// Largest dimension of the tower over `{$K(w)$}`.
const MAX_DIMENSION: usize = 64;

/// Largest absolute value of an integer exponent.
const MAX_EXPONENT: i64 = 64;

/// An element of the tower, by its coordinates in the basis of the monomials `{$product_k y_k^(e_k)$}` with
/// `{$e_k < q_k$}`, the monomial of index `{$sum_k e_k s_k$}` (`{$s_k = product_(j < k) q_j$}`).
type Element = Vec<RatFun>;

/// The tower of the radicals of an expression in `w`.
struct Tower {
    w: Symbol,
    /// The bases `{$b_k$}` as expressions, inner ones first.
    radicals: Vec<Expr>,
    /// The orders `{$q_k$}`.
    orders: Vec<usize>,
    /// `{$s_k = product_(j < k) q_j$}`.
    strides: Vec<usize>,
    dim: usize,
    /// The bases as elements of the previous levels.
    bases: Vec<Element>,
    /// `{$delta_k = D(b_k) / (q_k b_k)$}`, so that `{$D(y_k) = delta_k y_k$}`.
    deltas: Vec<Element>,
}

impl Tower {
    /// The tower of the radicals of `f` whose bases depend on `w`, `None` if `f` isn't an algebraic function of
    /// `w` (functions or symbolic exponents depending on `w`), if it has no such radical, or if the tower is too
    /// big.
    fn new(f: &Expr, w: Symbol, params: &mut Params) -> Option<Self> {
        let f = &split_bases(f, w);
        let mut radicals = vec![];
        let mut orders = vec![];
        collect(f, w, &mut radicals, &mut orders)?;
        if radicals.is_empty() {
            return None;
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
        let mut tower = Self {
            w,
            radicals: radicals.clone(),
            orders,
            strides,
            dim,
            bases: vec![],
            deltas: vec![],
        };
        for (k, base) in radicals.iter().enumerate() {
            // The base only has radicals of the previous levels, whose deltas are known
            let b = tower.element_split(base, params)?;
            let db = tower.derive(&b);
            let q = RatFun::from_rational(Rational::from(tower.orders[k]));
            let delta = scale(&tower.times(&db, &tower.inverse(&b)?), &q.inverse());
            tower.bases.push(b);
            tower.deltas.push(delta);
        }
        Some(tower)
    }

    fn zero(&self) -> Element {
        vec![RatFun::zero(); self.dim]
    }

    fn constant(&self, c: RatFun) -> Element {
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
            res[i] = RatFun::one();
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
            if c.is_zero() {
                continue;
            }
            let sum: Vec<usize> = self
                .exponents(i)
                .iter()
                .zip(exponents)
                .map(|(e, f)| e + f)
                .collect();
            res = plus(&res, &scale(&self.monomial(&sum), c));
        }
        res
    }

    fn times(&self, a: &Element, b: &Element) -> Element {
        let mut res = self.zero();
        for (j, c) in b.iter().enumerate() {
            if !c.is_zero() {
                let product = self.times_monomial(a, &self.exponents(j));
                res = plus(&res, &scale(&product, c));
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
                let mut row: Vec<RatFun> = columns.iter().map(|c| c[i].clone()).collect();
                row.push(if i == 0 {
                    RatFun::one()
                } else {
                    RatFun::zero()
                });
                row
            })
            .collect();
        solve_linear_unique(rows, self.dim)
    }

    /// `{$a^n$}`, `None` for a non-invertible `a` and a negative `n`.
    fn pow(&self, a: &Element, n: i64) -> Option<Element> {
        let base = if n < 0 { self.inverse(a)? } else { a.clone() };
        let mut res = self.constant(RatFun::one());
        for _ in 0..n.unsigned_abs() {
            res = self.times(&res, &base);
        }
        Some(res)
    }

    /// `{$D a$}`, with `{$D(r m) = r' m + r m sum_k e_k delta_k$}` for a monomial `m`.
    fn derive(&self, a: &Element) -> Element {
        let mut res = self.zero();
        for (i, c) in a.iter().enumerate() {
            if c.is_zero() {
                continue;
            }
            res[i] = res[i].plus(&c.derivative());
            let exponents = self.exponents(i);
            let mut log_derivative = self.zero();
            for (k, &e) in exponents.iter().enumerate().filter(|(_, e)| **e != 0) {
                let e = RatFun::from_rational(Rational::from(e));
                log_derivative = plus(&log_derivative, &scale(&self.deltas[k], &e));
            }
            let term = self.times_monomial(&log_derivative, &exponents);
            res = plus(&res, &scale(&term, c));
        }
        res
    }

    /// `f` as an element of the tower, `None` if it divides by a zero divisor.
    fn element(&self, f: &Expr, params: &mut Params) -> Option<Element> {
        self.element_split(&split_bases(f, self.w), params)
    }

    /// [`Tower::element`] for `f` whose bases are split by [`split_bases`].
    fn element_split(&self, f: &Expr, params: &mut Params) -> Option<Element> {
        if !has_radical(f, self.w) {
            let (num, den) = params.rational(f, self.w)?;
            return Some(self.constant(RatFun { num, den }));
        }
        match f {
            Term::Add(add) => add.iter().try_fold(self.zero(), |res, t| {
                Some(plus(&res, &self.element_split(t, params)?))
            }),
            Term::Mul(mul) => mul.iter().try_fold(
                self.constant(RatFun::from_rational(mul.coefficient.clone())),
                |res, t| Some(self.times(&res, &self.element_split(t, params)?)),
            ),
            Term::Pow(pow) => {
                let Term::Value(e) = &**pow.exponant else {
                    return None;
                };
                if let Ok(n) = i64::try_from(&e.value) {
                    let n = Some(n).filter(|n| n.abs() <= MAX_EXPONENT)?;
                    return self.pow(&self.element_split(&pow.base, params)?, n);
                }
                // `{$b^(p/r) = y^(p q/r)$}`
                let k = self.radicals.iter().position(|b| b == &*pow.base)?;
                let n = &e.value * Rational::from(self.orders[k]);
                let n = i64::try_from(&n).ok().filter(|n| n.abs() <= MAX_EXPONENT)?;
                let mut exponents = vec![0; self.orders.len()];
                exponents[k] = usize::try_from(n.unsigned_abs()).ok()?;
                let y = self.monomial(&exponents);
                if n < 0 { self.inverse(&y) } else { Some(y) }
            }
            Term::Value(_) | Term::Symbol(_) | Term::Fun(_) => None,
        }
    }
}

fn plus(a: &Element, b: &Element) -> Element {
    a.iter().zip(b).map(|(x, y)| x.plus(y)).collect()
}

fn scale(a: &Element, c: &RatFun) -> Element {
    a.iter().map(|x| x.times(c)).collect()
}

/// Whether `f` has a rational power with a non-integer exponent of a base depending on `w` or of a positive
/// rational.
fn has_radical(f: &Expr, w: Symbol) -> bool {
    match f {
        Term::Add(add) => add.iter().any(|t| has_radical(t, w)),
        Term::Mul(mul) => mul.iter().any(|t| has_radical(t, w)),
        Term::Pow(pow) => {
            has_radical(&pow.base, w)
                || (matches!(&**pow.exponant, Term::Value(e) if e.value.denominator_ref() != &1u32)
                    && (depends(&pow.base, w) || is_positive_value(&pow.base)))
        }
        Term::Value(_) | Term::Symbol(_) | Term::Fun(_) => false,
    }
}

/// Whether `b` is a positive rational, whose roots are generators of the tower (normalization writes constant
/// radicals with independent bases, so `{$sqrt(2)^2 = 2$}` is known there).
fn is_positive_value(b: &Expr) -> bool {
    matches!(b, Term::Value(c) if c.value > 0u32)
}

/// `f` with the bases of its radicals depending on `w` split into their factors over `{$QQ$}`, so that related bases
/// share their generators: `{$b = c product g_i^(e_i)$}` with `{$g_i(0) > 0$}` gives `{$b^r = c^r product g_i^(e_i r)$}`,
/// which holds near `{$w = 0^+$}` (`{$sqrt(2 + 2w) = sqrt(2) sqrt(1 + w)$}`, `{$sqrt(w^2 + 2w + 1) = 1 + w$}`). Bases
/// with radicals, vanishing at 0 or with a negative constant under an even root are kept.
fn split_bases(f: &Expr, w: Symbol) -> Expr {
    map_tree(f, &|t| {
        let Term::Pow(pow) = t else { return None };
        let Term::Value(e) = &**pow.exponant else {
            return None;
        };
        if e.value.denominator_ref() == &1u32 || !depends(&pow.base, w) || has_radical(&pow.base, w) {
            return None;
        }
        split_base(&pow.base, &e.value, w)
    })
}

/// `{$b^e$}` with the factors of `b` split, see [`split_bases`].
fn split_base(b: &Expr, e: &Rational, w: Symbol) -> Option<Expr> {
    let factored = b.factor();
    let factors: Vec<&Expr> = match &factored {
        Term::Mul(mul) => mul.iter().collect(),
        _ => vec![&factored],
    };
    let mut c = match &factored {
        Term::Mul(mul) => mul.coefficient.clone(),
        Term::Value(v) => v.value.clone(),
        _ => Rational::from(1),
    };
    let mut res = vec![];
    for factor in factors {
        let (g, m) = match factor {
            Term::Pow(pow) => match &**pow.exponant {
                Term::Value(m) => ((*pow.base).clone(), m.value.clone()),
                _ => return None,
            },
            Term::Value(_) => continue,
            _ => (factor.clone(), Rational::from(1)),
        };
        if !depends(&g, w) {
            return None;
        }
        let Term::Value(at_zero) = subs(&g, w, &zero()) else {
            return None;
        };
        if at_zero.value == 0u32 {
            return None;
        }
        let g = if at_zero.value < 0u32 {
            if m.denominator_ref() != &1u32 {
                return None;
            }
            if Integer::try_from(&m).ok()? % Integer::from(2) != 0 {
                c = -c;
            }
            -g
        } else {
            g
        };
        res.push((g, m));
    }
    if c < 0u32 {
        return None;
    }
    let mut out = value(c).pow(&value(e.clone()));
    for (g, m) in res {
        out = out * g.pow(&value(m * e));
    }
    (out != *b).then_some(out)
}

/// Collects the bases of the radicals of `f` depending on `w`, inner ones first, with the lcm of the
/// denominators of their exponents. `None` if `f` isn't algebraic in `w`.
fn collect(f: &Expr, w: Symbol, radicals: &mut Vec<Expr>, orders: &mut Vec<usize>) -> Option<()> {
    if !depends(f, w) && !has_radical(f, w) {
        return Some(());
    }
    match f {
        Term::Add(add) => add.iter().try_for_each(|t| collect(t, w, radicals, orders)),
        Term::Mul(mul) => mul.iter().try_for_each(|t| collect(t, w, radicals, orders)),
        Term::Pow(pow) => {
            let Term::Value(e) = &**pow.exponant else {
                return None;
            };
            if !depends(&pow.base, w) && !is_positive_value(&pow.base) {
                return Some(());
            }
            collect(&pow.base, w, radicals, orders)?;
            let q = usize::try_from(e.value.denominator_ref()).ok()?;
            if q != 1 {
                if let Some(k) = radicals.iter().position(|b| b == &*pow.base) {
                    orders[k] = lcm(orders[k], q);
                } else {
                    radicals.push((*pow.base).clone());
                    orders.push(q);
                }
            }
            Some(())
        }
        Term::Symbol(_) | Term::Value(_) => Some(()),
        Term::Fun(_) => None,
    }
}

const fn lcm(a: usize, b: usize) -> usize {
    let (mut x, mut y) = (a, b);
    while y != 0 {
        (x, y) = (y, x % y);
    }
    a / x * b
}

/// A differential operator annihilating the algebraic function `f` of `w`, whose radicals have bases which are
/// analytic and non-zero at `{$w = 0^+$}` (so that `f` has a Laurent series there). `None` if `f` isn't
/// algebraic, has no radical, or has no operator of order at most [`ore::MAX_ORDER`].
pub fn annihilator(f: &Expr, w: Symbol, params: &mut Params) -> Option<Operator> {
    let tower = Tower::new(f, w, params)?;
    if !tower.radicals.iter().all(|b| analytic_non_zero(b, w)) {
        return None;
    }
    let mut derivative = tower.element(f, params)?;
    ore::annihilator(Kind::Differential, tower.dim, |i| {
        if i > 0 {
            derivative = tower.derive(&derivative);
        }
        derivative.clone()
    })
}

/// Whether `e`, an algebraic function of `t`, is proven zero: it is zero in the tower of its radicals. `false`
/// when it isn't algebraic or isn't zero in the tower.
pub fn is_zero(e: &Expr, t: Symbol) -> bool {
    let mut params = Params::default();
    let split = split_bases(e, t);
    if !has_radical(&split, t) {
        // Its radicals were powers of factors of their bases
        return params
            .rational(&split, t)
            .is_some_and(|(num, den)| RatFun { num, den }.is_zero());
    }
    let e = &split;
    Tower::new(e, t, &mut params)
        .and_then(|tower| tower.element(e, &mut params))
        .is_some_and(|a| a.iter().all(RatFun::is_zero))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{field::real::R, parse, symbol};

    #[test]
    fn tower_arithmetic() {
        let w = symbol!("w");
        let mut params = Params::default();
        let f = parse!("sqrt(1 + w)", R);
        let tower = Tower::new(&f, w, &mut params).unwrap();
        let y = tower.element(&f, &mut params).unwrap();
        let b = tower.element(&parse!("1 + w", R), &mut params).unwrap();
        assert_eq!(tower.times(&y, &y), b);
        let one = tower.constant(RatFun::one());
        assert_eq!(tower.times(&y, &tower.inverse(&y).unwrap()), one);
    }

    #[test]
    fn zero_tests() {
        let t = symbol!("t");
        // `{$D sqrt(1 + sqrt(1 + t))$}` against its derivative written by hand, with
        // `{$1/(1 + sqrt(1 + t)) = (sqrt(1 + t) - 1)/t$}`
        let f = parse!("sqrt(1 + sqrt(1 + t))", R);
        let derivative = parse!(
            "sqrt(1 + sqrt(1 + t))*(sqrt(1 + t) - 1)/(4*t*sqrt(1 + t))",
            R
        );
        let e = f.derivative(t) - &derivative;
        assert!(!e.is_zero());
        assert!(is_zero(&e, t));
        assert!(is_zero(
            &parse!("sqrt(1 + sqrt(1 + t))^4 - 2*sqrt(1 + sqrt(1 + t))^2 - t", R),
            t
        ));
        assert!(!is_zero(&(f.derivative(t) - &derivative * &f), t));
        assert!(!is_zero(&(e + parse!("sqrt(1 + t) - 1", R)), t));
        assert!(!is_zero(&parse!("exp(t)*sqrt(1 + t)", R), t));
    }

    #[test]
    fn related_bases() {
        let t = symbol!("t");
        // Bases split into their factors share their generators, constant radicals are generators too
        assert!(is_zero(&parse!("sqrt(2 + 2*t) - sqrt(2)*sqrt(1 + t)", R), t));
        assert!(is_zero(&parse!("sqrt(t^2 + 2*t + 1) - t - 1", R), t));
        assert!(is_zero(&parse!("sqrt(1 - t)*sqrt(1 + t) - sqrt(1 - t^2)", R), t));
        assert!(is_zero(&parse!("(8 + 8*t)^(1/3) - 2*(1 + t)^(1/3)", R), t));
        assert!(is_zero(&parse!("sqrt(2)*sqrt(2 + 2*t) - 2*sqrt(1 + t)", R), t));
        // `{$sqrt((t - 1)^2) = 1 - t$}` near 0
        assert!(is_zero(&parse!("sqrt(t^2 - 2*t + 1) + t - 1", R), t));
        assert!(!is_zero(&parse!("sqrt(2 + 2*t) - sqrt(1 + t)", R), t));
        assert!(!is_zero(&parse!("sqrt(t^2 - 2*t + 1) - t + 1", R), t));
    }
}
