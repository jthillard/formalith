//! Polynomial systems, solved by splitting factored equations into cases, substituting unknowns and eliminating
//! them with resultants.
//!
//! The system is solved recursively, each branch holding the remaining equations `p = 0` (expanded) and the
//! unknowns assigned so far. At each step, the first strategy which applies is used:
//! 1. equations without unknowns are dropped if they are zero, and kill the branch otherwise,
//! 2. a product is split into one branch per factor (`x*y = 0` gives `x = 0` or `y = 0`),
//! 3. an unknown with a coefficient free of unknowns is substituted (`x + y^2 = 1` gives `x = 1 - y^2`),
//! 4. an equation in a single unknown gives one branch per root, found by [`PolynomialRoots`],
//! 5. an unknown is substituted when its coefficient contains other unknowns, `c` in `c*x + d = 0`, the case
//!    `c = 0, d = 0` being another branch,
//! 6. an unknown is eliminated from two equations with their resultant (`x^2 + y^2 = 5, x*y^2 = 4`),
//! 7. an equation of a single unknown, whose coefficients contain other unknowns, is solved by [`PolynomialRoots`],
//!    the case of a zero leading coefficient being another branch.
//!
//! Like linear systems, parameters are assumed to be generic: `a*x^2 = 1` gives `x = ±1/sqrt(a)`.

use std::{cmp::Ordering, collections::HashMap, fmt::Debug};

use malachite::{
    Integer, Natural, Rational,
    base::{
        num::{
            basic::traits::{One, Zero},
            conversion::traits::RoundingFrom,
        },
        rounding_modes::RoundingMode,
    },
};

use crate::{
    context::{Context, Symbol},
    field::{
        Group, Ring, TryElementFrom, TryExprFrom, complex::C, integer::Z, modular::Zn, real::R,
    },
    term::{Expand, Fun, Mul, Normalize, SymbolTerm, Term, TermSet},
};

use super::{Assignments, Solution, SolveError, plain};

/// Maximum depth of the recursion, which is reached by systems whose resultants keep growing.
const MAX_DEPTH: usize = 64;

/// Maximum modulus of `{$ZZ\/n ZZ$}` for which roots are found by trying every residue.
const MAX_RESIDUES: u64 = 1 << 16;

/// Maximum square root of the constant coefficient of a polynomial over `{$ZZ$}`, whose divisors are tried as roots.
const MAX_DIVISORS: Natural = Natural::const_from(1 << 20);

/// Maximum size of a Sylvester matrix, its determinant being computed in `{$O(n 2^n)$}` products.
const MAX_SYLVESTER_SIZE: usize = 12;

/// Solve the polynomial system `expression = 0` for each expanded expression, in `unknowns`.
///
/// # Errors
/// Returns an error if an expression isn't polynomial in the unknowns, or if a polynomial can't be solved.
pub(super) fn solve<T: Ring>(
    expressions: &[Term<T>],
    unknowns: &[Symbol],
) -> Result<Solution<T>, SolveError> {
    let branch = Branch {
        equations: expressions
            .iter()
            .map(|expression| Equation::new(expression.clone()))
            .collect(),
        unknowns: unknowns.to_vec(),
        assignments: vec![],
    };
    let mut solutions = vec![];
    branch.solve(0, &mut solutions)?;
    let solutions = solutions
        .into_iter()
        .map(|mut assignments| {
            // In the order of `unknowns`, with values simplified as the elimination nests fractions
            assignments.sort_by_key(|(unknown, _)| unknowns.iter().position(|u| u == unknown));
            assignments
                .into_iter()
                .map(|(unknown, value)| match value {
                    // Simplifying `1` in `Z` gives `1/1`
                    Term::Value(_) => (unknown, value),
                    value => (unknown, value.simplify()),
                })
                .collect()
        })
        .collect();
    Ok(Solution::from_branches(solutions))
}

/// Roots of polynomials in a set, and factorization of the equations. Implemented for every ring, with a default
/// which can't factor, nor find roots.
pub(crate) trait PolynomialRoots: Ring {
    /// Factor `term`, returning `None` if the set doesn't support factorization.
    fn factor_term(term: &Term<Self>) -> Option<Term<Self>>;

    /// The roots of the polynomial `sum(c_i x^i)`, given its coefficients `c_i` by increasing degree. The polynomial
    /// has a degree of at least one, and can't be factored by [`PolynomialRoots::factor_term`] when every
    /// coefficient is a value. Coefficients don't contain `x`, and their symbols are generic: the leading
    /// coefficient is assumed to be non-zero.
    ///
    /// Returns `None` if the roots can't be computed.
    fn roots(coefficients: &[Term<Self>]) -> Option<Vec<Term<Self>>>;
}

impl<T: Ring> PolynomialRoots for T {
    default fn factor_term(_: &Term<Self>) -> Option<Term<Self>> {
        None
    }

    default fn roots(_: &[Term<Self>]) -> Option<Vec<Term<Self>>> {
        None
    }
}

impl<T: Ring<ExponantSet: Ring, ProductCoefficientSet = T>> PolynomialRoots for T
where
    TermSet<T>: TryElementFrom<TermSet<T::ExponantSet>>,
    Term<T>: TryFrom<Term<T::ExponantSet>>,
    <Term<T> as TryFrom<Term<T::ExponantSet>>>::Error: Debug,
{
    default fn factor_term(term: &Term<Self>) -> Option<Term<Self>> {
        Some(term.factor())
    }

    /// The factorization of polynomials with value coefficients is complete, irreducible factors of degree two or
    /// more have no root in the set (like `{$x^2 + 1$}` over `{$QQ(i)$}`, or `{$x^2 - 3$}` over `{$ZZ\/7ZZ$}`), and
    /// neither do linear factors with a non-invertible coefficient (`{$2x - 1$}` over `{$ZZ$}`).
    default fn roots(coefficients: &[Term<Self>]) -> Option<Vec<Term<Self>>> {
        coefficients
            .iter()
            .all(|coefficient| matches!(coefficient, Term::Value(_)))
            .then(Vec::new)
    }
}

impl PolynomialRoots for R<Rational> {
    /// Polynomials of degree one or two, and polynomials of these degrees in `{$x^k$}`, like `{$x^4 - x^2 - 1$}`
    /// or `{$x^3 - 2$}`, are solved with radicals, as well as cubics with rational coefficients (see [`cubic_roots`]).
    /// Signs of radicals are found by approximating them. Roots of other polynomials aren't computed.
    fn roots(coefficients: &[Term<Self>]) -> Option<Vec<Term<Self>>> {
        let value = |value: i64| Term::constant(Rational::from(value), R);
        // A polynomial in `x^k`
        let k = (1..coefficients.len())
            .filter(|degree| !coefficients[*degree].is_zero())
            .fold(0, |k, degree| gcd(k, degree));
        if k > 1 {
            let coefficients: Vec<_> = coefficients.iter().step_by(k).cloned().collect();
            let roots = Self::roots(&coefficients)?;
            return Some(roots.iter().flat_map(|t| real_roots(t, k)).collect());
        }
        match coefficients {
            [c, b] => Some(vec![-c / b]),
            [c, b, a] => {
                let discriminant = (b * b - value(4) * a * c).expand();
                let (b, a) = (-b, value(2) * a);
                Some(match sign(&discriminant) {
                    Some(Ordering::Less) => vec![],
                    Some(Ordering::Equal) => vec![b / a],
                    _ => {
                        let root =
                            discriminant.pow(&Term::constant(Rational::from_signeds(1, 2), R));
                        vec![(&b - &root) / &a, (b + root) / a]
                    }
                })
            }
            [_, _, _, _] => cubic_roots(&values(coefficients)?),
            _ => None,
        }
    }
}

/// The real roots of the cubic `{$a x^3 + b x^2 + c x + d$}` with rational coefficients `[d, c, b, a]`. With
/// `{$x = t - b/(3 a)$}`, it becomes `{$t^3 + p t + q$}`, whose roots are given by Cardano's formula when
/// `{$Delta = (q/2)^2 + (p/3)^3 > 0$}` (one real root), the trigonometric form
/// `{$t_k = 2 sqrt(-p/3) cos(1/3 acos((3 q)/(2 p) sqrt(-3/p)) - (2 pi k)/3)$}` when `{$Delta < 0$}` (three real
/// roots), and `{$(3 q)/p$}`, `{$-(3 q)/(2 p)$}` when `{$Delta = 0$}`.
fn cubic_roots(coefficients: &[Rational]) -> Option<Vec<Term<R<Rational>>>> {
    let [d, c, b, a] = coefficients else {
        return None;
    };
    let value = |value: Rational| Term::constant(value, R);
    let ratio = |p: i64, q: i64| Rational::from_signeds(p, q);
    let p = (Rational::from(3) * a * c - b * b) / (Rational::from(3) * a * a);
    let q = (Rational::from(2) * b * b * b - Rational::from(9) * a * b * c
        + Rational::from(27) * a * a * d)
        / (Rational::from(27) * a * a * a);
    let shift = value(-(b / (Rational::from(3) * a)));
    let discriminant = (&q * &q) / Rational::from(4) + (&p * &p * &p) / Rational::from(27);
    let roots = match discriminant.cmp(&Rational::ZERO) {
        Ordering::Equal if p == 0 => vec![Term::zero(R)],
        Ordering::Equal => vec![
            value(Rational::from(3) * &q / &p),
            value(Rational::from(-3) * &q / (Rational::from(2) * &p)),
        ],
        Ordering::Greater => {
            let root = value(discriminant).pow(&value(ratio(1, 2)));
            let half = value(-&q / Rational::from(2));
            let (u, v) = (&half + &root, half - root);
            let cube_root = |t: &Term<R<Rational>>| real_roots(t, 3).pop();
            vec![cube_root(&u)? + cube_root(&v)?]
        }
        Ordering::Less => {
            let pi = Term::Symbol(SymbolTerm::new(Context::PI, R));
            let angle = Term::Fun(Box::new(Fun::new(
                Context::ACOS,
                vec![
                    value(Rational::from(3) * &q / (Rational::from(2) * &p))
                        * value(Rational::from(-3) / &p).pow(&value(ratio(1, 2))),
                ],
                R,
            )))
            .normalize()
                / value(Rational::from(3));
            let amplitude = value(Rational::from(2)) * value(-&p / Rational::from(3)).pow(&value(ratio(1, 2)));
            (0..3)
                .map(|k| {
                    let cos = Term::Fun(Box::new(Fun::new(
                        Context::COS,
                        vec![&angle - &(value(ratio(2 * k, 3)) * &pi)],
                        R,
                    )))
                    .normalize();
                    &amplitude * &cos
                })
                .collect()
        }
    };
    Some(roots.into_iter().map(|t| t + &shift).collect())
}

impl PolynomialRoots for C<R<Rational>> {
    /// Polynomials of degree one or two, and polynomials of these degrees in `{$x^k$}` with `{$k$}` a product of
    /// twos and threes, like `{$x^2 + 2$}` or `{$x^6 - 2$}`, are solved with radicals. Other polynomials aren't solved.
    fn roots(coefficients: &[Term<Self>]) -> Option<Vec<Term<Self>>> {
        // A polynomial in `x^k`
        let k = (1..coefficients.len())
            .filter(|degree| !coefficients[*degree].is_zero())
            .fold(0, |k, degree| gcd(k, degree));
        if k > 1 {
            let coefficients: Vec<_> = coefficients.iter().step_by(k).cloned().collect();
            let roots = Self::roots(&coefficients)?;
            return roots
                .iter()
                .map(|t| complex_roots(t, k))
                .collect::<Option<Vec<_>>>()
                .map(|roots| roots.into_iter().flatten().collect());
        }
        match coefficients {
            [c, b] => Some(vec![-c / b]),
            [c, b, a] => {
                let discriminant = (b * b - complex(4) * a * c).expand();
                let (b, a) = (-b, complex(2) * a);
                if discriminant.is_zero() {
                    return Some(vec![b / a]);
                }
                let root = complex_sqrt(&discriminant);
                Some(vec![(&b - &root) / &a, (b + root) / a])
            }
            _ => None,
        }
    }
}

impl PolynomialRoots for Zn {
    fn factor_term(term: &Term<Self>) -> Option<Term<Self>> {
        let set = term.get_set();
        set.factor(term)
    }

    /// Roots are searched among every residue when the modulus is small. Otherwise, irreducible polynomials have
    /// no root, when the modulus is prime.
    fn roots(coefficients: &[Term<Self>]) -> Option<Vec<Term<Self>>> {
        let set = coefficients[0].get_set();
        let coefficients = values(coefficients)?;
        if set.modulus() > MAX_RESIDUES {
            return set.is_field().then(Vec::new);
        }
        let evaluate = |x: u64| {
            coefficients
                .iter()
                .rev()
                .fold(0, |res, c| set.add(&set.mul(&res, &x), c))
        };
        Some(
            (0..set.modulus())
                .filter(|x| evaluate(*x) == 0)
                .map(|x| Term::constant(x, set))
                .collect(),
        )
    }
}

impl PolynomialRoots for Z<Integer> {
    // Factoring isn't supported in `Z`
    fn factor_term(_: &Term<Self>) -> Option<Term<Self>> {
        None
    }

    /// Integer roots divide the constant coefficient, once the roots `0` are removed.
    fn roots(coefficients: &[Term<Self>]) -> Option<Vec<Term<Self>>> {
        let mut coefficients = values(coefficients)?;
        let mut roots = vec![];
        if coefficients[0] == 0 {
            roots.push(Integer::ZERO);
            let zeros = coefficients.iter().take_while(|c| **c == 0).count();
            coefficients.drain(..zeros);
        }
        let evaluate = |x: &Integer| {
            coefficients
                .iter()
                .rev()
                .fold(Integer::ZERO, |res, c| res * x + c)
        };
        let constant = coefficients[0].unsigned_abs_ref().clone();
        if constant > MAX_DIVISORS * MAX_DIVISORS {
            return None;
        }
        let mut divisor = Natural::ONE;
        while &divisor * &divisor <= constant {
            if (&constant % &divisor) == 0 {
                for d in [divisor.clone(), &constant / &divisor] {
                    for root in [Integer::from(d.clone()), -Integer::from(d)] {
                        if !roots.contains(&root) && evaluate(&root) == 0 {
                            roots.push(root);
                        }
                    }
                }
            }
            divisor += Natural::ONE;
        }
        Some(
            roots
                .into_iter()
                .map(|root| Term::constant(root, Z))
                .collect(),
        )
    }
}

/// The elements of `coefficients`, if they are all values.
pub(super) fn values<T: Ring>(coefficients: &[Term<T>]) -> Option<Vec<T::Element>> {
    coefficients
        .iter()
        .map(|coefficient| match coefficient {
            Term::Value(value) => Some(value.value.clone()),
            _ => None,
        })
        .collect()
}

/// The real solutions of `{$x^k = t$}`.
fn real_roots(t: &Term<R<Rational>>, k: usize) -> Vec<Term<R<Rational>>> {
    let root =
        |t: &Term<R<Rational>>| t.pow(&Term::constant(Rational::from_unsigneds(1u64, k as u64), R));
    let even = k % 2 == 0;
    match sign(t) {
        Some(Ordering::Equal) => vec![Term::zero(R)],
        Some(Ordering::Less) if even => vec![],
        // Don't take a root of a negative number
        Some(Ordering::Less) => vec![-root(&-t)],
        _ if even => {
            let root = root(t);
            vec![-&root, root]
        }
        _ => vec![root(t)],
    }
}

/// The integer `value` in `{$CC$}`.
fn complex(value: i64) -> Term<C<R<Rational>>> {
    Term::constant([Rational::from(value), Rational::ZERO], C)
}

/// The solutions of `{$x^k = t$}` in `{$CC$}`, if `{$k$}` is a product of twos and threes.
fn complex_roots(t: &Term<C<R<Rational>>>, k: usize) -> Option<Vec<Term<C<R<Rational>>>>> {
    if k == 1 {
        return Some(vec![t.clone()]);
    }
    if t.is_zero() {
        return Some(vec![Term::zero(C)]);
    }
    // Cube roots last, so that they are taken on real values when possible (`{$x^6 = 2$}`)
    if k % 3 == 0 {
        // The primitive cube roots of unity `{$(-1 plus.minus i sqrt(3)) / 2$}`
        let i_sqrt_3 = complex(-3).pow(&Term::constant(
            [Rational::from_signeds(1, 2), Rational::ZERO],
            C,
        ));
        let omega = [
            (complex(-1) + &i_sqrt_3) / complex(2),
            (complex(-1) - i_sqrt_3) / complex(2),
        ];
        return Some(
            complex_roots(t, k / 3)?
                .iter()
                .flat_map(|t| {
                    let root = complex_cbrt(t);
                    let others = omega.clone().map(|omega| (&root * &omega).expand());
                    std::iter::once(root).chain(others)
                })
                .collect(),
        );
    }
    if k % 2 == 0 {
        return Some(
            complex_roots(t, k / 2)?
                .iter()
                .flat_map(|t| {
                    let root = complex_sqrt(t);
                    [-&root, root]
                })
                .collect(),
        );
    }
    None
}

/// A square root of `t` in `{$CC$}`. For a non-real value `{$a + b i$}`, it is
/// `{$sqrt((|z| + a) / 2) + "sgn"(b) i sqrt((|z| - a) / 2)$}`.
fn complex_sqrt(t: &Term<C<R<Rational>>>) -> Term<C<R<Rational>>> {
    let half = Term::constant([Rational::from_signeds(1, 2), Rational::ZERO], C);
    if let Term::Value(value) = t
        && let [a, b] = &value.value
        && *b != 0
    {
        let modulus = Term::constant([a * a + b * b, Rational::ZERO], C).pow(&half);
        let a = Term::constant([a.clone(), Rational::ZERO], C);
        let re = ((&modulus + &a) / complex(2)).pow(&half);
        let im = ((modulus - a) / complex(2)).pow(&half);
        let i = Term::constant(if *b > 0 { C.i() } else { C.conj(&C.i()) }, C);
        return re + i * im;
    }
    // `{$sqrt(v r) = sqrt(v) sqrt(r)$}` for a non-real coefficient `{$v$}` and a positive real `{$r$}`
    if let Term::Mul(mul) = t
        && mul.coefficient[1] != 0
    {
        let coefficient = Term::constant(mul.coefficient.clone(), C);
        let rest = t / &coefficient;
        if real_sign(&rest) == Some(Ordering::Greater) {
            return complex_sqrt(&coefficient) * rest.pow(&half);
        }
    }
    // `{$a + b i$}` with radicals `a` and `b`, like `{$(1 + i sqrt(3)) / 2$}`
    if let Some((a, b)) = split_complex(t)
        && let Some(b_sign @ (Ordering::Less | Ordering::Greater)) = real_sign(&b)
    {
        let modulus = (&a * &a + &b * &b).expand().pow(&half);
        let re = ((&modulus + &a) / complex(2)).pow(&half);
        let im = ((modulus - a) / complex(2)).pow(&half);
        let i = Term::constant(
            if b_sign == Ordering::Greater {
                C.i()
            } else {
                C.conj(&C.i())
            },
            C,
        );
        return re + i * im;
    }
    // Real values are handled by the normalization, `{$sqrt(-3) = i sqrt(3)$}`
    match real_sign(t) {
        Some(Ordering::Less) => Term::constant(C.i(), C) * (-t).pow(&half),
        _ => t.pow(&half),
    }
}

/// The real and imaginary parts `{$(a, b)$}` of `{$t = a + b i$}`, if every term of the expanded `t` is a complex
/// coefficient times a real expression (its symbols and radicals being assumed real).
pub(crate) fn split_complex(
    t: &Term<C<R<Rational>>>,
) -> Option<(Term<C<R<Rational>>>, Term<C<R<Rational>>>)> {
    let t = t.expand();
    let terms = match &t {
        Term::Add(add) => add.iter().cloned().collect(),
        _ => vec![t.clone()],
    };
    let (mut re, mut im) = (Term::zero(C), Term::zero(C));
    for term in terms {
        let (coefficient, rest) = match &term {
            Term::Value(value) => (value.value.clone(), Term::one(C)),
            Term::Mul(mul) => (
                mul.coefficient.clone(),
                &term / &Term::constant(mul.coefficient.clone(), C),
            ),
            _ => ([Rational::ONE, Rational::ZERO], term.clone()),
        };
        // The rest must be real
        TryExprFrom::<C<R<Rational>>>::try_from_expr(&R, rest.clone()).ok()?;
        let [a, b] = coefficient;
        re += Term::constant([a, Rational::ZERO], C) * &rest;
        im += Term::constant([b, Rational::ZERO], C) * rest;
    }
    Some((re, im))
}

/// A cube root of `t` in `{$CC$}`, real when `t` is real.
fn complex_cbrt(t: &Term<C<R<Rational>>>) -> Term<C<R<Rational>>> {
    let third = Term::constant([Rational::from_signeds(1, 3), Rational::ZERO], C);
    match real_sign(t) {
        Some(Ordering::Less) => -(-t).pow(&third),
        _ => t.pow(&third),
    }
}

/// The sign of `t`, if it is real and can be approximated.
fn real_sign(t: &Term<C<R<Rational>>>) -> Option<Ordering> {
    sign(&TryExprFrom::<C<R<Rational>>>::try_from_expr(&R, t.clone()).ok()?)
}

/// The sign of `term`, if it is zero or can be approximated. Symbols are generic, their sign is unknown.
fn sign(term: &Term<R<Rational>>) -> Option<Ordering> {
    if term.is_zero() {
        return Some(Ordering::Equal);
    }
    // Too close to zero to trust the approximation
    approximate(term)
        .filter(|value| value.abs() > 1e-9)
        .and_then(|value| value.partial_cmp(&0.))
}

/// Approximate `term` with a float, if it doesn't contain any symbol or function.
fn approximate(term: &Term<R<Rational>>) -> Option<f64> {
    let rational = |value: &Rational| f64::rounding_from(value, RoundingMode::Nearest).0;
    let res = match term {
        Term::Value(value) => rational(&value.value),
        Term::Add(add) => add.iter().map(approximate).sum::<Option<f64>>()?,
        Term::Mul(mul) => {
            rational(&mul.coefficient) * mul.iter().map(approximate).product::<Option<f64>>()?
        }
        Term::Pow(pow) => approximate(&pow.base)?.powf(approximate(&pow.exponant)?),
        Term::Symbol(_) | Term::Fun(_) => return None,
    };
    // Even roots of negative numbers
    res.is_finite().then_some(res)
}

/// The greatest common divisor of `a` and `b`.
const fn gcd(a: usize, b: usize) -> usize {
    if b == 0 { a } else { gcd(b, a % b) }
}

/// An expanded equation `term = 0`.
#[derive(Clone)]
struct Equation<T: Ring> {
    term: Term<T>,
    /// The equation was factored and can't be split anymore.
    factored: bool,
}

impl<T: Ring> Equation<T> {
    const fn new(term: Term<T>) -> Self {
        Self {
            term,
            factored: false,
        }
    }
}

/// A case of the system, with remaining equations.
#[derive(Clone)]
struct Branch<T: Ring> {
    equations: Vec<Equation<T>>,
    /// The unknowns not assigned yet.
    unknowns: Vec<Symbol>,
    /// Assigned unknowns, in terms of the remaining unknowns.
    assignments: Assignments<T>,
}

impl<T: Ring> Branch<T> {
    /// Check if `term` contains a remaining unknown.
    fn has_unknown(&self, term: &Term<T>) -> bool {
        term.symbols()
            .iter()
            .any(|symbol| self.unknowns.contains(symbol))
    }

    /// The remaining unknowns of `term`.
    fn unknowns_of(&self, term: &Term<T>) -> Vec<Symbol> {
        let symbols = term.symbols();
        self.unknowns
            .iter()
            .filter(|unknown| symbols.contains(unknown))
            .copied()
            .collect()
    }

    /// Add the solutions of the branch to `solutions`.
    fn solve(
        mut self,
        depth: usize,
        solutions: &mut Vec<Assignments<T>>,
    ) -> Result<(), SolveError> {
        if depth > MAX_DEPTH {
            return Err(SolveError::Unsolvable(plain(&self.equations[0].term)));
        }
        if !self.clean_up() {
            return Ok(());
        }
        if self.equations.is_empty() {
            solutions.push(self.assignments);
            return Ok(());
        }
        let branches = if let Some(branches) = self.split_product() {
            branches
        } else if let Some(branches) = self.substitute_linear(false)? {
            branches
        } else if let Some(branches) = self.univariate()? {
            branches
        } else if let Some(branches) = self.substitute_linear(true)? {
            branches
        } else if let Some(branches) = self.resultant()? {
            branches
        } else {
            self.multivariate()?
        };
        for branch in branches {
            branch.solve(depth + 1, solutions)?;
        }
        Ok(())
    }

    /// Remove equations which are zero, or repeated. Returns `false` if an equation without unknowns isn't zero,
    /// so that the branch has no solution.
    fn clean_up(&mut self) -> bool {
        let mut equations: Vec<Equation<T>> = vec![];
        for equation in std::mem::take(&mut self.equations) {
            if !self.has_unknown(&equation.term) {
                // Radicals may need a simplification to cancel
                if equation.term.is_zero() || equation.term.simplify().is_zero() {
                    continue;
                }
                return false;
            }
            if equations.iter().all(|e| e.term != equation.term) {
                equations.push(equation);
            }
        }
        self.equations = equations;
        true
    }

    /// Factor the equations which aren't factored yet. The first one which is a product gives a branch for each
    /// factor containing unknowns.
    fn split_product(&mut self) -> Option<Vec<Self>> {
        for index in 0..self.equations.len() {
            if self.equations[index].factored {
                continue;
            }
            let factors = self.factors(&self.equations[index].term);
            if factors.len() > 1 {
                return Some(
                    factors
                        .into_iter()
                        .map(|factor| {
                            let mut branch = self.clone();
                            branch.equations[index] = Equation {
                                term: factor.expand(),
                                factored: true,
                            };
                            branch
                        })
                        .collect(),
                );
            }
            // The factor is still preferred, it drops constants like `2` in `2*x^2 - 2`
            let equation = &mut self.equations[index];
            if let Some(factor) = factors.into_iter().next() {
                equation.term = factor.expand();
            }
            equation.factored = true;
        }
        None
    }

    /// The distinct factors of `term` containing unknowns, or no factor if the set can't factor.
    fn factors(&self, term: &Term<T>) -> Vec<Term<T>> {
        let Some(factored) = T::factor_term(term) else {
            return vec![];
        };
        let all = match factored {
            Term::Mul(mul) => mul.factors,
            factor => vec![factor],
        };
        let mut factors = vec![];
        for factor in all {
            // `f^k = 0` iff `f = 0`
            let factor = match factor {
                Term::Pow(pow) if pow.exponant.to_i64().is_some_and(|k| k > 0) => {
                    (*pow.base).clone()
                }
                factor => factor,
            };
            if self.has_unknown(&factor) && !factors.contains(&factor) {
                factors.push(factor);
            }
        }
        factors
    }

    /// Find an equation `c*x + d = 0` and substitute `x = -d/c`. When `symbolic` isn't set, `c` must not contain
    /// unknowns, and must be invertible if it is a value. Otherwise, `c` contains unknowns, and another branch is
    /// the case `c = 0, d = 0`.
    fn substitute_linear(&self, symbolic: bool) -> Result<Option<Vec<Self>>, SolveError> {
        // Prefer values, which don't need any assumption
        let mut best: Option<(u8, usize, Symbol, Term<T>, Term<T>)> = None;
        for (index, equation) in self.equations.iter().enumerate() {
            for &x in &self.unknowns_of(&equation.term) {
                let coefficients = polynomial_form(&equation.term, x)?;
                let [d, c] = coefficients.as_slice() else {
                    continue;
                };
                let rank = match c {
                    Term::Value(value) if value.set.try_inv(&value.value).is_some() => 0,
                    Term::Value(_) => continue,
                    c if self.has_unknown(c) != symbolic => continue,
                    _ => 1,
                };
                if best.as_ref().is_none_or(|(r, ..)| rank < *r) {
                    best = Some((rank, index, x, c.clone(), d.clone()));
                }
            }
        }
        let Some((_, index, x, c, d)) = best else {
            return Ok(None);
        };
        let mut branch = self.clone();
        branch.equations.remove(index);
        let mut branches = vec![];
        if symbolic {
            let mut zero = branch.clone();
            zero.equations.push(Equation::new(c.clone()));
            zero.equations.push(Equation::new(d.clone()));
            branches.push(zero);
        }
        branches.push(branch.assign(x, &(-d / c))?);
        Ok(Some(branches))
    }

    /// Find an equation of a single unknown, with a branch for each root.
    fn univariate(&self) -> Result<Option<Vec<Self>>, SolveError> {
        for (index, equation) in self.equations.iter().enumerate() {
            let [x] = self.unknowns_of(&equation.term)[..] else {
                continue;
            };
            let coefficients = polynomial_form(&equation.term, x)?;
            let roots = T::roots(&coefficients)
                .ok_or_else(|| SolveError::Unsolvable(plain(&equation.term)))?;
            let mut branch = self.clone();
            branch.equations.remove(index);
            return roots
                .iter()
                .map(|root| branch.clone().assign(x, root))
                .collect::<Result<_, _>>()
                .map(Some);
        }
        Ok(None)
    }

    /// Eliminate an unknown `y` from two equations `p` and `q`, adding their resultant, a polynomial without `y`.
    /// `p` and `q` are kept, they are solved for `y` once the other unknowns are known.
    fn resultant(&self) -> Result<Option<Vec<Self>>, SolveError> {
        // Candidates `(size of the Sylvester matrix, p, q, y)`, the smallest first
        let mut candidates = vec![];
        for (i, p) in self.equations.iter().enumerate() {
            for (j, q) in self.equations.iter().enumerate().skip(i + 1) {
                let q_unknowns = self.unknowns_of(&q.term);
                for y in self.unknowns_of(&p.term) {
                    if !q_unknowns.contains(&y) {
                        continue;
                    }
                    let p_form = polynomial_form(&p.term, y)?;
                    let q_form = polynomial_form(&q.term, y)?;
                    candidates.push((p_form.len() + q_form.len() - 2, j, p_form, q_form));
                }
            }
        }
        candidates.sort_by_key(|(size, ..)| *size);
        for (size, j, p, q) in candidates {
            if size > MAX_SYLVESTER_SIZE {
                break;
            }
            let resultant = sylvester_determinant(&p, &q).expand();
            let resultant = resultant.as_fraction(true).0.expand();
            // `p` and `q` have a common factor. When they are irreducible, `q` is a multiple of `p`
            if resultant.is_zero() {
                let q = &self.equations[j];
                if !(q.factored && T::factor_term(&q.term).is_some()) {
                    return Err(SolveError::Unsolvable(plain(&q.term)));
                }
                let mut branch = self.clone();
                branch.equations.remove(j);
                return Ok(Some(vec![branch]));
            }
            if self.equations.iter().any(|e| e.term == resultant) {
                continue;
            }
            let mut branch = self.clone();
            branch.equations.push(Equation::new(resultant));
            return Ok(Some(vec![branch]));
        }
        Ok(None)
    }

    /// Solve an equation for an unknown whose coefficients contain other unknowns, like `x^2 + y^2 = 1` for `x`.
    /// Another branch is the case of a zero leading coefficient.
    fn multivariate(&self) -> Result<Vec<Self>, SolveError> {
        for (index, equation) in self.equations.iter().enumerate() {
            for x in self.unknowns_of(&equation.term) {
                let coefficients = polynomial_form(&equation.term, x)?;
                let Some(roots) = T::roots(&coefficients) else {
                    continue;
                };
                let mut branch = self.clone();
                branch.equations.remove(index);
                let mut branches = vec![];
                let leading = coefficients.last().expect("x appears in the equation");
                if self.has_unknown(leading) {
                    let mut zero = branch.clone();
                    let degree = coefficients.len() - 1;
                    let rest = coefficients[..degree]
                        .iter()
                        .enumerate()
                        .fold(Term::zero(leading.get_set()), |res, (i, c)| {
                            res + c * &power(x, i, leading.get_set())
                        });
                    zero.equations.push(Equation::new(leading.clone()));
                    zero.equations.push(Equation::new(rest.expand()));
                    branches.push(zero);
                }
                for root in &roots {
                    branches.push(branch.clone().assign(x, root)?);
                }
                return Ok(branches);
            }
        }
        Err(SolveError::Unsolvable(plain(&self.equations[0].term)))
    }

    /// Assign `x = value` in the branch, `value` not containing `x`.
    fn assign(mut self, x: Symbol, value: &Term<T>) -> Result<Self, SolveError> {
        let substitute = |term: &Term<T>| {
            term.substitute(x, value)
                .ok_or_else(|| SolveError::NotPolynomial(plain(term)))
        };
        for equation in &mut self.equations {
            if !equation.term.symbols().contains(&x) {
                continue;
            }
            // The denominator is assumed to be non-zero
            let term = substitute(&equation.term)?.expand();
            *equation = Equation::new(term.as_fraction(true).0.expand());
        }
        for (_, assigned) in &mut self.assignments {
            *assigned = substitute(assigned)?;
        }
        self.unknowns.retain(|unknown| *unknown != x);
        self.assignments.push((x, value.clone()));
        Ok(self)
    }
}

/// `x^n`, as a term of `set`.
fn power<T: Ring>(x: Symbol, n: usize, set: T) -> Term<T> {
    let x = Term::Symbol(crate::term::SymbolTerm::new(x, set));
    (0..n).fold(Term::one(set), |res, _| res * &x)
}

/// Split an expanded expression into its coefficients `c_i` by increasing degree, so that it is `sum(c_i x^i)`.
/// Coefficients don't contain `x`, the last one isn't zero (unless the expression is zero).
///
/// # Errors
/// Returns an error if the expression isn't polynomial in `x`, like `abs(x)` or `x^(1/2)`.
pub(super) fn polynomial_form<T: Ring>(
    expression: &Term<T>,
    x: Symbol,
) -> Result<Vec<Term<T>>, SolveError> {
    let set = expression.get_set();
    let has_x = |term: &Term<T>| term.symbols().contains(&x);
    // The degree of a factor `x` or `x^k`
    let degree = |factor: &Term<T>| match factor {
        Term::Symbol(symbol) if symbol.symbol == x => Some(1),
        Term::Pow(pow) if matches!(&*pow.base, Term::Symbol(symbol) if symbol.symbol == x) => pow
            .exponant
            .to_i64()
            .and_then(|k| usize::try_from(k).ok())
            .filter(|k| *k > 0),
        _ => None,
    };
    let not_polynomial = |term: &Term<T>| SolveError::NotPolynomial(plain(term));
    let terms = match expression {
        Term::Add(add) => add.terms.as_slice(),
        term => std::slice::from_ref(term),
    };
    let mut coefficients = vec![Term::zero(set)];
    for term in terms {
        let (degree, coefficient) = if !has_x(term) {
            (0, term.clone())
        } else if let Some(degree) = degree(term) {
            (degree, Term::one(set))
        } else if let Term::Mul(mul) = term {
            // `c * f_1 * ... * x^k * ... * f_n`, where only `x^k` contains `x`
            let mut total = 0;
            let mut others = vec![];
            for factor in mul.iter() {
                if !has_x(factor) {
                    others.push(factor.clone());
                    continue;
                }
                total += degree(factor).ok_or_else(|| not_polynomial(term))?;
            }
            let coefficient = Term::Mul(Mul::new(mul.coefficient.clone(), others, set));
            (total, coefficient.normalize())
        } else {
            return Err(not_polynomial(term));
        };
        if coefficients.len() <= degree {
            coefficients.resize(degree + 1, Term::zero(set));
        }
        coefficients[degree] += coefficient;
    }
    while coefficients.len() > 1 && coefficients.last().is_some_and(Term::is_zero) {
        coefficients.pop();
    }
    Ok(coefficients)
}

/// The determinant of the Sylvester matrix of `p` and `q`, given their coefficients by increasing degree, which is
/// their resultant.
///
/// It is computed by expanding along rows, with the minors memoized by the set of used columns, so that it doesn't
/// need divisions.
fn sylvester_determinant<T: Ring>(p: &[Term<T>], q: &[Term<T>]) -> Term<T> {
    let set = p[0].get_set();
    let (m, n) = (p.len() - 1, q.len() - 1);
    let size = m + n;
    // `n` rows of `p` coefficients, then `m` rows of `q` coefficients, by decreasing degree
    let entry = |row: usize, column: usize| -> Option<&Term<T>> {
        let (coefficients, shift) = if row < n { (p, row) } else { (q, row - n) };
        let degree = coefficients.len() - 1;
        column
            .checked_sub(shift)
            .filter(|k| *k <= degree)
            .map(|k| &coefficients[degree - k])
            .filter(|c| !c.is_zero())
    };
    let mut minors: HashMap<usize, Term<T>> = HashMap::new();
    minors.insert((1 << size) - 1, Term::one(set));
    // Masks of used columns, by decreasing number of used columns
    let mut masks: Vec<usize> = (0..1 << size).collect();
    masks.sort_by_key(|mask: &usize| std::cmp::Reverse(mask.count_ones()));
    for mask in masks {
        let row = mask.count_ones() as usize;
        if row == size {
            continue;
        }
        let mut minor = Term::zero(set);
        let mut free = 0;
        for column in 0..size {
            if mask & (1 << column) != 0 {
                continue;
            }
            if let (Some(value), Some(sub)) =
                (entry(row, column), minors.get(&(mask | 1 << column)))
            {
                let product = (value * sub).expand();
                minor = if free % 2 == 0 {
                    minor + product
                } else {
                    minor - product
                };
            }
            free += 1;
        }
        if !minor.is_zero() {
            minors.insert(mask, minor);
        }
    }
    minors.remove(&0).unwrap_or_else(|| Term::zero(set))
}
