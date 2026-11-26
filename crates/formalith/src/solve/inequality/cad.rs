//! Cylindrical algebraic decomposition, solving polynomial inequalities in the unknowns `{$x_1, ..., x_n$}`.
//!
//! 1. The numerators and denominators of the relations are factored into irreducible polynomials, each one
//!    belonging to the level of its last unknown.
//! 2. Projection: the polynomials of the last level give polynomials of the lower levels whose roots are the
//!    points where the roots in the last unknown appear, disappear or cross (coefficients, discriminants and
//!    resultants, `McCallum`'s projection), down to polynomials in `{$x_1$}`.
//! 3. Lifting: the real roots of the polynomials in `{$x_1$}` split the line into points (sections) and open
//!    intervals (sectors). Over a sample point of each one, the roots in `{$x_2$}` of the polynomials of the second
//!    level split the line again, and so on. On each cell the polynomials have a constant sign, found at the
//!    sample point: zero for the polynomials whose root defines the cell, from an approximation for the others.
//! 4. The bounds of a cell are the roots as expressions of the previous unknowns (found by
//!    [`Solve::solve_for`], matched with the roots at the sample point), and neighboring cells with the same
//!    description are merged, so `{$x^2 + y^2 <= 1$}` gives the single cell
//!    `{$x in [-1, 1], y in [-sqrt(1 - x^2), sqrt(1 - x^2)]$}`.

use std::{cmp::Ordering, collections::BTreeSet};

use malachite::{
    Natural, Rational,
    base::num::{
        arithmetic::traits::{Abs, Ceiling, Floor, Pow, Reciprocal},
        basic::traits::{One, Zero},
    },
};

use crate::{
    context::{
        Symbol,
        assumptions::{
            Assumptions, SignSet,
            linear::{LinearForm, Var},
        },
    },
    field::real::{
        R,
        approx::{approximate, approximate_fixed},
        expr::{Expr, depends, subs, value, variable, zero},
        rootof,
        sign::linear_expr,
    },
    integrate::poly::Poly,
    solve::{
        Equation, Solution, Solve, SolveError, plain,
        polynomial::{MAX_SYLVESTER_SIZE, polynomial_form, sylvester_determinant},
    },
    term::{Expand, Normalize, Term, relation::Relation},
};

use super::{DIGITS, Inequality, Interval};

/// Maximum number of unknowns related by the relations.
const MAX_UNKNOWNS: usize = 3;

/// Maximum number of polynomials of the decomposition.
const MAX_FACTORS: usize = 40;

/// Bits of the approximations of bounds compared by [`close`], accurate to about `{$2^(-116) < 10^(-34)$}`.
const SAME_BOUND_BITS: u64 = 116;

/// Whether the approximations `a` and `b` are the same point.
fn close(a: &Rational, b: &Rational) -> bool {
    let difference = (a - b).abs();
    let scale = a.clone().abs() + Rational::ONE;
    difference * Rational::from(10u32).pow(30u64) <= scale
}

/// The product of two signs.
fn mul(a: Ordering, b: Ordering) -> Ordering {
    match (a, b) {
        (Ordering::Equal, _) | (_, Ordering::Equal) => Ordering::Equal,
        (a, b) if a == b => Ordering::Greater,
        _ => Ordering::Less,
    }
}

/// A real root, with its approximation.
#[derive(Clone, Debug)]
struct Root {
    value: Expr,
    approximation: Rational,
}

/// The values of the unknown in a solution of a single equation.
fn values(solution: Solution<R<Rational>>) -> Vec<Expr> {
    match solution {
        Solution::NoSolution => vec![],
        Solution::Assignments(assignments) => {
            assignments.into_iter().map(|(_, value)| value).collect()
        }
        Solution::Alternatives(branches) => branches
            .into_iter()
            .filter_map(|assignments| assignments.into_iter().next().map(|(_, value)| value))
            .collect(),
    }
}

/// Bound on the numerator and denominator of the rationals recognized by [`rational_value`].
const MAX_RECOGNIZED: u64 = 1_000_000_000_000;

/// The rational equal to the constant `c`, which isn't a value, when its approximation is one with a small
/// numerator and denominator.
///
/// Over a section, the coefficients are expressions of roots of the projection, which may be rationals without
/// simplifying to them, like `{$x_0^3 - 3 x_0 + 1 = 0$}` for a root `{$x_0 = 2 cos(2 pi / 9)$}`, or a constant
/// written with nested radicals equal to 1600 at a root of a discriminant. `solve_for` doesn't finish on polynomials
/// with such coefficients, and the square roots of a vanishing value approximated as slightly negative would be
/// wrong. A coefficient is a rational when its approximation at [`DIGITS`] digits is within a relative
/// `{$10^(-35)$}` of one with numerator and denominator below `{$10^12$}` (0 when it is zero at the maximum
/// precision), which an irrational number would only be by chance.
fn rational_value(c: &Expr) -> Option<Rational> {
    let approximation = approximate(c, DIGITS)?;
    if approximation == 0 {
        return Some(approximation);
    }
    let margin = (&approximation).abs() / Rational::from(10u32).pow(35u64);
    let rational = simplest(&(&approximation - &margin), &(&approximation + margin));
    let bound = Natural::from(MAX_RECOGNIZED);
    (*rational.numerator_ref() <= bound && *rational.denominator_ref() <= bound).then_some(rational)
}

/// The polynomial `p` in `x` with its coefficients equal to rationals replaced by them, see [`rational_value`].
fn with_rational_coefficients(p: &Expr, x: Symbol) -> Result<Expr, SolveError> {
    let form = polynomial_form(p, x)?;
    if form.iter().all(|c| matches!(c, Term::Value(_))) {
        return Ok(p.clone());
    }
    Ok(form
        .into_iter()
        .enumerate()
        .fold(zero(), |res, (degree, c)| {
            let c = match c {
                Term::Value(_) => c,
                _ => rational_value(&c).map_or(c, value),
            };
            res + c * variable(x).pow(&value(Rational::from(degree)))
        })
        .expand())
}

/// The real roots of the polynomial `p` in `x`, whose coefficients are constants, approximated.
fn real_roots(p: &Expr, x: Symbol) -> Result<Vec<Root>, SolveError> {
    if !depends(p, x) {
        return Ok(vec![]);
    }
    let solution = R.solve_for(&[Equation::new(p.clone(), zero())], &[x])?;
    approximated(values(solution))
}

/// The rationals of the coefficients `coefficients`, when they are all values.
fn values_of(coefficients: &[Expr]) -> Option<Vec<Rational>> {
    coefficients
        .iter()
        .map(|c| match c {
            Term::Value(value) => Some(value.value.clone()),
            _ => None,
        })
        .collect()
}

/// The roots `values`, approximated.
fn approximated(values: Vec<Expr>) -> Result<Vec<Root>, SolveError> {
    values
        .into_iter()
        .map(|value| {
            let approximation = approximate(&value, DIGITS).ok_or_else(|| {
                SolveError::Inequality(format!("can't approximate `{}`", plain(&value)))
            })?;
            Ok(Root {
                value,
                approximation,
            })
        })
        .collect()
}

/// The simplest rational in the open interval `(lo, hi)`, with the smallest denominator, or `lo` when the interval
/// is empty.
fn simplest(lo: &Rational, hi: &Rational) -> Rational {
    if lo >= hi {
        return lo.clone();
    }
    if *lo < 0 && *hi > 0 {
        return Rational::ZERO;
    }
    if *hi <= 0 {
        return -simplest(&-hi, &-lo);
    }
    let floor = Rational::from(lo.clone().floor());
    let next = &floor + Rational::ONE;
    if next < *hi {
        return next;
    }
    // `{$lo - "floor" < t < hi - "floor" <= 1$}`, and `{$1 / t$}` is the simplest rational above `{$1/(hi - "floor")$}`
    let (a, b) = (hi - &floor, lo - &floor);
    let above = (&a).reciprocal();
    let u = if b == 0 {
        Rational::from(above.floor()) + Rational::ONE
    } else {
        simplest(&above, &(&b).reciprocal())
    };
    floor + u.reciprocal()
}

/// The simplest rational between the bounds `lo` and `hi`, `None` at infinity.
///
/// The bounds are approximations of roots, maybe on the wrong side of them (`{$-4/3$}` is approximated by
/// `{$-1.333...3 > -4/3$}`), so the interval is first shrunk by more than their error, else the root itself may be
/// the simplest rational of the interval and a sector would be sampled at a section.
fn simplest_between(lo: Option<&Rational>, hi: Option<&Rational>) -> Rational {
    let margin =
        |bound: &Rational| ((bound).abs() + Rational::ONE) / Rational::from(10u32).pow(35u64);
    let lo = lo.map(|lo| lo + margin(lo));
    let hi = hi.map(|hi| hi - margin(hi));
    let (lo, hi) = (lo.as_ref(), hi.as_ref());
    match (lo, hi) {
        (None, None) => Rational::ZERO,
        (Some(lo), None) if *lo < 0 => Rational::ZERO,
        (Some(lo), None) => Rational::from(lo.clone().floor()) + Rational::ONE,
        (None, Some(hi)) if *hi > 0 => Rational::ZERO,
        (None, Some(hi)) => Rational::from(hi.clone().ceiling()) - Rational::ONE,
        (Some(lo), Some(hi)) => simplest(lo, hi),
    }
}

/// A relation `{$c product p_i^(e_i) / product q_j^(f_j) op 0$}`.
struct Constraint {
    relation: Relation,
    /// The sign of `c`, the part free of unknowns.
    sign: Ordering,
    /// The factors `p_i` of the numerator, and whether their multiplicity is odd.
    numerator: Vec<(usize, bool)>,
    /// The factors `q_j` of the denominator, and whether their multiplicity is odd.
    denominator: Vec<(usize, bool)>,
}

/// A sample point of a cell: values of the first unknowns.
#[derive(Clone, Default)]
struct Sample {
    /// The exact values.
    values: Vec<Expr>,
    /// Whether each value is a root (the cell is a point in this unknown).
    sections: Vec<bool>,
    /// The factors vanishing on the cell.
    vanishing: Vec<usize>,
}

/// The solutions over a cell of the first unknowns: `Leaf` once every unknown has a value, else the solutions as
/// intervals of the next unknown.
#[derive(Clone, Debug, PartialEq)]
enum Description {
    Leaf(bool),
    Pieces(Vec<Piece>),
}

impl Description {
    const fn is_empty(&self) -> bool {
        match self {
            Self::Leaf(holds) => !*holds,
            Self::Pieces(pieces) => pieces.is_empty(),
        }
    }
}

/// An interval of the next unknown, with the solutions over it.
#[derive(Clone, Debug, PartialEq)]
struct Piece {
    interval: Interval<R<Rational>>,
    inner: Description,
}

/// A cell of a stack, before merging.
struct Cell {
    interval: Interval<R<Rational>>,
    description: Description,
    /// The value of the unknown, for a section.
    section: Option<Expr>,
}

/// The decomposition.
struct Cad<'a> {
    unknowns: &'a [Symbol],
    /// The irreducible polynomials.
    factors: Vec<Expr>,
    /// The level of each factor, the index of its last unknown.
    levels: Vec<usize>,
    /// The roots of each factor in its last unknown, as expressions of the previous ones.
    roots: Vec<Vec<Expr>>,
    constraints: Vec<Constraint>,
}

impl<'a> Cad<'a> {
    const fn new(unknowns: &'a [Symbol]) -> Self {
        Self {
            unknowns,
            factors: vec![],
            levels: vec![],
            roots: vec![],
            constraints: vec![],
        }
    }

    /// Whether `term` depends on an unknown.
    fn depends(&self, term: &Expr) -> bool {
        self.unknowns.iter().any(|x| depends(term, *x))
    }

    /// Whether `term` is a polynomial in the unknowns, with coefficients free of them.
    fn is_polynomial(&self, term: &Expr) -> bool {
        if !self.depends(term) {
            return true;
        }
        match term {
            Term::Value(_) | Term::Symbol(_) => true,
            Term::Add(add) => add.iter().all(|t| self.is_polynomial(t)),
            Term::Mul(mul) => mul.iter().all(|t| self.is_polynomial(t)),
            Term::Pow(pow) => {
                self.is_polynomial(&pow.base)
                    && matches!(&**pow.exponant, Term::Value(n)
                        if n.value > 0 && n.value.denominator_ref() == &1u32)
            }
            Term::Fun(_) => false,
        }
    }

    /// Whether `term` is a polynomial in the unknowns with rational coefficients, which can be factored.
    fn is_rational(&self, term: &Expr) -> bool {
        match term {
            Term::Value(_) => true,
            Term::Symbol(symbol) => self.unknowns.contains(&symbol.symbol),
            Term::Add(add) => add.iter().all(|t| self.is_rational(t)),
            Term::Mul(mul) => mul.iter().all(|t| self.is_rational(t)),
            Term::Pow(pow) => {
                self.is_rational(&pow.base)
                    && matches!(&**pow.exponant, Term::Value(n)
                        if n.value > 0 && n.value.denominator_ref() == &1u32)
            }
            Term::Fun(_) => false,
        }
    }

    /// The part of the polynomial `p` free of unknowns, and its irreducible factors with their multiplicities.
    fn split_factors(&self, p: &Expr) -> (Expr, Vec<(Expr, u32)>) {
        let factored = if self.depends(p) && self.is_rational(p) {
            p.factor()
        } else {
            p.clone()
        };
        let (mut constant, items): (Expr, Vec<Expr>) = match &factored {
            Term::Mul(mul) => (
                value(mul.coefficient.clone()),
                mul.iter().cloned().collect(),
            ),
            other => (Term::one(R), vec![other.clone()]),
        };
        let mut factors = vec![];
        for item in items {
            if !self.depends(&item) {
                constant *= item;
                continue;
            }
            match &item {
                Term::Pow(pow) => match &**pow.exponant {
                    Term::Value(n) if let Ok(e) = u32::try_from(&n.value) => {
                        factors.push(((*pow.base).clone(), e));
                    }
                    _ => factors.push((item.clone(), 1)),
                },
                _ => factors.push((item, 1)),
            }
        }
        (constant.normalize(), factors)
    }

    /// The index of the factor `p`, added if needed.
    fn add_factor(&mut self, p: &Expr) -> Result<usize, SolveError> {
        let p = p.expand();
        if let Some(index) = self.factors.iter().position(|f| *f == p) {
            return Ok(index);
        }
        if self.factors.len() >= MAX_FACTORS {
            return Err(SolveError::Inequality(
                "too many polynomials to solve the inequalities".to_owned(),
            ));
        }
        let level = self
            .unknowns
            .iter()
            .rposition(|x| depends(&p, *x))
            .expect("A factor depends on an unknown");
        self.factors.push(p);
        self.levels.push(level);
        Ok(self.factors.len() - 1)
    }

    /// The sign of the constant `c`.
    fn constant_sign(c: &Expr) -> Result<Ordering, SolveError> {
        crate::field::real::expr::constant_sign(&c.normalize())
            .ok_or_else(|| SolveError::Inequality(format!("can't find the sign of `{}`", plain(c))))
    }

    /// The factors of the polynomial `p`, and the sign of its part free of unknowns.
    fn factors_of(&mut self, p: &Expr) -> Result<(Ordering, Vec<(usize, bool)>), SolveError> {
        let (constant, factors) = self.split_factors(p);
        let sign = Self::constant_sign(&constant)?;
        let factors = factors
            .into_iter()
            .map(|(factor, multiplicity)| Ok((self.add_factor(&factor)?, multiplicity % 2 == 1)))
            .collect::<Result<_, SolveError>>()?;
        Ok((sign, factors))
    }

    /// Add the relation `lhs op rhs`.
    fn add_constraint(
        &mut self,
        lhs: &Expr,
        relation: Relation,
        rhs: &Expr,
    ) -> Result<(), SolveError> {
        let f = (lhs.clone() - rhs.clone()).normalize();
        let (num, den) = f.as_fraction(true);
        let (num, den) = (num.expand(), den.expand());
        for p in [&num, &den] {
            if !self.is_polynomial(p) {
                return Err(SolveError::NotPolynomial(plain(p)));
            }
        }
        let (num_sign, numerator) = self.factors_of(&num)?;
        let (den_sign, denominator) = self.factors_of(&den)?;
        self.constraints.push(Constraint {
            relation,
            sign: mul(num_sign, den_sign),
            numerator,
            denominator,
        });
        Ok(())
    }

    /// The resultant of the polynomials of coefficients `p` and `q`.
    fn resultant(p: &[Expr], q: &[Expr]) -> Result<Expr, SolveError> {
        if p.len() + q.len() - 2 > MAX_SYLVESTER_SIZE {
            return Err(SolveError::Inequality(
                "the polynomials of the inequalities have too large degrees".to_owned(),
            ));
        }
        Ok(sylvester_determinant(p, q).expand())
    }

    /// Project the factors of each level to the lower levels, from the last one.
    fn project(&mut self) -> Result<(), SolveError> {
        for level in (1..self.unknowns.len()).rev() {
            let x = self.unknowns[level];
            let forms = (0..self.factors.len())
                .filter(|id| self.levels[*id] == level)
                .map(|id| polynomial_form(&self.factors[id], x))
                .collect::<Result<Vec<_>, _>>()?;
            let mut projected = vec![];
            for (i, form) in forms.iter().enumerate() {
                projected.extend(form.iter().cloned());
                if form.len() > 2 {
                    let derivative: Vec<Expr> = form
                        .iter()
                        .enumerate()
                        .skip(1)
                        .map(|(degree, c)| (value(Rational::from(degree)) * c.clone()).normalize())
                        .collect();
                    projected.push(Self::resultant(form, &derivative)?);
                }
                for other in &forms[i + 1..] {
                    projected.push(Self::resultant(form, other)?);
                }
            }
            for p in projected {
                let p = p.expand();
                if p.is_zero() || !self.depends(&p) {
                    continue;
                }
                let (_, factors) = self.split_factors(&p);
                for (factor, _) in factors {
                    self.add_factor(&factor)?;
                }
            }
        }
        Ok(())
    }

    /// Find the roots of the factors as expressions of the previous unknowns.
    fn find_roots(&mut self) {
        self.roots = (0..self.factors.len())
            .map(|id| {
                let level = self.levels[id];
                if level == 0 {
                    return vec![];
                }
                let equation = Equation::new(self.factors[id].clone(), zero());
                R.solve_for(&[equation], &[self.unknowns[level]])
                    .map_or_default(values)
            })
            .collect();
    }

    /// `term` with the first unknowns replaced by `values`.
    fn substitute(term: &Expr, values: &[(Symbol, Expr)]) -> Expr {
        values
            .iter()
            .fold(term.clone(), |term, (x, value)| subs(&term, *x, value))
            .normalize()
    }

    /// The first unknowns with their values in `sample`.
    fn point(&self, sample: &Sample) -> Vec<(Symbol, Expr)> {
        self.unknowns
            .iter()
            .copied()
            .zip(sample.values.iter().cloned())
            .collect()
    }

    /// The approximation of `term` at `point`.
    fn approximate_at(term: &Expr, point: &[(Symbol, Expr)]) -> Option<Rational> {
        approximate(&Self::substitute(term, point), DIGITS)
    }

    /// The sign of the factor `id` at the sample point of a cell.
    fn factor_sign(&self, id: usize, sample: &Sample) -> Result<Ordering, SolveError> {
        if sample.vanishing.contains(&id) {
            return Ok(Ordering::Equal);
        }
        let factor = &self.factors[id];
        match Self::approximate_at(factor, &self.point(sample)) {
            Some(approximation) if approximation != 0 => Ok(approximation.cmp(&Rational::ZERO)),
            _ => Err(SolveError::Inequality(format!(
                "can't find the sign of `{}`",
                plain(factor)
            ))),
        }
    }

    /// Whether every relation holds at the sample point of a cell, giving a value to every unknown.
    fn holds(&self, sample: &Sample) -> Result<bool, SolveError> {
        for constraint in &self.constraints {
            let mut sign = constraint.sign;
            for (id, odd) in &constraint.numerator {
                let factor = self.factor_sign(*id, sample)?;
                if factor == Ordering::Equal || *odd {
                    sign = mul(sign, factor);
                }
            }
            for (id, odd) in &constraint.denominator {
                let factor = self.factor_sign(*id, sample)?;
                if factor == Ordering::Equal {
                    return Ok(false);
                }
                if *odd {
                    sign = mul(sign, factor);
                }
            }
            if constraint.relation.holds(SignSet::from_ordering(sign)) != Some(true) {
                return Ok(false);
            }
        }
        Ok(true)
    }

    /// The root `root` of the factors `ids` over the cell of `sample`, as an expression of the previous unknowns.
    fn symbolic_root(
        &self,
        root: &Root,
        ids: &[usize],
        sample: &Sample,
    ) -> Result<Expr, SolveError> {
        let point = self.point(sample);
        for id in ids {
            for candidate in &self.roots[*id] {
                if Self::approximate_at(candidate, &point)
                    .is_some_and(|approximation| close(&approximation, &root.approximation))
                {
                    return Ok(candidate.clone());
                }
            }
        }
        let id = ids[0];
        Err(SolveError::Inequality(format!(
            "can't express the roots of `{}` in `{}`",
            plain(&self.factors[id]),
            self.unknowns[self.levels[id]].name()
        )))
    }

    /// The real roots of `p`, the factor `id` over the point of `sample`, when they can be found by elimination.
    ///
    /// `solve_for` doesn't finish on polynomials of degree 3 or more whose coefficients are written with nested
    /// radicals, like a quartic in `{$y$}` over a root of its discriminant in `{$x$}`. Their roots are roots of the
    /// resultants of the factor with the factors vanishing at the sections of the sample, which eliminate the unknowns
    /// with irrational values: a polynomial with rational coefficients, whose exact real roots (`rootof`) are kept
    /// where `p` vanishes. Returns `None` when a resultant vanishes or is too large.
    fn eliminated_roots(
        &self,
        id: usize,
        p: &Expr,
        sample: &Sample,
    ) -> Result<Option<Vec<Root>>, SolveError> {
        let level = sample.values.len();
        let x = self.unknowns[level];
        // The values of sectors are rationals
        let sectors: Vec<(Symbol, Expr)> = self
            .point(sample)
            .into_iter()
            .zip(&sample.sections)
            .filter_map(|(value, section)| (!*section).then_some(value))
            .collect();
        let mut eliminated = Self::substitute(&self.factors[id], &sectors).expand();
        for j in (0..level).rev().filter(|j| sample.sections[*j]) {
            let xj = self.unknowns[j];
            if !depends(&eliminated, xj) {
                continue;
            }
            let Some(section) = sample
                .vanishing
                .iter()
                .find(|vanishing| self.levels[**vanishing] == j)
            else {
                return Ok(None);
            };
            let q = Self::substitute(&self.factors[*section], &sectors).expand();
            let (p_form, q_form) = (polynomial_form(&eliminated, xj)?, polynomial_form(&q, xj)?);
            if p_form.len() + q_form.len() - 2 > MAX_SYLVESTER_SIZE {
                return Ok(None);
            }
            eliminated = Self::resultant(&p_form, &q_form)?;
        }
        let Some(coefficients) = values_of(&polynomial_form(&eliminated, x)?) else {
            return Ok(None);
        };
        if coefficients.iter().all(|c| *c == 0) {
            return Ok(None);
        }
        if coefficients.len() < 2 {
            return Ok(Some(vec![]));
        }
        let roots = rootof::real_roots(&Poly::new(coefficients))
            .into_iter()
            .filter(|root| {
                approximate_fixed(&subs(p, x, root).normalize(), SAME_BOUND_BITS)
                    .is_some_and(|value| close(&value, &Rational::ZERO))
            })
            .collect();
        approximated(roots).map(Some)
    }

    /// The solutions over the cell of `sample`.
    fn lift(&self, sample: &Sample) -> Result<Description, SolveError> {
        let level = sample.values.len();
        if level == self.unknowns.len() {
            return Ok(Description::Leaf(self.holds(sample)?));
        }
        let x = self.unknowns[level];
        let point = self.point(sample);
        // The roots of the factors of this level over the sample point, sorted, with the factors vanishing there
        let mut roots: Vec<(Root, Vec<usize>)> = vec![];
        for id in (0..self.factors.len()).filter(|id| self.levels[*id] == level) {
            let mut p = Self::substitute(&self.factors[id], &point).expand();
            if sample.sections.iter().any(|section| *section) {
                p = with_rational_coefficients(&p, x)?;
            }
            if p.is_zero() {
                return Err(SolveError::Inequality(format!(
                    "`{}` vanishes identically on a part of the solutions",
                    plain(&self.factors[id])
                )));
            }
            let form = polynomial_form(&p, x)?;
            let eliminated = if form.len() > 3 && values_of(&form).is_none() {
                self.eliminated_roots(id, &p, sample)?
            } else {
                None
            };
            let found = match eliminated {
                Some(found) => found,
                None => real_roots(&p, x)?,
            };
            roots.extend(found.into_iter().map(|root| (root, vec![id])));
        }
        roots.sort_by(|(a, _), (b, _)| a.approximation.cmp(&b.approximation));
        let mut merged: Vec<(Root, Vec<usize>)> = vec![];
        for (root, ids) in roots {
            match merged.last_mut() {
                Some((last, last_ids)) if close(&last.approximation, &root.approximation) => {
                    last_ids.extend(ids);
                }
                _ => merged.push((root, ids)),
            }
        }
        // Over points, the bounds are constants, else expressions of the previous unknowns
        let constants = sample.sections.iter().all(|section| *section);
        let bounds = merged
            .iter()
            .map(|(root, ids)| {
                if constants {
                    Ok(root.value.clone())
                } else {
                    self.symbolic_root(root, ids, sample)
                }
            })
            .collect::<Result<Vec<_>, SolveError>>()?;
        let mut cells = vec![];
        for i in 0..=merged.len() {
            let lower = i.checked_sub(1);
            let mut child = sample.clone();
            child.values.push(value(simplest_between(
                lower.map(|j| &merged[j].0.approximation),
                merged.get(i).map(|(root, _)| &root.approximation),
            )));
            child.sections.push(false);
            cells.push(Cell {
                interval: Interval {
                    lo: lower.map(|j| bounds[j].clone()),
                    lo_closed: false,
                    hi: bounds.get(i).cloned(),
                    hi_closed: false,
                },
                description: self.lift(&child)?,
                section: None,
            });
            if let Some((root, ids)) = merged.get(i) {
                let mut child = sample.clone();
                child.values.push(root.value.clone());
                child.sections.push(true);
                child.vanishing.extend(ids);
                cells.push(Cell {
                    interval: Interval {
                        lo: Some(bounds[i].clone()),
                        lo_closed: true,
                        hi: Some(bounds[i].clone()),
                        hi_closed: true,
                    },
                    description: self.lift(&child)?,
                    section: Some(root.value.clone()),
                });
            }
        }
        Ok(Description::Pieces(self.merge(&cells, &point)))
    }

    /// Whether the sector `sector` and the neighboring section `section` have the same description at the section.
    fn continues(&self, sector: &Cell, section: &Cell, point: &[(Symbol, Expr)]) -> bool {
        let mut point = point.to_vec();
        point.push((
            self.unknowns[point.len()],
            section.section.clone().expect("A section has a value"),
        ));
        self.equivalent(&sector.description, &section.description, &point)
    }

    /// Whether the descriptions `a` and `b` are the same at `point`.
    fn equivalent(&self, a: &Description, b: &Description, point: &[(Symbol, Expr)]) -> bool {
        match (a, b) {
            (Description::Leaf(a), Description::Leaf(b)) => a == b,
            (Description::Pieces(a), Description::Pieces(b)) => {
                a.len() == b.len()
                    && a.iter().zip(b).all(|(a, b)| {
                        let (i, j) = (&a.interval, &b.interval);
                        let lo = Self::same_bound(i.lo.as_ref(), j.lo.as_ref(), point);
                        let hi = Self::same_bound(i.hi.as_ref(), j.hi.as_ref(), point);
                        if !(lo && hi && i.lo_closed == j.lo_closed && i.hi_closed == j.hi_closed) {
                            return false;
                        }
                        // Compare the next levels inside the interval
                        let inside = if let Some(value) = i.point() {
                            Self::substitute(value, point)
                        } else {
                            let bound = |bound: Option<&Expr>| {
                                bound.and_then(|bound| Self::approximate_at(bound, point))
                            };
                            let (lo, hi) = (bound(i.lo.as_ref()), bound(i.hi.as_ref()));
                            if (i.lo.is_some() && lo.is_none()) || (i.hi.is_some() && hi.is_none())
                            {
                                return false;
                            }
                            // The bounds of a sector may meet at the point, like `{$plus.minus sqrt(1 - x^2)$}`
                            // at `{$x = 1$}`
                            value(simplest_between(lo.as_ref(), hi.as_ref()))
                        };
                        let mut point = point.to_vec();
                        point.push((self.unknowns[point.len()], inside));
                        self.equivalent(&a.inner, &b.inner, &point)
                    })
            }
            _ => false,
        }
    }

    /// Whether the bounds `a` and `b` are the same at `point`.
    fn same_bound(a: Option<&Expr>, b: Option<&Expr>, point: &[(Symbol, Expr)]) -> bool {
        match (a, b) {
            (None, None) => true,
            (Some(a), Some(b)) => {
                // `close` only needs an absolute accuracy, and a bound may vanish at the point, where `approximate`
                // would raise its precision up to its maximum
                let approximate_at = |term: &Expr| {
                    approximate_fixed(&Self::substitute(term, point), SAME_BOUND_BITS)
                };
                match (approximate_at(a), approximate_at(b)) {
                    (Some(a), Some(b)) => close(&a, &b),
                    _ => false,
                }
            }
            _ => false,
        }
    }

    /// Merge the consecutive cells of a stack with the same solutions, keeping the cells with solutions.
    fn merge(&self, cells: &[Cell], point: &[(Symbol, Expr)]) -> Vec<Piece> {
        let mut pieces: Vec<Piece> = vec![];
        // The piece being built, the index of its last cell, and whether it has a sector
        let mut current: Option<(Piece, usize, bool)> = None;
        for (i, cell) in cells.iter().enumerate() {
            if cell.description.is_empty() {
                continue;
            }
            let is_sector = cell.section.is_none();
            if let Some((piece, last, has_sector)) = &mut current
                && *last + 1 == i
            {
                let previous = &cells[*last];
                let continues = if is_sector {
                    self.continues(cell, previous, point)
                        && (!*has_sector || piece.inner == cell.description)
                } else {
                    self.continues(previous, cell, point)
                };
                if continues {
                    piece.interval.hi.clone_from(&cell.interval.hi);
                    piece.interval.hi_closed = cell.interval.hi_closed;
                    if is_sector {
                        piece.inner = cell.description.clone();
                        *has_sector = true;
                    }
                    *last = i;
                    continue;
                }
            }
            if let Some((piece, ..)) = current.take() {
                pieces.push(piece);
            }
            current = Some((
                Piece {
                    interval: cell.interval.clone(),
                    inner: cell.description.clone(),
                },
                i,
                is_sector,
            ));
        }
        pieces.extend(current.map(|(piece, ..)| piece));
        pieces
    }

    /// The cells of `description`, `prefix` giving the intervals of the previous unknowns and `points` the values
    /// of those which are points.
    fn flatten(
        &self,
        description: &Description,
        prefix: &mut Vec<Interval<R<Rational>>>,
        points: &[(Symbol, Expr)],
        out: &mut Vec<Vec<Interval<R<Rational>>>>,
    ) {
        match description {
            Description::Leaf(true) => out.push(prefix.clone()),
            Description::Leaf(false) => {}
            Description::Pieces(pieces) => {
                let x = self.unknowns[prefix.len()];
                for piece in pieces {
                    let bound = |bound: &Option<Expr>| {
                        bound.as_ref().map(|bound| Self::substitute(bound, points))
                    };
                    let interval = Interval {
                        lo: bound(&piece.interval.lo),
                        hi: bound(&piece.interval.hi),
                        ..piece.interval.clone()
                    };
                    let mut points = points.to_vec();
                    if let Some(value) = interval.point() {
                        points.push((x, value.clone()));
                    }
                    prefix.push(interval);
                    self.flatten(&piece.inner, prefix, &points, out);
                    prefix.pop();
                }
            }
        }
    }
}

/// Solve the polynomial `inequalities` for `unknowns`, which contain every symbol of the relations: the cells of
/// the solutions, with an interval per unknown.
pub(super) fn solve(
    inequalities: &[&Inequality<R<Rational>>],
    unknowns: &[Symbol],
) -> Result<Vec<Vec<Interval<R<Rational>>>>, SolveError> {
    if unknowns.len() > MAX_UNKNOWNS {
        return Err(SolveError::Inequality(format!(
            "inequalities relating more than {MAX_UNKNOWNS} unknowns can't be solved"
        )));
    }
    let mut cad = Cad::new(unknowns);
    for inequality in inequalities {
        cad.add_constraint(&inequality.lhs, inequality.relation, &inequality.rhs)?;
    }
    // The assumptions on the unknowns are other relations, when they relate only unknowns
    let assumptions = Assumptions::current();
    let mut conditions = BTreeSet::new();
    for x in unknowns {
        let assumed = assumptions.get(*x).sign;
        if assumed != SignSet::ANY {
            conditions.insert((LinearForm::variable(Var::Symbol(*x)), assumed));
        }
        conditions.extend(
            assumptions
                .conditions_on(*x)
                .into_iter()
                .filter(|(form, _)| form.symbols().all(|s| unknowns.contains(&s))),
        );
    }
    for (form, signs) in conditions {
        if let Some(relation) = Relation::ALL
            .into_iter()
            .find(|relation| relation.signs() == signs)
        {
            cad.add_constraint(&linear_expr(&form, &[]), relation, &zero())?;
        }
    }
    // Roots contradicting the assumptions are needed too
    let _guard = Assumptions::new().enter();
    cad.project()?;
    cad.find_roots();
    let description = cad.lift(&Sample::default())?;
    let mut cells = vec![];
    cad.flatten(&description, &mut vec![], &[], &mut cells);
    Ok(cells)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_simplest() {
        let r = |p: i64, q: i64| Rational::from(p) / Rational::from(q);
        assert_eq!(simplest(&r(1, 3), &r(2, 3)), r(1, 2));
        assert_eq!(simplest(&r(-5, 2), &r(-2, 1)), r(-7, 3));
        assert_eq!(simplest(&r(-1, 1), &r(3, 1)), r(0, 1));
        assert_eq!(simplest(&r(1, 1), &r(3, 2)), r(4, 3));
        assert_eq!(simplest(&r(2, 1), &r(7, 2)), r(3, 1));
        assert_eq!(simplest_between(Some(&r(5, 2)), None), Rational::from(3));
        assert_eq!(simplest_between(None, Some(&r(-1, 2))), Rational::from(-1));
    }
}
