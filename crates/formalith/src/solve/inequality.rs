//! Inequalities in one unknown, like `x^2 - 3x + 2 > 0`, whose solutions are unions of intervals.
//!
//! Each relation `lhs op rhs` is written as `{$f = n / d$}`, `n` and `d` being polynomials in the unknown. The real
//! roots of `n` and `d` (found by [`Solve::solve_for`], so they can have radicals) split the line into open
//! intervals, on which `f` has a constant sign, found at a sample point. The relations of a system hold on the
//! intersection of their solutions.

use std::{collections::BTreeSet, fmt};

use malachite::{
    Rational,
    base::num::{
        arithmetic::traits::{Abs, Pow},
        basic::traits::Zero,
    },
};

use crate::{
    context::{
        Context, Symbol,
        assumptions::{SignSet, assumption},
    },
    field::{
        Set,
        real::{
            R,
            approx::approximate,
            expr::{Expr, depends, subs, value, zero},
        },
    },
    printer::{PrettyPrint, PrettyPrinter, Print, PrintOptions},
    term::{Expand, Normalize, SymbolTerm, Term, relation::Relation},
};

use super::{Equation, Solution, Solve, SolveError};

/// Significant digits of the approximations comparing roots and finding signs.
const DIGITS: u64 = 40;

/// A relation `lhs op rhs`, like `x^2 < 4`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Inequality<T: Set> {
    /// The left side.
    pub lhs: Term<T>,
    /// The comparison.
    pub relation: Relation,
    /// The right side.
    pub rhs: Term<T>,
}

impl<T: Set> Inequality<T> {
    /// Create the relation `lhs op rhs`.
    #[must_use]
    pub const fn new(lhs: Term<T>, relation: Relation, rhs: Term<T>) -> Self {
        Self { lhs, relation, rhs }
    }
}

impl<T: Set> Print for Inequality<T> {
    fn print(&self, options: &PrintOptions, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.lhs.print(options, f)?;
        f.write_str(" ")?;
        Self::operator(self.relation.operator(), options, f)?;
        f.write_str(" ")?;
        self.rhs.print(options, f)
    }
}

impl<T: Set> PrettyPrint for Inequality<T> {
    fn pretty_print(&self, options: &PrintOptions) -> PrettyPrinter {
        let mut res = self.lhs.pretty_print(options);
        res.concat(
            self.relation.pretty_operator(),
            true,
            &self.rhs.pretty_print(options),
        );
        res
    }
}

impl<T: Set> fmt::Display for Inequality<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        PrettyPrint::fmt(self, &PrintOptions::default(), f)
    }
}

/// An interval of the real line, with bounds `None` at infinity.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Interval<T: Set> {
    /// The lower bound, `None` for `{$-oo$}`.
    pub lo: Option<Term<T>>,
    /// Whether the lower bound belongs to the interval.
    pub lo_closed: bool,
    /// The upper bound, `None` for `{$oo$}`.
    pub hi: Option<Term<T>>,
    /// Whether the upper bound belongs to the interval.
    pub hi_closed: bool,
}

impl<T: Set> Interval<T> {
    /// Whether the interval is a single point `{$[a, a]$}`.
    fn point(&self) -> Option<&Term<T>> {
        match (&self.lo, &self.hi) {
            (Some(lo), Some(hi)) if lo == hi => Some(lo),
            _ => None,
        }
    }
}

/// The solutions of inequalities in one unknown: the union of disjoint intervals, sorted.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Intervals<T: Set> {
    /// The unknown, `None` when the relations don't contain any symbol.
    pub unknown: Option<Symbol>,
    /// The intervals.
    pub intervals: Vec<Interval<T>>,
}

impl<T: Set> Intervals<T> {
    /// Whether every value is a solution.
    fn is_everything(&self) -> bool {
        matches!(
            self.intervals.as_slice(),
            [Interval {
                lo: None,
                hi: None,
                ..
            }]
        )
    }

    /// The text printed without intervals.
    fn text(&self, options: &PrintOptions) -> Option<String> {
        let text = match self.unknown {
            _ if self.intervals.is_empty() => "no solution",
            None => "true",
            Some(_) => return None,
        };
        Some(if options.typst {
            format!("\"{text}\"")
        } else {
            text.to_owned()
        })
    }
}

impl<T: Set> Print for Intervals<T> {
    fn print(&self, options: &PrintOptions, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let Some(text) = self.text(options) {
            return f.write_str(&text);
        }
        let unknown = self.unknown.expect("There is an unknown").name();
        let (element, union, reals) = if options.typst {
            (" in ", " union ", "RR")
        } else {
            (" ∈ ", " ∪ ", "ℝ")
        };
        if let [interval] = self.intervals.as_slice()
            && let Some(point) = interval.point()
        {
            write!(f, "{unknown} ")?;
            Self::operator("=", options, f)?;
            f.write_str(" ")?;
            return point.print(options, f);
        }
        write!(f, "{unknown}{element}")?;
        if self.is_everything() {
            return f.write_str(reals);
        }
        for (i, interval) in self.intervals.iter().enumerate() {
            if i != 0 {
                f.write_str(union)?;
            }
            if let Some(point) = interval.point() {
                f.write_str("{")?;
                point.print(options, f)?;
                f.write_str("}")?;
                continue;
            }
            f.write_str(if interval.lo_closed { "[" } else { "(" })?;
            match &interval.lo {
                Some(lo) => lo.print(options, f)?,
                None => f.write_str("-oo")?,
            }
            f.write_str(", ")?;
            match &interval.hi {
                Some(hi) => hi.print(options, f)?,
                None => f.write_str("oo")?,
            }
            f.write_str(if interval.hi_closed { "]" } else { ")" })?;
        }
        Ok(())
    }
}

impl<T: Set> PrettyPrint for Intervals<T> {
    fn pretty_print(&self, options: &PrintOptions) -> PrettyPrinter {
        if let Some(text) = self.text(options) {
            return text.into();
        }
        let mut res =
            PrettyPrinter::from(self.unknown.expect("There is an unknown").name().to_owned());
        if let [interval] = self.intervals.as_slice()
            && let Some(point) = interval.point()
        {
            res.concat("=", true, &point.pretty_print(options));
            return res;
        }
        if self.is_everything() {
            res.concat("∈", true, &PrettyPrinter::from("ℝ".to_owned()));
            return res;
        }
        let mut union = PrettyPrinter::empty();
        for interval in &self.intervals {
            let printed = if let Some(point) = interval.point() {
                let mut point = point.pretty_print(options);
                point.group('{', '}');
                point
            } else {
                let bound = |bound: &Option<Term<T>>, positive| {
                    bound.as_ref().map_or_else(
                        || PrettyPrinter::from(if positive { "∞" } else { "-∞" }.to_owned()),
                        |bound| bound.pretty_print(options),
                    )
                };
                let mut printed = bound(&interval.lo, false);
                printed.concat(", ", false, &bound(&interval.hi, true));
                printed.group(
                    if interval.lo_closed { '[' } else { '(' },
                    if interval.hi_closed { ']' } else { ')' },
                );
                printed
            };
            union.concat("∪", true, &printed);
        }
        res.concat("∈", true, &union);
        res
    }
}

impl<T: Set> fmt::Display for Intervals<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        PrettyPrint::fmt(self, &PrintOptions::default(), f)
    }
}

/// Sets in which inequalities can be solved. Implemented for every set, but only supported in `{$RR$}`.
pub trait SolveInequality: Set {
    /// Solve the system of `inequalities` (which may contain equations) for `unknown`, or for their only symbol
    /// when `unknown` is `None`.
    ///
    /// # Errors
    /// Returns an error if the set has no order, if there are several unknowns or parameters, or if a relation
    /// isn't between rational functions of the unknown whose roots can be found.
    fn solve_inequalities(
        &self,
        inequalities: &[Inequality<Self>],
        unknown: Option<Symbol>,
    ) -> Result<Intervals<Self>, SolveError>;
}

impl<T: Set> SolveInequality for T {
    default fn solve_inequalities(
        &self,
        _: &[Inequality<Self>],
        _: Option<Symbol>,
    ) -> Result<Intervals<Self>, SolveError> {
        Err(SolveError::Unsupported)
    }
}

/// A root of a numerator or a denominator, with its approximation.
#[derive(Clone)]
struct Root {
    value: Expr,
    approximation: Rational,
}

impl Root {
    /// Whether `self` and `other` are approximately the same point.
    fn same(&self, other: &Self) -> bool {
        let difference = (&self.approximation - &other.approximation).abs();
        let scale = self.approximation.clone().abs() + Rational::from(1);
        difference * Rational::from(10u32).pow(30u64) <= scale
    }
}

/// A relation `{$f op 0$}` with `{$f = n / d$}`, and the real roots of `n` and `d`.
struct Prepared {
    f: Expr,
    relation: Relation,
    numerator_roots: Vec<Root>,
    denominator_roots: Vec<Root>,
}

impl Prepared {
    /// Whether the relation holds at `point`.
    fn holds_at(&self, point: &Root, x: Symbol) -> Result<bool, SolveError> {
        if self.denominator_roots.iter().any(|root| root.same(point)) {
            return Ok(false);
        }
        if self.numerator_roots.iter().any(|root| root.same(point)) {
            return Ok(self.relation.holds(SignSet::ZERO) == Some(true));
        }
        self.holds_with(&subs(&self.f, x, &point.value))
    }

    /// Whether the relation holds on the open interval containing the rational `sample`, which isn't a root.
    fn holds_near(&self, sample: &Rational, x: Symbol) -> Result<bool, SolveError> {
        self.holds_with(&subs(&self.f, x, &value(sample.clone())))
    }

    /// Whether the relation holds for the constant value `f`, non-zero.
    fn holds_with(&self, f: &Expr) -> Result<bool, SolveError> {
        let approximation = approximate(&f.normalize(), DIGITS).ok_or_else(|| {
            SolveError::Inequality(format!("can't find the sign of `{}`", super::plain(f)))
        })?;
        let sign = SignSet::from_ordering(approximation.cmp(&Rational::ZERO));
        Ok(self.relation.holds(sign) == Some(true))
    }
}

/// Whether `term` is a polynomial in `x`, with coefficients free of `x`.
fn is_polynomial(term: &Expr, x: Symbol) -> bool {
    if !depends(term, x) {
        return true;
    }
    match term {
        Term::Value(_) | Term::Symbol(_) => true,
        Term::Add(add) => add.iter().all(|t| is_polynomial(t, x)),
        Term::Mul(mul) => mul.iter().all(|t| is_polynomial(t, x)),
        Term::Pow(pow) => {
            is_polynomial(&pow.base, x)
                && matches!(&**pow.exponant, Term::Value(n)
                    if n.value > 0 && n.value.denominator_ref() == &1u32)
        }
        Term::Fun(_) => false,
    }
}

/// The real roots of the polynomial `p` in `x`, approximated.
fn real_roots(p: &Expr, x: Symbol) -> Result<Vec<Root>, SolveError> {
    if !depends(p, x) {
        return Ok(vec![]);
    }
    let solution = R.solve_for(&[Equation::new(p.clone(), zero())], &[x])?;
    let values = match solution {
        Solution::NoSolution => vec![],
        Solution::Assignments(assignments) => {
            assignments.into_iter().map(|(_, value)| value).collect()
        }
        Solution::Alternatives(branches) => branches
            .into_iter()
            .filter_map(|assignments| assignments.into_iter().next().map(|(_, value)| value))
            .collect(),
    };
    values
        .into_iter()
        .map(|value| {
            let approximation = approximate(&value, DIGITS).ok_or_else(|| {
                SolveError::Inequality(format!("can't approximate `{}`", super::plain(&value)))
            })?;
            Ok(Root {
                value,
                approximation,
            })
        })
        .collect()
}

impl SolveInequality for R<Rational> {
    fn solve_inequalities(
        &self,
        inequalities: &[Inequality<Self>],
        unknown: Option<Symbol>,
    ) -> Result<Intervals<Self>, SolveError> {
        let symbols: BTreeSet<Symbol> = inequalities
            .iter()
            .flat_map(|inequality| [&inequality.lhs, &inequality.rhs])
            .flat_map(Term::symbols)
            .filter(|symbol| !Context::is_builtin_constant(*symbol))
            .collect();
        let unknown = match unknown {
            Some(unknown) => Some(unknown),
            None if symbols.len() <= 1 => symbols.first().copied(),
            None => None,
        };
        if symbols.iter().any(|symbol| Some(*symbol) != unknown) {
            return Err(SolveError::Inequality(
                "inequalities are solved for a single unknown, without parameters".to_owned(),
            ));
        }
        // Without symbols, the relations are checked at any point
        let x = unknown.unwrap_or_else(|| Symbol::new("x"));
        let prepared = inequalities
            .iter()
            .map(|inequality| {
                let f = (inequality.lhs.clone() - inequality.rhs.clone()).normalize();
                let (num, den) = f.as_fraction(true);
                let (num, den) = (num.expand(), den.expand());
                for p in [&num, &den] {
                    if !is_polynomial(p, x) {
                        return Err(SolveError::NotPolynomial(super::plain(p)));
                    }
                }
                Ok(Prepared {
                    f,
                    relation: inequality.relation,
                    numerator_roots: real_roots(&num, x)?,
                    denominator_roots: real_roots(&den, x)?,
                })
            })
            .collect::<Result<Vec<_>, SolveError>>()?;
        let mut prepared = prepared;
        // The assumptions on the unknown are another relation
        let assumed = assumption(x).sign;
        if let Some(relation) = Relation::ALL
            .into_iter()
            .find(|relation| relation.signs() == assumed && assumed != SignSet::ANY)
        {
            // `solve` would drop the root 0, which contradicts the assumption
            prepared.push(Prepared {
                f: Term::Symbol(SymbolTerm::new(x, R)),
                relation,
                numerator_roots: vec![Root {
                    value: zero(),
                    approximation: Rational::ZERO,
                }],
                denominator_roots: vec![],
            });
        }
        // The points splitting the line, sorted and without duplicates
        let mut points: Vec<Root> = prepared
            .iter()
            .flat_map(|p| p.numerator_roots.iter().chain(&p.denominator_roots))
            .cloned()
            .collect();
        points.sort_by(|a, b| a.approximation.cmp(&b.approximation));
        points.dedup_by(|a, b| a.same(b));
        let holds_near = |sample: &Rational| -> Result<bool, SolveError> {
            prepared
                .iter()
                .try_fold(true, |res, p| Ok(res && p.holds_near(sample, x)?))
        };
        let holds_at = |point: &Root| -> Result<bool, SolveError> {
            prepared
                .iter()
                .try_fold(true, |res, p| Ok(res && p.holds_at(point, x)?))
        };
        // Pieces of the line: the open intervals between the points, and the points
        let mut intervals = vec![];
        let mut current: Option<(Option<Expr>, bool)> = None;
        for k in 0..=points.len() {
            let lower = k.checked_sub(1).map(|j| &points[j]);
            if let Some(point) = lower {
                if holds_at(point)? {
                    current.get_or_insert((Some(point.value.clone()), true));
                } else if let Some((lo, lo_closed)) = current.take() {
                    intervals.push(Interval {
                        lo,
                        lo_closed,
                        hi: Some(point.value.clone()),
                        hi_closed: false,
                    });
                }
            }
            let sample = match (lower, points.get(k)) {
                (None, None) => Rational::ZERO,
                (None, Some(upper)) => &upper.approximation - Rational::from(1),
                (Some(lower), None) => &lower.approximation + Rational::from(1),
                (Some(lower), Some(upper)) => {
                    (&lower.approximation + &upper.approximation) / Rational::from(2)
                }
            };
            if holds_near(&sample)? {
                current.get_or_insert((lower.map(|point| point.value.clone()), false));
            } else if let Some((lo, lo_closed)) = current.take() {
                let point = lower.expect("An interval started at a point");
                intervals.push(Interval {
                    lo,
                    lo_closed,
                    hi: Some(point.value.clone()),
                    hi_closed: true,
                });
            }
        }
        if let Some((lo, lo_closed)) = current {
            intervals.push(Interval {
                lo,
                lo_closed,
                hi: None,
                hi_closed: false,
            });
        }
        Ok(Intervals { unknown, intervals })
    }
}
