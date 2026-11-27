//! Systems of inequalities, like `x^2 - 3x + 2 > 0` or `x^2 + y^2 < 1, y > 0`.
//!
//! Their solutions are unions of cells: the first unknown in an interval, the next one between bounds depending on the first one, and so on.
//!
//! Each relation `lhs op rhs` is written as `{$f = n / d$}`, `n` and `d` being polynomials in the unknowns. The
//! relations are split into groups sharing no unknown, each one solved by a cylindrical algebraic decomposition
//! (see [`cad`]), and the solutions of the groups are combined. Absolute values and roots, like in
//! `{$sqrt(x) < 3$}`, are eliminated into polynomials (see [`atoms`]), the domains of even roots being other
//! relations.

mod atoms;
mod cad;

use std::{collections::BTreeSet, fmt};

use malachite::Rational;

use crate::{
    context::{Context, Symbol, assumptions::SignSet},
    field::{
        Set,
        real::{R, expr::constant_sign},
    },
    printer::{PrettyPrint, PrettyPrinter, Print, PrintOptions},
    term::{Normalize, Term, relation::Relation},
};

use super::SolveError;

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
        res.concat_breaking(
            self.relation.pretty_operator(),
            true,
            &self.rhs.pretty_print(options),
            crate::printer::BreakKind::Relation,
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
    /// The whole real line.
    const fn everything() -> Self {
        Self {
            lo: None,
            lo_closed: false,
            hi: None,
            hi_closed: false,
        }
    }

    /// Whether the interval is a single point `{$[a, a]$}`.
    fn point(&self) -> Option<&Term<T>> {
        match (&self.lo, &self.hi) {
            (Some(lo), Some(hi)) if lo == hi => Some(lo),
            _ => None,
        }
    }

    /// Whether the interval is the whole real line.
    const fn is_everything(&self) -> bool {
        self.lo.is_none() && self.hi.is_none()
    }

    /// Print the interval, `{a}` for a point.
    fn print_interval(&self, options: PrintOptions, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let Some(point) = self.point() {
            f.write_str("{")?;
            point.print(&options, f)?;
            return f.write_str("}");
        }
        f.write_str(if self.lo_closed { "[" } else { "(" })?;
        match &self.lo {
            Some(lo) => lo.print(&options, f)?,
            None => f.write_str("-oo")?,
        }
        f.write_str(", ")?;
        match &self.hi {
            Some(hi) => hi.print(&options, f)?,
            None => f.write_str("+oo")?,
        }
        f.write_str(if self.hi_closed { "]" } else { ")" })
    }

    /// Pretty print the interval, `{a}` for a point.
    fn pretty_print_interval(&self, options: PrintOptions) -> PrettyPrinter {
        if let Some(point) = self.point() {
            let mut point = point.pretty_print(&options);
            point.group('{', '}');
            return point;
        }
        let bound = |bound: &Option<Term<T>>, positive| {
            bound.as_ref().map_or_else(
                || PrettyPrinter::from(if positive { "+∞" } else { "-∞" }.to_owned()),
                |bound| bound.pretty_print(&options),
            )
        };
        let mut printed = bound(&self.lo, false);
        printed.concat(", ", false, &bound(&self.hi, true));
        printed.group(
            if self.lo_closed { '[' } else { '(' },
            if self.hi_closed { ']' } else { ')' },
        );
        printed
    }
}

/// A printed line of a [`Region`]: the intervals of the first unknowns, and the union of those of the last one.
type Line<'a, T> = (&'a [Interval<T>], Vec<&'a Interval<T>>);

/// The solutions of a system of inequalities: a union of cells.
///
/// Each cell gives an interval per unknown, whose bounds may depend on the previous unknowns, like `{$x in (-1, 1), y in (-sqrt(1 - x^2), sqrt(1 - x^2))$}`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Region<T: Set> {
    /// The unknowns, empty when the relations don't contain any symbol.
    pub unknowns: Vec<Symbol>,
    /// The cells, with an interval per unknown.
    pub cells: Vec<Vec<Interval<T>>>,
}

impl<T: Set> Region<T> {
    /// The text printed without intervals.
    fn text(&self, options: PrintOptions) -> Option<String> {
        let text = if self.cells.is_empty() {
            "no solution"
        } else if self.unknowns.is_empty() {
            "true"
        } else {
            return None;
        };
        Some(if options.typst {
            format!("\"{text}\"")
        } else {
            text.to_owned()
        })
    }

    /// The lines of the solution: groups of consecutive cells only differing by their last interval, which are
    /// printed as a union.
    fn lines(&self) -> Vec<Line<'_, T>> {
        let mut lines: Vec<Line<'_, T>> = vec![];
        for cell in &self.cells {
            let (last, prefix) = cell
                .split_last()
                .expect("A cell has an interval per unknown");
            match lines.last_mut() {
                Some((previous, union)) if *previous == prefix => union.push(last),
                _ => lines.push((prefix, vec![last])),
            }
        }
        lines
    }

    /// Print `unknown` in the union `intervals`.
    fn print_coordinate(
        unknown: Symbol,
        intervals: &[&Interval<T>],
        options: PrintOptions,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result {
        let (element, union, reals) = if options.typst {
            (" in ", " union ", "RR")
        } else {
            (" ∈ ", " ∪ ", "ℝ")
        };
        let name = if options.typst {
            crate::printer::typst_name(unknown.name())
        } else {
            unknown.name().into()
        };
        if let [interval] = intervals
            && let Some(point) = interval.point()
        {
            write!(f, "{name} ")?;
            Self::operator("=", &options, f)?;
            f.write_str(" ")?;
            return point.print(&options, f);
        }
        write!(f, "{name}{element}")?;
        if let [interval] = intervals
            && interval.is_everything()
        {
            return f.write_str(reals);
        }
        for (i, interval) in intervals.iter().enumerate() {
            if i != 0 {
                f.write_str(union)?;
            }
            interval.print_interval(options, f)?;
        }
        Ok(())
    }

    /// Pretty print `unknown` in the union `intervals`.
    fn pretty_print_coordinate(
        unknown: Symbol,
        intervals: &[&Interval<T>],
        options: PrintOptions,
    ) -> PrettyPrinter {
        let mut res = PrettyPrinter::from(unknown.name().to_owned());
        if let [interval] = intervals {
            if let Some(point) = interval.point() {
                res.concat_breaking(
                    "=",
                    true,
                    &point.pretty_print(&options),
                    crate::printer::BreakKind::Relation,
                );
                return res;
            }
            if interval.is_everything() {
                res.concat("∈", true, &PrettyPrinter::from("ℝ".to_owned()));
                return res;
            }
        }
        let mut union = PrettyPrinter::empty();
        for interval in intervals {
            union.concat_breaking(
                "∪",
                true,
                &interval.pretty_print_interval(options),
                crate::printer::BreakKind::Sum,
            );
        }
        res.concat_breaking("∈", true, &union, crate::printer::BreakKind::Relation);
        res
    }
}

impl<T: Set> Print for Region<T> {
    fn print(&self, options: &PrintOptions, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let Some(text) = self.text(*options) {
            return f.write_str(&text);
        }
        let (last, others) = self.unknowns.split_last().expect("There is an unknown");
        // One line per group of cells, `\` being a line break in Typst
        for (i, (prefix, union)) in self.lines().into_iter().enumerate() {
            if i != 0 {
                f.write_str(if options.typst { " \\ " } else { "\n" })?;
            }
            for (unknown, interval) in others.iter().zip(prefix) {
                Self::print_coordinate(*unknown, &[interval], *options, f)?;
                f.write_str(", ")?;
            }
            Self::print_coordinate(*last, &union, *options, f)?;
        }
        Ok(())
    }
}

impl<T: Set> PrettyPrint for Region<T> {
    fn pretty_print(&self, options: &PrintOptions) -> PrettyPrinter {
        if let Some(text) = self.text(*options) {
            return text.into();
        }
        let (last, others) = self.unknowns.split_last().expect("There is an unknown");
        let mut res = PrettyPrinter::empty();
        for (prefix, union) in self.lines() {
            let mut line = PrettyPrinter::empty();
            for (unknown, interval) in others.iter().zip(prefix) {
                line.concat_breaking(
                    ", ",
                    false,
                    &Self::pretty_print_coordinate(*unknown, &[interval], *options),
                    crate::printer::BreakKind::Separator,
                );
            }
            line.concat_breaking(
                ", ",
                false,
                &Self::pretty_print_coordinate(*last, &union, *options),
                crate::printer::BreakKind::Separator,
            );
            res.stack(&line.wrapped(options.width));
        }
        res
    }
}

impl<T: Set> fmt::Display for Region<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        PrettyPrint::fmt(self, &PrintOptions::default(), f)
    }
}

/// Sets in which inequalities can be solved. Implemented for every set, but only supported in `{$RR$}`.
pub trait SolveInequality: Set {
    /// Solve the system of `inequalities` (which may contain equations) for `unknowns`, or for all their symbols
    /// sorted by name when `unknowns` is empty. The bounds of an unknown may depend on the previous ones.
    ///
    /// # Errors
    /// Returns an error if the set has no order, if there are parameters, or if a relation isn't between rational
    /// functions of the unknowns whose roots can be found.
    fn solve_inequalities(
        &self,
        inequalities: &[Inequality<Self>],
        unknowns: &[Symbol],
    ) -> Result<Region<Self>, SolveError>;
}

impl<T: Set> SolveInequality for T {
    default fn solve_inequalities(
        &self,
        _: &[Inequality<Self>],
        _: &[Symbol],
    ) -> Result<Region<Self>, SolveError> {
        Err(SolveError::Unsupported)
    }
}

/// Significant digits of the approximations comparing roots and finding signs.
const DIGITS: u64 = 40;

/// Maximum number of cells of the solution, combining the solutions of independent groups of relations.
const MAX_CELLS: usize = 64;

/// The symbols of a relation, other than builtin constants.
fn symbols(inequality: &Inequality<R<Rational>>) -> BTreeSet<Symbol> {
    [&inequality.lhs, &inequality.rhs]
        .into_iter()
        .flat_map(Term::symbols)
        .filter(|symbol| !Context::is_builtin_constant(*symbol))
        .collect()
}

impl SolveInequality for R<Rational> {
    fn solve_inequalities(
        &self,
        inequalities: &[Inequality<Self>],
        unknowns: &[Symbol],
    ) -> Result<Region<Self>, SolveError> {
        profile_scope!("solve inequalities");
        let all: BTreeSet<Symbol> = inequalities.iter().flat_map(symbols).collect();
        let unknowns = if unknowns.is_empty() {
            let mut all: Vec<Symbol> = all.iter().copied().collect();
            all.sort_by_key(|symbol| symbol.name());
            all
        } else {
            unknowns.to_vec()
        };
        if all.iter().any(|symbol| !unknowns.contains(symbol)) {
            return Err(SolveError::Inequality(
                "inequalities are solved for every symbol, without parameters".to_owned(),
            ));
        }
        // Relations without unknowns are true or false
        for inequality in inequalities.iter().filter(|i| symbols(i).is_empty()) {
            let f = (inequality.lhs.clone() - inequality.rhs.clone()).normalize();
            let sign = constant_sign(&f).ok_or_else(|| {
                SolveError::Inequality(format!("can't find the sign of `{}`", super::plain(&f)))
            })?;
            if inequality.relation.holds(SignSet::from_ordering(sign)) != Some(true) {
                return Ok(Region {
                    unknowns,
                    cells: vec![],
                });
            }
        }
        // Groups of unknowns sharing relations, in the order of `unknowns`
        let mut group: Vec<usize> = (0..unknowns.len()).collect();
        for inequality in inequalities {
            let indices: Vec<usize> = symbols(inequality)
                .iter()
                .filter_map(|symbol| unknowns.iter().position(|u| u == symbol))
                .collect();
            if let Some((&first, rest)) = indices.split_first() {
                for &other in rest {
                    let (from, to) = (group[other], group[first]);
                    for g in &mut group {
                        if *g == from {
                            *g = to;
                        }
                    }
                }
            }
        }
        let mut cells: Vec<Vec<Interval<Self>>> = vec![vec![]];
        let mut order: Vec<usize> = vec![];
        let groups: BTreeSet<usize> = group.iter().copied().collect();
        for g in groups {
            let members: Vec<usize> = (0..unknowns.len()).filter(|i| group[*i] == g).collect();
            let group_unknowns: Vec<Symbol> = members.iter().map(|i| unknowns[*i]).collect();
            let relations: Vec<&Inequality<Self>> = inequalities
                .iter()
                .filter(|inequality| {
                    symbols(inequality)
                        .iter()
                        .any(|symbol| group_unknowns.contains(symbol))
                })
                .collect();
            let group_cells = if relations.is_empty() {
                vec![
                    group_unknowns
                        .iter()
                        .map(|_| Interval::everything())
                        .collect(),
                ]
            } else {
                cad::solve(&relations, &group_unknowns)?
            };
            if group_cells.is_empty() {
                return Ok(Region {
                    unknowns,
                    cells: vec![],
                });
            }
            if cells.len() * group_cells.len() > MAX_CELLS {
                return Err(SolveError::Inequality(
                    "the solution has too many cells".to_owned(),
                ));
            }
            cells = cells
                .iter()
                .flat_map(|cell| {
                    group_cells
                        .iter()
                        .map(move |group_cell: &Vec<Interval<Self>>| {
                            cell.iter().chain(group_cell).cloned().collect()
                        })
                })
                .collect();
            order.extend(members);
        }
        // Back to the order of `unknowns`
        let cells = cells
            .into_iter()
            .map(|cell| {
                let mut sorted: Vec<Option<Interval<Self>>> = vec![None; unknowns.len()];
                for (interval, i) in cell.into_iter().zip(&order) {
                    sorted[*i] = Some(interval);
                }
                sorted
                    .into_iter()
                    .map(|interval| interval.expect("Every unknown has an interval"))
                    .collect()
            })
            .collect();
        Ok(Region { unknowns, cells })
    }
}
