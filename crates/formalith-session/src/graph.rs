//! Graphs of the lines of a session, for graphical interfaces: curves `y = f(x)`, `x = g(y)`, implicit curves and
//! regions in `x` and `y` (also intersections of several relations, like `x^2 + y^2 < 1, y > 0`), and points.
//!
//! Graphs are compiled to [`Numeric`] expressions, evaluated with the values `[x, y, params...]`: `x` at index
//! [`Graph::X`], `y` at index [`Graph::Y`] and the parameters of [`Graph::params`] after them.
//!
//! ```
//! use formalith_session::{Session, formalith::printer::PrintOptions, graph::GraphKind};
//!
//! let mut session = Session::new();
//! let (response, graph) = session.graph("y = a*x^2");
//! assert_eq!(response.output.print(PrintOptions::plain()), "y = (x^2)*a");
//! let graph = graph.unwrap();
//! assert_eq!(graph.params, ["a"]);
//! let GraphKind::Function { expr, .. } = &graph.kind else { unreachable!() };
//! assert_eq!(expr.eval(&[3., f64::NAN, 2.]), 18.);
//! ```

use std::collections::BTreeSet;

use formalith::{
    context::{Context, Symbol},
    dynamic::Evaluated,
    field::real::{R, Real, numeric::Numeric},
    parser::{Parser, environment::Statement},
    term::{Term, relation::Relation},
};

use crate::Environment;

/// The graph of a line, see the [module documentation](self).
#[derive(Clone, Debug, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Graph {
    /// What to draw.
    pub kind: GraphKind,
    /// The free symbols other than `x` and `y`, by name, whose values follow `x` and `y` in evaluations.
    pub params: Vec<String>,
}

/// The kinds of graphs.
#[derive(Clone, Debug, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum GraphKind {
    /// The curve `y = f(x)`.
    Function {
        /// `f(x)`.
        expr: Numeric,
        /// `f'(x)`, if it can be evaluated.
        derivative: Option<Numeric>,
    },
    /// The curve `x = g(y)`.
    InverseFunction {
        /// `g(y)`.
        expr: Numeric,
    },
    /// The points where every relation `F_i(x, y) op 0` holds: a curve `F(x, y) = 0`, a region, or their
    /// intersections.
    Implicit {
        /// The relations, at least one.
        relations: Vec<ImplicitRelation>,
    },
    /// A point.
    Point {
        /// Its abscissa.
        x: Numeric,
        /// Its ordinate.
        y: Numeric,
    },
}

/// A relation `F(x, y) op 0` of a [`GraphKind::Implicit`] graph.
#[derive(Clone, Debug, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct ImplicitRelation {
    /// `F(x, y)`, the difference of the sides of the relation.
    pub expr: Numeric,
    /// The comparison of `F(x, y)` with 0.
    pub relation: Comparison,
}

impl ImplicitRelation {
    /// Check if the relation holds at the values `values` (see [`Numeric::eval`]).
    #[must_use]
    pub fn holds(&self, values: &[f64]) -> bool {
        self.relation.holds(self.expr.eval(values))
    }
}

/// The comparisons drawn by [`GraphKind::Implicit`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum Comparison {
    /// `= 0`, a curve.
    Equal,
    /// `< 0`
    Less,
    /// `<= 0`
    LessEqual,
    /// `> 0`
    Greater,
    /// `>= 0`
    GreaterEqual,
}

impl Comparison {
    /// The comparison of a relation, `None` for `!=`.
    const fn new(relation: Relation) -> Option<Self> {
        Some(match relation {
            Relation::Equal => Self::Equal,
            Relation::Less => Self::Less,
            Relation::LessEqual => Self::LessEqual,
            Relation::Greater => Self::Greater,
            Relation::GreaterEqual => Self::GreaterEqual,
            Relation::NotEqual => return None,
        })
    }

    /// Check if `value` compares with 0 like this.
    #[must_use]
    pub fn holds(self, value: f64) -> bool {
        match self {
            Self::Equal => value == 0.,
            Self::Less => value < 0.,
            Self::LessEqual => value <= 0.,
            Self::Greater => value > 0.,
            Self::GreaterEqual => value >= 0.,
        }
    }

    /// Check if the comparison excludes its boundary, drawn dashed.
    #[must_use]
    pub const fn is_strict(self) -> bool {
        matches!(self, Self::Less | Self::Greater)
    }
}

impl Graph {
    /// The index of `x` in the values given to evaluations.
    pub const X: usize = 0;
    /// The index of `y` in the values given to evaluations.
    pub const Y: usize = 1;

    /// The name of the first part which can't be evaluated numerically, like `integrate`.
    #[must_use]
    pub fn unsupported(&self) -> Option<&str> {
        match &self.kind {
            GraphKind::Function { expr, .. } | GraphKind::InverseFunction { expr } => {
                expr.unsupported()
            }
            GraphKind::Implicit { relations } => relations
                .iter()
                .find_map(|relation| relation.expr.unsupported()),
            GraphKind::Point { x, y } => x.unsupported().or_else(|| y.unsupported()),
        }
    }
}

/// The variables `x` and `y`.
fn xy() -> (Symbol, Symbol) {
    (Symbol::new("x"), Symbol::new("y"))
}

/// The parameters of `terms`: their symbols other than `excluded` and builtin constants, sorted by name.
fn params<'a>(terms: impl IntoIterator<Item = &'a Term<Real>>, excluded: &[Symbol]) -> Vec<Symbol> {
    let mut params: Vec<Symbol> = terms
        .into_iter()
        .flat_map(Term::symbols)
        .collect::<BTreeSet<_>>()
        .into_iter()
        .filter(|symbol| !excluded.contains(symbol) && !Context::is_builtin_constant(*symbol))
        .collect();
    params.sort_by_key(|symbol| symbol.name());
    params
}

/// Compile `parts` with the variables `[x, y, params...]`, `x` being `var` in place of the symbol `x`.
fn compile_all(
    parts: &[&Term<Real>],
    var: Symbol,
    kind: impl FnOnce(Vec<Numeric>) -> GraphKind,
) -> Graph {
    profile_scope!("compile graph");
    let (x, y) = xy();
    let params = params(parts.iter().copied(), &[var, x, y]);
    let vars: Vec<Symbol> = [var, y].into_iter().chain(params.iter().copied()).collect();
    Graph {
        kind: kind(
            parts
                .iter()
                .map(|part| Numeric::compile(part, &vars))
                .collect(),
        ),
        params: params.iter().map(|param| param.name().to_owned()).collect(),
    }
}

/// Compile `parts` with the variables `[x, y, params...]`, `x` being `var` in place of the symbol `x`.
fn compile<const N: usize>(
    parts: [&Term<Real>; N],
    var: Symbol,
    kind: impl FnOnce([Numeric; N]) -> GraphKind,
) -> Graph {
    compile_all(&parts, var, |compiled| {
        kind(compiled.try_into().expect("One expression per part"))
    })
}

/// The graph of `y = f(x)`, `x` being `var`.
fn function(f: &Term<Real>, var: Symbol) -> Graph {
    let derivative = f.derivative(var);
    let mut graph = compile([f, &derivative], var, |[expr, derivative]| {
        GraphKind::Function {
            expr,
            derivative: Some(derivative),
        }
    });
    if let GraphKind::Function { derivative, .. } = &mut graph.kind
        && derivative
            .as_ref()
            .is_some_and(|derivative| derivative.unsupported().is_some())
    {
        *derivative = None;
    }
    graph
}

/// The graph of a relation `lhs op rhs`, if it depends on `x` or `y`.
fn relation_graph(lhs: &Term<Real>, relation: Relation, rhs: &Term<Real>) -> Option<Graph> {
    let (x, y) = xy();
    let is = |term: &Term<Real>, symbol| matches!(term, Term::Symbol(s) if s.symbol() == symbol);
    let free_of = |term: &Term<Real>, symbol| !term.symbols().contains(&symbol);
    let comparison = Comparison::new(relation)?;
    if !(free_of(lhs, x) && free_of(rhs, x) && free_of(lhs, y) && free_of(rhs, y)) {
        if comparison == Comparison::Equal {
            for (side, other) in [(lhs, rhs), (rhs, lhs)] {
                if is(side, y) && free_of(other, y) {
                    return Some(function(other, x));
                }
                if is(side, x) && free_of(other, x) {
                    return Some(compile([other], x, |[expr]| GraphKind::InverseFunction {
                        expr,
                    }));
                }
            }
        }
        return region_graph(&[(lhs, relation, rhs)]);
    }
    None
}

/// The graph of the region where every relation `lhs op rhs` holds, `!=` relations being left out, if there are
/// other ones.
fn region_graph(relations: &[(&Term<Real>, Relation, &Term<Real>)]) -> Option<Graph> {
    let (comparisons, differences): (Vec<Comparison>, Vec<Term<Real>>) = relations
        .iter()
        .filter_map(|(lhs, relation, rhs)| Some((Comparison::new(*relation)?, *lhs - *rhs)))
        .unzip();
    if comparisons.is_empty() {
        return None;
    }
    let differences: Vec<&Term<Real>> = differences.iter().collect();
    Some(compile_all(&differences, xy().0, |exprs| {
        GraphKind::Implicit {
            relations: exprs
                .into_iter()
                .zip(comparisons)
                .map(|(expr, relation)| ImplicitRelation { expr, relation })
                .collect(),
        }
    }))
}

/// The index of the closing bracket matching the opening one at the start of `text`.
fn closing_bracket(text: &str) -> Option<usize> {
    let mut depth = 0_usize;
    for (i, c) in text.char_indices() {
        match c {
            '(' | '[' | '{' => depth += 1,
            ')' | ']' | '}' => {
                depth = depth.checked_sub(1)?;
                if depth == 0 {
                    return Some(i);
                }
            }
            _ => {}
        }
    }
    None
}

/// The byte indices of the characters of `text` outside of brackets.
fn top_level(text: &str) -> impl Iterator<Item = (usize, char)> + '_ {
    let mut depth = 0_i32;
    text.char_indices().filter(move |&(_, c)| {
        let top = depth == 0;
        match c {
            '(' | '[' | '{' => depth += 1,
            ')' | ']' | '}' => depth -= 1,
            _ => return top,
        }
        false
    })
}

/// The coordinates of a point `point(a, b)` or `(a, b)`.
fn split_point(line: &str) -> Option<(&str, &str)> {
    let start = if line.starts_with("point") {
        let rest = line["point".len()..].trim_start();
        line.len() - rest.len()
    } else {
        0
    };
    let inner = &line[start..];
    if !inner.starts_with('(') || closing_bracket(inner)? != inner.len() - 1 {
        return None;
    }
    let inner = &inner[1..inner.len() - 1];
    let mut commas = top_level(inner).filter(|&(_, c)| c == ',');
    let (comma, _) = commas.next()?;
    if commas.next().is_some() {
        return None;
    }
    Some((&inner[..comma], &inner[comma + 1..]))
}

/// The sides of a single relation `lhs op rhs`, outside of brackets, `None` for definitions, systems and chains of
/// relations.
fn split_relation(line: &str) -> Option<(&str, Relation, &str)> {
    let bytes = line.as_bytes();
    let mut found = None;
    for (i, c) in top_level(line) {
        let next = bytes.get(i + 1).copied();
        let (relation, len) = match c {
            ',' => return None,
            ':' if next == Some(b'=') => return None,
            '!' if next == Some(b'=') => (Relation::NotEqual, 2),
            '<' if next == Some(b'=') => (Relation::LessEqual, 2),
            '>' if next == Some(b'=') => (Relation::GreaterEqual, 2),
            '<' => (Relation::Less, 1),
            '>' => (Relation::Greater, 1),
            '=' if i > 0 && b"<>!:".contains(&bytes[i - 1]) => continue,
            '=' => (Relation::Equal, 1),
            _ => continue,
        };
        if found.is_some() {
            return None;
        }
        found = Some((&line[..i], relation, &line[i + len..]));
    }
    found
}

/// The relations of a line of comma-separated relations, outside of brackets, `None` if a part isn't a single
/// relation.
fn split_relations(line: &str) -> Option<Vec<(&str, Relation, &str)>> {
    let mut parts = vec![];
    let mut start = 0;
    for (i, c) in top_level(line).chain([(line.len(), ',')]) {
        if c == ',' {
            parts.push(split_relation(&line[start..i])?);
            start = i + 1;
        }
    }
    Some(parts)
}

/// Parse an expression in `R` with the definitions of `env`.
fn parse(input: &str, env: &Environment) -> Result<Term<Real>, String> {
    Parser::new(input)
        .with_environment(env)
        .parse(R)
        .map_err(|err| err.to_string())
}

/// Evaluate a line in `R`, which isn't a command, with its graph.
///
/// Relations in `y` are kept as they are rather than solved; others are solved, and drawn like relations. Several
/// relations, one of them an inequality, are drawn as the region where they all hold, and solved if possible,
/// else kept as they are.
///
/// # Errors
/// Returns the parsing error message if `line` is not a valid statement.
///
/// # Panics
/// Panics if an operation is not supported.
pub(crate) fn evaluate(
    line: &str,
    env: &mut Environment,
) -> Result<(Evaluated, Option<Graph>), String> {
    let (x, y) = xy();
    if let Some((a, b)) = split_point(line) {
        let (a, b) = (parse(a, env)?, parse(b, env)?);
        let graph = compile([&a, &b], x, |[x, y]| GraphKind::Point { x, y });
        return Ok((Evaluated::point(a, b), Some(graph)));
    }
    if let Some((lhs, relation, rhs)) = split_relation(line) {
        let (lhs, rhs) = (parse(lhs, env)?, parse(rhs, env)?);
        let graph = relation_graph(&lhs, relation, &rhs);
        if lhs.symbols().contains(&y) || rhs.symbols().contains(&y) {
            return Ok((Evaluated::relation(lhs, relation, rhs), graph));
        }
        let statement = env.eval(line, R).map_err(|err| err.to_string())?;
        return Ok((Evaluated::new(statement), graph));
    }
    if let Some(relations) = split_relations(line)
        && relations
            .iter()
            .any(|(_, relation, _)| *relation != Relation::Equal)
    {
        let relations = relations
            .into_iter()
            .map(|(lhs, relation, rhs)| Ok((parse(lhs, env)?, relation, parse(rhs, env)?)))
            .collect::<Result<Vec<_>, String>>()?;
        let graph = region_graph(
            &relations
                .iter()
                .map(|(lhs, relation, rhs)| (lhs, *relation, rhs))
                .collect::<Vec<_>>(),
        );
        let evaluated = match env.eval(line, R) {
            Ok(statement) => Evaluated::new(statement),
            Err(_) => Evaluated::relations(relations),
        };
        return Ok((evaluated, graph));
    }
    let statement = env.eval(line, R).map_err(|err| err.to_string())?;
    let graph = match &statement {
        Statement::Expression(term) => {
            let symbols = term.symbols();
            (symbols.contains(&x) && !symbols.contains(&y)).then(|| function(term, x))
        }
        Statement::Definition { params, body, .. } => match params.as_slice() {
            [param] => Some(function(body, *param)),
            [] if body.symbols().contains(&x) && !body.symbols().contains(&y) => {
                Some(function(body, x))
            }
            _ => None,
        },
        _ => None,
    };
    Ok((Evaluated::new(statement), graph))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_split() {
        assert_eq!(split_point("point(1, 2)"), Some(("1", " 2")));
        assert_eq!(split_point("(a, f(1, 2))"), Some(("a", " f(1, 2)")));
        assert_eq!(split_point("(x + 1)(x - 1)"), None);
        assert_eq!(split_point("(1, 2, 3)"), None);
        assert_eq!(
            split_relation("y = x^2"),
            Some(("y ", Relation::Equal, " x^2"))
        );
        assert_eq!(
            split_relation("y <= x"),
            Some(("y ", Relation::LessEqual, " x"))
        );
        assert_eq!(split_relation("f(x) := x"), None);
        assert_eq!(split_relation("x + y = 1, x = 2"), None);
        assert_eq!(split_relation("0 < x < 1"), None);
        assert_eq!(split_relation("piecewise(x < 0, 1, 2)"), None);
        assert_eq!(
            split_relations("x > 0, f(x, y) < 1"),
            Some(vec![
                ("x ", Relation::Greater, " 0"),
                (" f(x, y) ", Relation::Less, " 1")
            ])
        );
        assert_eq!(split_relations("x > 0, y"), None);
        assert_eq!(split_relations("a := 1, x > 0"), None);
    }
}
