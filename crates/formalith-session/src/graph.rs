//! Graphs of the lines of a session, for graphical interfaces.
//!
//! Curves `y = f(x)`, `x = g(y)`, implicit curves and
//! regions in `x` and `y` (also intersections of several relations, like `x^2 + y^2 < 1, y > 0`), points, and the
//! areas of definite integrals `integrate(f, x, a, b)`, and surfaces `z = f(x, y)` ([`GraphKind::Surface`]) for
//! expressions in both `x` and `y`, definitions of two parameters and equations `z = f(x, y)`. In `C`, functions
//! `f(z)` are drawn as the images of the lines of a grid, or in 3D as the surface `|f|` colored by `arg f`
//! ([`GraphKind::ComplexMap`]), real ones as surfaces `f(x + i y)`, functions of a real `x` as curves (with their
//! real and imaginary parts when they aren't real, [`GraphKind::ComplexCurve`]), constants as points
//! `(Re, Im)`, and relations between real functions of `z` as regions of the plane `z = x + i y`
//! (`abs(z) < 2, im(z) > 0`). Sequences of `R^N` and recursive definitions in `R` (`u(0) := 1`, `u(n) := 2 u(n - 1) + 1`) are drawn
//! as their points `(k, u_k)` ([`GraphKind::Sequence`]), the other parameters of a definition `f(c, n)` being
//! parameters of the graph.
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
    field::{
        Set,
        complex::{C, Complex, SharedParts, real_parts},
        real::{
            R, Real,
            numeric::{Numeric, free_symbols},
        },
        sequence::{Seq, numeric::NumericSequence},
    },
    parser::{Parser, ParserError, environment::Statement},
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
    /// The curve `y = f(x)` with the area between it and the axis `y = 0` for `x` between `a` and `b`, from a
    /// definite integral `integrate(f, x, a, b)`.
    Integral {
        /// `f(x)`.
        expr: Numeric,
        /// `f'(x)`, if it can be evaluated.
        derivative: Option<Numeric>,
        /// The lower bound, which may depend on the parameters.
        a: Numeric,
        /// The upper bound, which may depend on the parameters.
        b: Numeric,
    },
    /// The surface `z = f(x, y)`.
    Surface {
        /// `f(x, y)`.
        expr: Numeric,
    },
    /// The images under a complex function `f` of the lines of the grid `Re z = k` and `Im z = k` for integers
    /// `k` between `-10` and `10`, in the plane `(Re f, Im f)`, from a function of `z` in `C` which isn't real. In
    /// 3D, the surface of height `|f(x + i y)|` colored by `arg f`. Both parts are evaluated with `x = Re z` and
    /// `y = Im z`.
    ComplexMap {
        /// `Re f(x + i y)`.
        re: Numeric,
        /// `Im f(x + i y)`.
        im: Numeric,
    },
    /// A function `f` of a real `x` with complex values, from a function of `x` (or of a parameter other than `z`)
    /// in `C`: drawn as the curves `y = Re f(x)` and `y = Im f(x)`, or as the path `(Re f(x), Im f(x))`.
    ComplexCurve {
        /// `Re f(x)`.
        re: Numeric,
        /// `Im f(x)`.
        im: Numeric,
        /// `(Re f)'(x)`, if it can be evaluated.
        re_derivative: Option<Numeric>,
        /// `(Im f)'(x)`, if it can be evaluated.
        im_derivative: Option<Numeric>,
    },
    /// The points `(k, u_k)` of a sequence `u`, for the integers `k` where it is defined.
    Sequence {
        /// The sequence, its index being `x`.
        terms: NumericSequence,
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
            GraphKind::Function { expr, .. }
            | GraphKind::InverseFunction { expr }
            | GraphKind::Surface { expr } => expr.unsupported(),
            GraphKind::Implicit { relations } => relations
                .iter()
                .find_map(|relation| relation.expr.unsupported()),
            GraphKind::Integral { expr, a, b, .. } => expr
                .unsupported()
                .or_else(|| a.unsupported())
                .or_else(|| b.unsupported()),
            GraphKind::Sequence { terms } => terms.unsupported(),
            GraphKind::Point { x, y }
            | GraphKind::ComplexMap { re: x, im: y }
            | GraphKind::ComplexCurve { re: x, im: y, .. } => {
                x.unsupported().or_else(|| y.unsupported())
            }
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
        .flat_map(free_symbols)
        .collect::<BTreeSet<_>>()
        .into_iter()
        .filter(|symbol| !excluded.contains(symbol) && !Context::is_builtin_constant(*symbol))
        .collect();
    params.sort_by_key(|symbol| symbol.name());
    params
}

/// Compile `parts` with the variables `[x, y, params...]`, `x` and `y` being `vars` in place of the symbols `x` and
/// `y`.
fn compile_all(
    parts: &[&Term<Real>],
    vars: [Symbol; 2],
    kind: impl FnOnce(Vec<Numeric>) -> GraphKind,
) -> Graph {
    compile_shared(parts, vars, &[], kind)
}

/// Compile `parts` like [`compile_all`], their symbols `bindings[k].0` standing for the terms `bindings[k].1` (see
/// [`SharedParts`]), which aren't parameters.
fn compile_shared(
    parts: &[&Term<Real>],
    [xvar, yvar]: [Symbol; 2],
    bindings: &[(Symbol, Term<Real>)],
    kind: impl FnOnce(Vec<Numeric>) -> GraphKind,
) -> Graph {
    profile_scope!("compile graph");
    let (x, y) = xy();
    let excluded: Vec<Symbol> = [xvar, yvar, x, y]
        .into_iter()
        .chain(bindings.iter().map(|(symbol, _)| *symbol))
        .collect();
    let params = params(
        parts
            .iter()
            .copied()
            .chain(bindings.iter().map(|(_, value)| value)),
        &excluded,
    );
    let vars: Vec<Symbol> = [xvar, yvar]
        .into_iter()
        .chain(params.iter().copied())
        .collect();
    Graph {
        kind: kind(
            parts
                .iter()
                .map(|part| Numeric::compile_shared(part, &vars, bindings))
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
    compile_all(&parts, [var, xy().1], |compiled| {
        kind(compiled.try_into().expect("One expression per part"))
    })
}

/// A compiled derivative, if it can be evaluated.
fn evaluable(derivative: Numeric) -> Option<Numeric> {
    derivative.unsupported().is_none().then_some(derivative)
}

/// The graph of `y = f(x)`, `x` being `var`.
fn function(f: &Term<Real>, var: Symbol) -> Graph {
    let derivative = f.derivative(var);
    compile([f, &derivative], var, |[expr, derivative]| {
        GraphKind::Function {
            expr,
            derivative: evaluable(derivative),
        }
    })
}

/// The surface `z = f(x, y)`, `x` and `y` being `vars`.
fn surface(f: &Term<Real>, vars: [Symbol; 2]) -> Graph {
    compile_all(&[f], vars, |compiled| GraphKind::Surface {
        expr: compiled.into_iter().next().expect("One expression"),
    })
}

/// The graph of a definite integral `integrate(f, var, a, b)`, if `f` only depends on `var` and parameters, and the
/// bounds only on parameters.
#[allow(clippy::many_single_char_names)]
fn integral_graph(line: &str, env: &Environment) -> Option<Graph> {
    let [f, var, a, b] = split_call(line, "integrate")?;
    let Term::Symbol(var) = parse(var, env).ok()? else {
        return None;
    };
    let var = var.symbol();
    let (f, a, b) = (
        parse(f, env).ok()?,
        parse(a, env).ok()?,
        parse(b, env).ok()?,
    );
    let (x, y) = xy();
    let f_symbols = f.symbols();
    if [x, y]
        .into_iter()
        .any(|symbol| symbol != var && f_symbols.contains(&symbol))
    {
        return None;
    }
    for bound in [&a, &b] {
        let symbols = bound.symbols();
        if [var, x, y].iter().any(|symbol| symbols.contains(symbol)) {
            return None;
        }
    }
    let derivative = f.derivative(var);
    Some(compile(
        [&f, &derivative, &a, &b],
        var,
        |[expr, derivative, a, b]| GraphKind::Integral {
            expr,
            derivative: evaluable(derivative),
            a,
            b,
        },
    ))
}

/// The points of a sequence of `R^N` indexed by `index`, `None` for a constant sequence.
fn sequence_graph(term: &Term<Seq<Real>>, index: Symbol) -> Option<Graph> {
    let Term::Value(value) = term else {
        return None;
    };
    let sequence = value.element();
    let symbols = NumericSequence::symbols(sequence);
    if sequence.as_closed().is_some() && !symbols.contains(&index) {
        return None;
    }
    let mut params: Vec<Symbol> = symbols
        .into_iter()
        .filter(|symbol| *symbol != index && !Context::is_builtin_constant(*symbol))
        .collect();
    params.sort_by_key(|symbol| symbol.name());
    Some(Graph {
        kind: GraphKind::Sequence {
            terms: NumericSequence::compile(sequence, index, &params),
        },
        params: params.iter().map(|param| param.name().to_owned()).collect(),
    })
}

/// The points of the sequence defined as `name` by a recursive rule and values at integers, like `u(0) := 1` and
/// `u(n) := 2 u(n - 1) + 1`, `None` if it can't be built yet (a value is missing) or isn't a sequence.
fn defined_sequence(name: Symbol, env: &Environment) -> Option<Graph> {
    let definition = env
        .get(name)
        .filter(|definition| definition.is_sequence())?;
    let index = definition
        .params()
        .get(definition.index())
        .copied()
        .unwrap_or_else(|| Symbol::new("n"));
    let term = Parser::new(name.name())
        .with_environment(env)
        .parse(R.get_sequence_set(index))
        .ok()?;
    sequence_graph(&term, index)
}

/// The graph of a relation `lhs op rhs`, if it depends on `x` or `y`.
fn relation_graph(lhs: &Term<Real>, relation: Relation, rhs: &Term<Real>) -> Option<Graph> {
    let (x, y) = xy();
    let z = Symbol::new("z");
    let is = |term: &Term<Real>, symbol| matches!(term, Term::Symbol(s) if s.symbol() == symbol);
    let free_of = |term: &Term<Real>, symbol| !term.symbols().contains(&symbol);
    let comparison = Comparison::new(relation)?;
    if !(free_of(lhs, x) && free_of(rhs, x) && free_of(lhs, y) && free_of(rhs, y)) {
        if comparison == Comparison::Equal {
            for (side, other) in [(lhs, rhs), (rhs, lhs)] {
                if is(side, z) && free_of(other, z) {
                    return Some(surface(other, [x, y]));
                }
            }
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
    region_graph_shared(relations, &[])
}

/// The graph of the region where every relation holds like [`region_graph`], with the shared subexpressions
/// `bindings` (see [`compile_shared`]).
fn region_graph_shared(
    relations: &[(&Term<Real>, Relation, &Term<Real>)],
    bindings: &[(Symbol, Term<Real>)],
) -> Option<Graph> {
    let (comparisons, differences): (Vec<Comparison>, Vec<Term<Real>>) = relations
        .iter()
        .filter_map(|(lhs, relation, rhs)| Some((Comparison::new(*relation)?, *lhs - *rhs)))
        .unzip();
    if comparisons.is_empty() {
        return None;
    }
    let differences: Vec<&Term<Real>> = differences.iter().collect();
    Some(compile_shared(
        &differences,
        xy().into(),
        bindings,
        |exprs| GraphKind::Implicit {
            relations: exprs
                .into_iter()
                .zip(comparisons)
                .map(|(expr, relation)| ImplicitRelation { expr, relation })
                .collect(),
        },
    ))
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
    let start = line
        .strip_prefix("point")
        .map_or(0, |rest| line.len() - rest.trim_start().len());
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

/// The `N` arguments of a call `name(...)` making up the whole line.
fn split_call<'a, const N: usize>(line: &'a str, name: &str) -> Option<[&'a str; N]> {
    let inner = line.strip_prefix(name)?.trim_start();
    if !inner.starts_with('(') || closing_bracket(inner)? != inner.len() - 1 {
        return None;
    }
    let inner = &inner[1..inner.len() - 1];
    let mut args = vec![];
    let mut start = 0;
    for (i, c) in top_level(inner).chain([(inner.len(), ',')]) {
        if c == ',' {
            args.push(&inner[start..i]);
            start = i + 1;
        }
    }
    args.try_into().ok()
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
fn parse(input: &str, env: &Environment) -> Result<Term<Real>, ParserError> {
    Parser::new(input)
        .with_offset(None)
        .with_environment(env)
        .parse(R)
}

/// Parse an expression in `R` like [`parse`], `input` being a part of `line`, so that errors point at `line`.
fn parse_part(input: &str, line: &str, env: &Environment) -> Result<Term<Real>, ParserError> {
    parse_part_in(input, line, env, R)
}

/// Parse an expression in `set` like [`parse_part`].
fn parse_part_in<T: Set>(
    input: &str,
    line: &str,
    env: &Environment,
    set: T,
) -> Result<Term<T>, ParserError> {
    // The parts of a line are slices of it
    let offset = (input.as_ptr().addr())
        .checked_sub(line.as_ptr().addr())
        .filter(|offset| offset + input.len() <= line.len());
    Parser::new(input)
        .with_offset(offset)
        .with_environment(env)
        .parse(set)
}

/// Evaluate a line in `R`, which isn't a command, with its graph.
///
/// Relations in `y` are kept as they are rather than solved; others are solved, and drawn like relations. Several
/// relations, one of them an inequality, are drawn as the region where they all hold, and solved if possible,
/// else kept as they are.
///
/// # Errors
/// Returns the parsing error if `line` is not a valid statement.
///
/// # Panics
/// Panics if an operation is not supported.
pub(crate) fn evaluate(
    line: &str,
    env: &mut Environment,
) -> Result<(Evaluated, Option<Graph>), ParserError> {
    let (x, y) = xy();
    if let Some((a, b)) = split_point(line) {
        let (a, b) = (parse_part(a, line, env)?, parse_part(b, line, env)?);
        let graph = compile([&a, &b], x, |[x, y]| GraphKind::Point { x, y });
        return Ok((Evaluated::point(a, b), Some(graph)));
    }
    if let Some((lhs, relation, rhs)) = split_relation(line) {
        let (lhs, rhs) = (parse_part(lhs, line, env)?, parse_part(rhs, line, env)?);
        let graph = relation_graph(&lhs, relation, &rhs);
        if lhs.symbols().contains(&y) || rhs.symbols().contains(&y) {
            return Ok((Evaluated::relation(lhs, relation, rhs), graph));
        }
        let statement = env.eval(line, R)?;
        return Ok((Evaluated::new(statement), graph));
    }
    if let Some(relations) = split_relations(line)
        && relations
            .iter()
            .any(|(_, relation, _)| *relation != Relation::Equal)
    {
        let relations = relations
            .into_iter()
            .map(|(lhs, relation, rhs)| {
                Ok((
                    parse_part(lhs, line, env)?,
                    relation,
                    parse_part(rhs, line, env)?,
                ))
            })
            .collect::<Result<Vec<_>, ParserError>>()?;
        let graph = region_graph(
            &relations
                .iter()
                .map(|(lhs, relation, rhs)| (lhs, *relation, rhs))
                .collect::<Vec<_>>(),
        );
        let evaluated = env
            .eval(line, R)
            .map_or_else(|_| Evaluated::relations(relations), Evaluated::new);
        return Ok((evaluated, graph));
    }
    if let Some(graph) = integral_graph(line, env) {
        let statement = env.eval(line, R)?;
        return Ok((Evaluated::new(statement), Some(graph)));
    }
    let statement = env.eval(line, R)?;
    let graph_of = |term: &Term<Real>| {
        let symbols = term.symbols();
        match (symbols.contains(&x), symbols.contains(&y)) {
            (true, false) => Some(function(term, x)),
            (_, true) => Some(surface(term, [x, y])),
            (false, false) => None,
        }
    };
    let graph = match &statement {
        Statement::Expression(term) => graph_of(term),
        Statement::Definition { name, .. }
            if env
                .get(*name)
                .is_some_and(formalith::parser::environment::Definition::is_recursive) =>
        {
            defined_sequence(*name, env)
        }
        // A value at an integer
        Statement::Definition { case: Some(_), .. } => None,
        Statement::Definition { params, body, .. } => match params.as_slice() {
            [param] => Some(function(body, *param)),
            [p, q] => Some(surface(body, [*p, *q])),
            [] => graph_of(body),
            _ => None,
        },
        _ => None,
    };
    Ok((Evaluated::new(statement), graph))
}

/// Evaluate a line in `set`, a set `R^N` of sequences, which isn't a command, with its graph: the points of
/// sequences which aren't constant.
///
/// # Errors
/// Returns the parsing error if `line` is not a valid statement.
///
/// # Panics
/// Panics if an operation is not supported.
pub(crate) fn evaluate_sequence(
    line: &str,
    env: &mut Environment,
    set: Seq<Real>,
) -> Result<(Evaluated, Option<Graph>), ParserError> {
    let statement = env.eval(line, set)?;
    let graph = match &statement {
        Statement::Expression(term) | Statement::Definition { body: term, .. } => {
            sequence_graph(term, set.index())
        }
        _ => None,
    };
    Ok((Evaluated::new(statement), graph))
}

/// The graph of a complex function `f` of `var`, see [`GraphKind::ComplexMap`], or the surface `Re f` when `f` is
/// real.
fn complex_map(f: &Term<Complex>, var: Symbol) -> Option<Graph> {
    let (x, y) = xy();
    let shared = SharedParts::new(var, x, y);
    let (re, im) = shared.parts(f)?;
    let bindings = shared.into_bindings();
    if im.is_zero() {
        return Some(compile_shared(&[&re], [x, y], &bindings, |compiled| {
            GraphKind::Surface {
                expr: compiled.into_iter().next().expect("One expression"),
            }
        }));
    }
    Some(compile_shared(&[&re, &im], [x, y], &bindings, |compiled| {
        let [re, im] = compiled.try_into().expect("Two parts");
        GraphKind::ComplexMap { re, im }
    }))
}

/// The graph of a function `f` of the real `var` in `C`: a curve `y = f(x)` when `f` is real, else a
/// [`GraphKind::ComplexCurve`].
fn complex_function(f: &Term<Complex>, var: Symbol) -> Option<Graph> {
    let (re, im) = real_parts(f)?;
    if im.is_zero() {
        return Some(function(&re, var));
    }
    let (re_derivative, im_derivative) = (re.derivative(var), im.derivative(var));
    Some(compile(
        [&re, &im, &re_derivative, &im_derivative],
        var,
        |[re, im, re_derivative, im_derivative]| GraphKind::ComplexCurve {
            re,
            im,
            re_derivative: evaluable(re_derivative),
            im_derivative: evaluable(im_derivative),
        },
    ))
}

/// The point `(Re c, Im c)` of a constant `c`.
fn complex_point(c: &Term<Complex>) -> Option<Graph> {
    let (re, im) = real_parts(c)?;
    Some(compile([&re, &im], xy().0, |[x, y]| GraphKind::Point {
        x,
        y,
    }))
}

/// The graph of the region of the plane `z = x + i y` where every relation `lhs op rhs` between complex terms
/// holds, `!=` relations being left out, if both sides of every relation are real, like `abs(z) < 2`.
fn complex_region(relations: &[(Term<Complex>, Relation, Term<Complex>)]) -> Option<Graph> {
    let (x, y) = xy();
    // The parts of iterated functions like `f(z, n) = f(z, n - 1)^2 + z` share their subexpressions
    let shared = SharedParts::new(Symbol::new("z"), x, y);
    let differences = relations
        .iter()
        .filter(|(_, relation, _)| *relation != Relation::NotEqual)
        .map(|(lhs, relation, rhs)| {
            let (re, im) = shared.parts(&(lhs - rhs))?;
            im.is_zero().then_some((re, *relation))
        })
        .collect::<Option<Vec<_>>>()?;
    let bindings = shared.into_bindings();
    let zero = Term::zero(R);
    region_graph_shared(
        &differences
            .iter()
            .map(|(re, relation)| (re, *relation, &zero))
            .collect::<Vec<_>>(),
        &bindings,
    )
}

/// Evaluate a line in `C`, which isn't a command, with its graph: the images of a grid under functions of `z` (see
/// [`GraphKind::ComplexMap`]), curves for functions of `x` or of another single parameter of a definition (see
/// [`GraphKind::ComplexCurve`]), points `(Re c, Im c)` for constants `c`, and regions for relations in `z`, `x` or
/// `y` (see [`GraphKind::Implicit`]), kept as they are, which are drawn when their sides are real, like
/// `abs(z - 1) <= re(z)`.
///
/// # Errors
/// Returns the parsing error if `line` is not a valid statement.
///
/// # Panics
/// Panics if an operation is not supported.
pub(crate) fn evaluate_complex(
    line: &str,
    env: &mut Environment,
) -> Result<(Evaluated, Option<Graph>), ParserError> {
    let (x, y) = xy();
    let z = Symbol::new("z");
    let relations = split_relation(line)
        .map(|relation| vec![relation])
        .or_else(|| {
            split_relations(line).filter(|relations| {
                relations
                    .iter()
                    .any(|(_, relation, _)| *relation != Relation::Equal)
            })
        });
    if let Some(relations) = relations {
        let relations = relations
            .into_iter()
            .map(|(lhs, relation, rhs)| {
                Ok((
                    parse_part_in(lhs, line, env, C)?,
                    relation,
                    parse_part_in(rhs, line, env, C)?,
                ))
            })
            .collect::<Result<Vec<_>, ParserError>>()?;
        let variable = relations.iter().any(|(lhs, _, rhs)| {
            [lhs, rhs].into_iter().any(|side| {
                let symbols = side.symbols();
                [x, y, z].iter().any(|symbol| symbols.contains(symbol))
            })
        });
        if variable {
            let graph = complex_region(&relations);
            return Ok((Evaluated::relations(relations), graph));
        }
    }
    let statement = env.eval(line, C)?;
    let graph_of = |term: &Term<Complex>| {
        let symbols = term.symbols();
        match [x, y, z].map(|symbol| symbols.contains(&symbol)) {
            [false, false, true] => complex_map(term, z),
            [true, false, false] => complex_function(term, x),
            [false, false, false] => complex_point(term),
            _ => None,
        }
    };
    let graph = match &statement {
        Statement::Expression(term) => graph_of(term),
        Statement::Definition { case: Some(_), .. } => None,
        Statement::Definition { params, body, .. } => match params.as_slice() {
            [param] if *param == z => complex_map(body, z),
            [param] => complex_function(body, *param),
            [] => graph_of(body),
            _ => None,
        },
        _ => None,
    };
    Ok((Evaluated::new(statement), graph))
}

#[cfg(test)]
mod tests {
    use formalith::printer::PrintOptions;

    use super::*;

    #[test]
    fn test_split() {
        assert_eq!(split_point("point(1, 2)"), Some(("1", " 2")));
        assert_eq!(split_point("(a, f(1, 2))"), Some(("a", " f(1, 2)")));
        assert_eq!(split_point("(x + 1)(x - 1)"), None);
        assert_eq!(split_point("(1, 2, 3)"), None);
        assert_eq!(
            split_call("integrate (f(x, 1), x, 0, 1)", "integrate"),
            Some(["f(x, 1)", " x", " 0", " 1"])
        );
        assert_eq!(split_call::<4>("integrate(x, x)", "integrate"), None);
        assert_eq!(
            split_call::<4>("integrate(x, x, 0, 1) + 1", "integrate"),
            None
        );
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

    #[test]
    fn test_surface() {
        let mut env = Environment::new();
        let surface = |line: &str, env: &mut Environment| {
            let (_, graph) = evaluate(line, env).unwrap();
            let graph = graph.unwrap_or_else(|| panic!("No graph for {line}"));
            let GraphKind::Surface { expr } = graph.kind else {
                panic!("Expected a surface for {line}");
            };
            (expr, graph.params)
        };
        let (expr, params) = surface("x*y", &mut env);
        assert_eq!(expr.eval(&[2., 3.]), 6.);
        assert_eq!(params, Vec::<String>::new());
        let (expr, _) = surface("f(u, v) := u^2 - v", &mut env);
        assert_eq!(expr.eval(&[2., 3.]), 1.);
        let (expr, _) = surface("z = x^2 + y^2", &mut env);
        assert_eq!(expr.eval(&[1., 2.]), 5.);
        let (expr, params) = surface("a*x*y", &mut env);
        assert_eq!(params, ["a"]);
        assert_eq!(expr.eval(&[1., 2., 3.]), 6.);
        // A curve, not a surface
        let (_, graph) = evaluate("y = x^2", &mut env).unwrap();
        assert!(matches!(graph.unwrap().kind, GraphKind::Function { .. }));
        // A `piecewise` keeping an unevaluated integral, whose derivative must not evaluate it again
        let (_, graph) = evaluate("integrate(sqrt(x/r-1),r,1,x)", &mut env).unwrap();
        assert!(matches!(graph.unwrap().kind, GraphKind::Function { .. }));
    }

    #[test]
    fn test_complex_map() {
        let mut env = Environment::new();
        let (_, graph) = evaluate_complex("z^2", &mut env).unwrap();
        let Some(GraphKind::ComplexMap { re, im }) = graph.map(|graph| graph.kind) else {
            panic!("Expected a complex map");
        };
        assert_eq!(re.eval(&[1., 2.]), -3.);
        assert_eq!(im.eval(&[1., 2.]), 4.);
        let (_, graph) = evaluate_complex("f(z) := a/z", &mut env).unwrap();
        let graph = graph.unwrap();
        assert!(matches!(graph.kind, GraphKind::ComplexMap { .. }));
        assert_eq!(graph.params, ["a"]);
        assert!(evaluate_complex("x + y", &mut env).unwrap().1.is_none());
        // Real functions of `z` are surfaces
        let (_, graph) = evaluate_complex("abs(z)", &mut env).unwrap();
        let Some(GraphKind::Surface { expr }) = graph.map(|graph| graph.kind) else {
            panic!("Expected a surface");
        };
        assert!((expr.eval(&[3., 4.]) - 5.).abs() < 1e-12);
        assert!(evaluate_complex("x + z", &mut env).unwrap().1.is_none());
        let (_, graph) = evaluate_complex("sin(x)", &mut env).unwrap();
        assert!(matches!(graph.unwrap().kind, GraphKind::Function { .. }));
        // Large powers: of a real base directly, of `z` in polar form
        let (_, graph) = evaluate_complex("x^17", &mut env).unwrap();
        let Some(GraphKind::Function { expr, .. }) = graph.map(|graph| graph.kind) else {
            panic!("Expected a function");
        };
        assert_eq!(expr.eval(&[-2., f64::NAN]), -131_072.);
        let (_, graph) = evaluate_complex("z^17", &mut env).unwrap();
        let Some(GraphKind::ComplexMap { re, im }) = graph.map(|graph| graph.kind) else {
            panic!("Expected a complex map");
        };
        // `(1 + i)^17 = 256 + 256 i`
        assert!(
            (re.eval(&[1., 1.]) - 256.).abs() < 1e-9 && (im.eval(&[1., 1.]) - 256.).abs() < 1e-9
        );
        for line in ["exp(i*x)", "f(t) := exp(i*t)"] {
            let (_, graph) = evaluate_complex(line, &mut env).unwrap();
            let Some(GraphKind::ComplexCurve { re, im, .. }) = graph.map(|graph| graph.kind) else {
                panic!("Expected a complex curve for {line}");
            };
            assert_eq!(re.eval(&[0., f64::NAN]), 1.);
            assert!((im.eval(&[std::f64::consts::FRAC_PI_2, f64::NAN]) - 1.).abs() < 1e-12);
        }
        for (line, point) in [("i", [0., 1.]), ("1 + 2*i", [1., 2.])] {
            let (_, graph) = evaluate_complex(line, &mut env).unwrap();
            let Some(GraphKind::Point { x, y }) = graph.map(|graph| graph.kind) else {
                panic!("Expected a point for {line}");
            };
            assert_eq!([x.eval(&[]), y.eval(&[])], point);
        }
        // Parts with only a numerical form
        for (line, z, value) in [
            (
                "zeta(z)",
                [2., 1.],
                [1.150_355_703_254_9, -0.437_530_865_919_608],
            ),
            (
                "gamma(z)",
                [1., 1.],
                [0.498_015_668_118_356, -0.154_949_828_301_811],
            ),
            ("ln(z)", [3., 4.], [5f64.ln(), 0.927_295_218_001_612]),
            ("sqrt(z)", [-3., 4.], [1., 2.]),
            ("z^i", [0., 1.], [(-std::f64::consts::FRAC_PI_2).exp(), 0.]),
        ] {
            let (_, graph) = evaluate_complex(line, &mut env).unwrap();
            let Some(GraphKind::ComplexMap { re, im }) = graph.map(|graph| graph.kind) else {
                panic!("Expected a complex map for {line}");
            };
            let (u, v) = (re.eval(&z), im.eval(&z));
            assert!(
                (u - value[0]).abs() < 1e-9 && (v - value[1]).abs() < 1e-9,
                "{line} at {z:?}: {u} + {v} i"
            );
        }
        let (_, graph) = evaluate_complex("zeta(1/2 + i*x)", &mut env).unwrap();
        let Some(GraphKind::ComplexCurve { re, im, .. }) = graph.map(|graph| graph.kind) else {
            panic!("Expected a complex curve for zeta(1/2 + i x)");
        };
        let at_zero = [
            re.eval(&[14.134_725_141_734_693]),
            im.eval(&[14.134_725_141_734_693]),
        ];
        assert!(at_zero.iter().all(|part| part.abs() < 1e-9), "{at_zero:?}");
        let mut session = crate::Session::new();
        session.run(":set C");
        // Symbolic results don't use the numerical parts
        assert_eq!(
            session
                .run("re(zeta(2 + i))")
                .output
                .print(PrintOptions::plain()),
            "re(zeta(2+i))"
        );
        let (response, graph) = session.graph("(z + i)^2");
        assert!(matches!(graph.unwrap().kind, GraphKind::ComplexMap { .. }));
        assert_eq!(
            response.output.print(PrintOptions::plain()),
            session.run("(z + i)^2").output.print(PrintOptions::plain())
        );
    }
}
