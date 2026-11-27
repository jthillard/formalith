//! Inequalities checked against their definition: points sampled in the region of the result satisfy every
//! relation, and random points are in the region exactly when they satisfy every relation (away from the
//! boundaries, where rounding decides).

use crate::common::{
    harness::{Verdict, assert_pass, case_rng, check_all, fuzz},
    numeric::{Domain, decimal, eval, number, split_top, symbols},
    random,
    rng::Rng,
};
use formalith::parser::environment::Environment;
use std::time::Duration;

/// Random points tested for membership.
const POINTS: usize = 40;
/// Points sampled in each line of the region.
const REGION_SAMPLES: usize = 8;
/// Distance to the boundaries under which a point isn't tested.
const MARGIN: f64 = 1e-6;
/// Tolerance of equations at points sampled in the region.
const TOLERANCE: f64 = 1e-9;

/// A comparison of a relation.
#[derive(Clone, Copy, Debug, PartialEq)]
enum Op {
    Less,
    LessEqual,
    Greater,
    GreaterEqual,
    Equal,
    NotEqual,
}

impl Op {
    /// Whether `d op 0`, `d` being far enough from 0.
    fn holds(self, d: f64) -> bool {
        match self {
            Self::Less | Self::LessEqual => d < 0.0,
            Self::Greater | Self::GreaterEqual => d > 0.0,
            Self::Equal => d == 0.0,
            Self::NotEqual => d != 0.0,
        }
    }
}

/// A relation `lhs - rhs op 0`.
#[derive(Clone, Debug)]
struct Relation {
    difference: String,
    op: Op,
}

/// The relations and unknowns of the statement `input`: comma-separated relations, or `solve(relations..., x, y)`.
fn statement(input: &str) -> (Vec<Relation>, Vec<String>) {
    let inner = input
        .strip_prefix("solve(")
        .and_then(|s| s.strip_suffix(')'))
        .unwrap_or(input);
    let mut relations = vec![];
    let mut unknowns = vec![];
    for item in split_top(inner, ',') {
        let op = [
            ("<=", Op::LessEqual),
            (">=", Op::GreaterEqual),
            ("!=", Op::NotEqual),
            ("<", Op::Less),
            (">", Op::Greater),
            ("=", Op::Equal),
        ]
        .into_iter()
        .find_map(|(text, op)| item.split_once(text).map(|parts| (parts, op)));
        match op {
            Some(((lhs, rhs), op)) => relations.push(Relation {
                difference: format!("({}) - ({})", lhs.trim(), rhs.trim()),
                op,
            }),
            None => unknowns.push(item),
        }
    }
    if unknowns.is_empty() {
        let all: Vec<String> = relations.iter().map(|r| r.difference.clone()).collect();
        unknowns = symbols(&all.join(" + "));
        unknowns.sort();
    }
    (relations, unknowns)
}

/// One piece of the union of an unknown: an interval (whether its ends are closed doesn't matter, points near
/// the boundaries being skipped), or a point.
#[derive(Clone, Debug)]
enum Piece {
    Interval {
        lo: Option<String>,
        hi: Option<String>,
    },
    Point(String),
}

/// The values of an unknown in a line of the region.
#[derive(Clone, Debug)]
enum Values {
    Union(Vec<Piece>),
    Equal(String),
}

/// A line of the region: the values of each unknown, in order, the bounds depending on the previous ones.
type Line = Vec<(String, Values)>;

/// The region printed in `output`, `None` for `no solution`, the empty line for `true`.
fn region(output: &str) -> Result<Vec<Line>, String> {
    if output == "no solution" {
        return Ok(vec![]);
    }
    if output == "true" {
        return Ok(vec![vec![]]);
    }
    let mut lines = vec![];
    for text in output.lines() {
        let mut line = vec![];
        for item in split_top(text, ',') {
            if let Some((x, union)) = item.split_once(" ∈ ") {
                line.push((
                    x.trim().to_owned(),
                    Values::Union(union_pieces(union.trim())?),
                ));
            } else if let Some((x, value)) = item.split_once(" = ") {
                line.push((x.trim().to_owned(), Values::Equal(value.trim().to_owned())));
            } else {
                return Err(format!("bad item `{item}` in `{text}`"));
            }
        }
        lines.push(line);
    }
    Ok(lines)
}

/// The pieces of a union like `(-oo, 1) ∪ {2} ∪ [3, oo)` or `ℝ`.
fn union_pieces(union: &str) -> Result<Vec<Piece>, String> {
    union
        .split(" ∪ ")
        .map(|piece| {
            let piece = piece.trim();
            if piece == "ℝ" {
                return Ok(Piece::Interval { lo: None, hi: None });
            }
            if let Some(point) = piece.strip_prefix('{').and_then(|p| p.strip_suffix('}')) {
                return Ok(Piece::Point(point.to_owned()));
            }
            let inner = &piece[1..piece.len() - 1];
            let [lo, hi]: [String; 2] = split_top(inner, ',')
                .try_into()
                .map_err(|_| format!("bad interval `{piece}`"))?;
            let bound = |b: String| (b != "+oo" && b != "-oo").then_some(b);
            Ok(Piece::Interval {
                lo: bound(lo),
                hi: bound(hi),
            })
        })
        .collect()
}

/// The value of `expr` with the unknowns of `env` defined.
fn value_in(env: &Environment, expr: &str) -> Option<f64> {
    number(env, expr)
}

/// Define `x := v` in `env`.
fn define(env: &mut Environment, x: &str, v: &str) -> bool {
    eval(env, &format!("{x} := ({v})")).is_ok()
}

/// Whether the point of `env` is in `line`, `None` when it is too close to a bound to tell.
fn line_contains(env: &Environment, line: &Line, point: &[(String, f64)]) -> Option<bool> {
    let mut defined = Environment::new();
    for (x, values) in line {
        let v = point.iter().find(|(y, _)| y == x)?.1;
        let inside = match values {
            Values::Equal(e) => {
                let e = value_in(&defined, e)?;
                if (v - e).abs() < MARGIN {
                    return None;
                }
                false
            }
            Values::Union(pieces) => {
                let mut inside = false;
                for piece in pieces {
                    match piece {
                        Piece::Point(p) => {
                            if (v - value_in(&defined, p)?).abs() < MARGIN {
                                return None;
                            }
                        }
                        Piece::Interval { lo, hi } => {
                            let lo = match lo {
                                Some(lo) => value_in(&defined, lo)?,
                                None => f64::NEG_INFINITY,
                            };
                            let hi = match hi {
                                Some(hi) => value_in(&defined, hi)?,
                                None => f64::INFINITY,
                            };
                            if (v - lo).abs() < MARGIN || (v - hi).abs() < MARGIN {
                                return None;
                            }
                            inside |= lo < v && v < hi;
                        }
                    }
                }
                inside
            }
        };
        if !inside {
            return Some(false);
        }
        // The exact value of the point, from `env`
        let exact = eval(&mut env.clone(), x).ok()?;
        define(&mut defined, x, &exact);
    }
    Some(true)
}

/// Check the inequalities of `input`.
fn inequalities(input: &str) -> Verdict {
    let output = match eval(&mut Environment::new(), input) {
        Ok(output) => output,
        Err(e) => return Verdict::Skip(e),
    };
    verify(input, &output)
}

/// Check that `output` is the solution of the inequalities `input`.
fn verify(input: &str, output: &str) -> Verdict {
    let (relations, mut unknowns) = statement(input);
    let lines = match region(output) {
        Ok(lines) => lines,
        Err(e) => return Verdict::Wrong(format!("{e} in `{output}`")),
    };
    if let Some(line) = lines.first().filter(|line| !line.is_empty()) {
        unknowns = line.iter().map(|(x, _)| x.clone()).collect();
    }
    let mut rng = case_rng(input);
    let mut checked = 0;
    // Points of the region satisfy the relations
    for line in &lines {
        for _ in 0..REGION_SAMPLES {
            if let Some((env, point)) = sample_line(line, &mut rng) {
                match check_relations(&env, &relations, false) {
                    Some(Ok(())) => checked += 1,
                    Some(Err(e)) => {
                        return Verdict::Wrong(format!(
                            "{} is in the region, but {e}",
                            show(&point)
                        ));
                    }
                    None => {}
                }
            }
        }
    }
    // Random points satisfying the relations are in the region, the others aren't
    let only_inequalities = relations.iter().all(|r| r.op != Op::Equal);
    for _ in 0..POINTS {
        let mut env = Environment::new();
        let mut point = vec![];
        for x in &unknowns {
            let v = Domain::Range(-4.0, 4.0).sample(&mut rng);
            define(&mut env, x, &v);
            let Some(f) = value_in(&env, x) else {
                return Verdict::Skip(format!("can't evaluate `{x}`"));
            };
            point.push((x.clone(), f));
        }
        let holds = match check_relations(&env, &relations, true) {
            Some(Ok(())) => true,
            Some(Err(_)) => false,
            None => continue,
        };
        let mut inside = Some(false);
        for line in &lines {
            match line_contains(&env, line, &point) {
                Some(true) => {
                    inside = Some(true);
                    break;
                }
                Some(false) => {}
                None => inside = None,
            }
        }
        let Some(inside) = inside else {
            continue;
        };
        if holds && !inside && only_inequalities {
            return Verdict::Wrong(format!(
                "{} satisfies every relation but isn't in the region `{output}`",
                show(&point)
            ));
        }
        if !holds && inside {
            return Verdict::Wrong(format!(
                "{} is in the region `{output}` but doesn't satisfy every relation",
                show(&point)
            ));
        }
        checked += 1;
    }
    if checked > 0 {
        Verdict::Pass
    } else {
        Verdict::Skip(format!("nothing checked in `{output}`"))
    }
}

/// A point as `x = 1/2, y = -3`.
fn show(point: &[(String, f64)]) -> String {
    let parts: Vec<_> = point.iter().map(|(x, v)| format!("{x} = {v}")).collect();
    parts.join(", ")
}

/// Whether every relation holds at the point of `env`: `Some(Err(why))` when one doesn't, `None` when a value
/// can't be computed or, with `margin`, is too close to 0 to tell.
fn check_relations(
    env: &Environment,
    relations: &[Relation],
    margin: bool,
) -> Option<Result<(), String>> {
    let mut result = Ok(());
    for relation in relations {
        let d = value_in(env, &relation.difference)?;
        let ok = if margin {
            if d.abs() < MARGIN {
                return None;
            }
            relation.op.holds(d)
        } else {
            // A point of the region, on the boundary for non-strict relations and equations
            match relation.op {
                Op::Less => d < TOLERANCE,
                Op::LessEqual => d <= TOLERANCE,
                Op::Greater => d > -TOLERANCE,
                Op::GreaterEqual => d >= -TOLERANCE,
                Op::Equal => d.abs() <= TOLERANCE,
                Op::NotEqual => true,
            }
        };
        if !ok && result.is_ok() {
            result = Err(format!(
                "`{} {:?} 0` doesn't hold ({d})",
                relation.difference, relation.op
            ));
        }
    }
    Some(result)
}

/// A point of `line`, inside its intervals, as definitions in an environment.
fn sample_line(line: &Line, rng: &mut Rng) -> Option<(Environment, Vec<(String, f64)>)> {
    let mut env = Environment::new();
    let mut point = vec![];
    for (x, values) in line {
        let v = match values {
            Values::Equal(e) => e.clone(),
            Values::Union(pieces) => match rng.pick(pieces) {
                Piece::Point(p) => p.clone(),
                Piece::Interval { lo, hi } => {
                    let lo = lo.as_ref().map(|lo| value_in(&env, lo));
                    let hi = hi.as_ref().map(|hi| value_in(&env, hi));
                    let width = f64::from(rng.range(1, 5) as i32);
                    let (lo, hi) = match (lo, hi) {
                        (Some(Some(lo)), Some(Some(hi))) => (lo, hi),
                        (Some(Some(lo)), None) => (lo, lo + width),
                        (None, Some(Some(hi))) => (hi - width, hi),
                        (None, None) => (-width, width),
                        _ => return None,
                    };
                    if hi - lo < 1e-6 {
                        return None;
                    }
                    // Often near the ends, where wrong bounds show
                    let t = if rng.chance(0.5) {
                        let near = 0.01 + 0.05 * f64::from(rng.range(0, 100) as i32) / 100.0;
                        if rng.chance(0.5) { near } else { 1.0 - near }
                    } else {
                        0.05 + 0.9 * f64::from(rng.range(0, 1000) as i32) / 1000.0
                    };
                    decimal(lo + (hi - lo) * t)
                }
            },
        };
        if !define(&mut env, x, &v) {
            return None;
        }
        point.push((x.clone(), value_in(&env, x)?));
    }
    Some((env, point))
}

#[test]
fn oracle_detects_wrong_regions() {
    let wrong = |input: &str, output: &str| matches!(verify(input, output), Verdict::Wrong(_));
    assert!(wrong("x^2 < 4", "x ∈ (-2, 3)"));
    assert!(wrong("x^2 < 4", "x ∈ (-1, 2)"));
    assert!(wrong("x^2 > 1", "x ∈ (1, +oo)"));
    assert!(wrong("x^2 + y^2 < 1", "x ∈ (-1, 1), y ∈ (-1, 1)"));
    assert!(wrong("x^2 = 4, x > 0", "x = -2"));
    assert!(wrong("x^2 + 1 > 0", "no solution"));
    assert!(wrong("x^2 < 0", "true"));
    assert!(matches!(
        verify(
            "x^2 + y^2 <= 1",
            "x ∈ [-1, 1], y ∈ [-((-(x^2)+1)^(1/2)), (-(x^2)+1)^(1/2)]"
        ),
        Verdict::Pass
    ));
}

#[test]
fn curated_inequalities() {
    check_all(
        "inequalities",
        &[
            "x^2 - 3*x + 2 > 0",
            "x^2 <= 4",
            "(x-1)/(x+2) >= 0",
            "x^2 >= 0",
            "x^2*(x-1) >= 0",
            "x != 1",
            "x^2 < 2",
            "x^3 - 2*x < 1",
            "x > 0, x^2 < 4",
            "x^2 - 2 > 0, x < 0",
            "x^2 = 4, x > 0",
            "solve(x^3 < x, x)",
            "x > 0, y > 0",
            "x^2 + y^2 < 1",
            "x^2 + y^2 <= 1",
            "y > x^2, y < 1",
            "x*y > 0",
            "y^2 > x",
            "x + y = 1, x != y",
            "solve(x^2 + y^2 < 1, y, x)",
            "x^2 + y^2 + z^2 < 1",
            "x^2 + 1 > 0",
        ],
        inequalities,
    );
}

/// A random comparison.
fn op(rng: &mut Rng) -> &'static str {
    rng.pick(&["<", "<=", ">", ">=", "!="])
}

/// A random relation in `x`: products of linear factors, rational functions, polynomials against constants.
fn univariate(rng: &mut Rng) -> String {
    match rng.below(4) {
        0 => {
            let count = rng.range(1, 4) as usize;
            format!("{} {} 0", random::linear_factors(rng, "x", count), op(rng))
        }
        1 => {
            let (p, q) = (rng.range(1, 2) as usize, rng.range(1, 2) as usize);
            format!(
                "({})/({}) {} 0",
                random::linear_factors(rng, "x", p),
                random::linear_factors(rng, "x", q),
                op(rng)
            )
        }
        2 => {
            let degree = rng.range(2, 4) as usize;
            let p = random::univariate(rng, "x", degree, 4);
            format!("{p} {} {}", op(rng), rng.range(-5, 5))
        }
        _ => format!(
            "x^2 {} {}, {} {} 0",
            op(rng),
            rng.range(1, 9),
            random::linear(rng, "x"),
            op(rng)
        ),
    }
}

/// A random system in `x`, `y`.
fn bivariate(rng: &mut Rng) -> String {
    let c = rng.range(1, 6);
    match rng.below(6) {
        0 => format!("x^2 + {}*y^2 {} {c}", rng.range(1, 3), op(rng)),
        1 => {
            let p = random::univariate(rng, "x", 2, 3);
            format!("y {} {p}, y {} {c}", op(rng), op(rng))
        }
        2 => format!("x*y {} {}", op(rng), rng.range(-3, 3)),
        3 => format!("y^2 {} x + {}", op(rng), rng.range(-2, 2)),
        4 => format!(
            "{} + {}*y {} 0, x - y {} {}",
            random::linear(rng, "x"),
            rng.nonzero(3),
            op(rng),
            op(rng),
            rng.range(-2, 2)
        ),
        _ => format!(
            "x + {}*y = {}, x^2 {} {c}",
            rng.nonzero(3),
            rng.range(-3, 3),
            op(rng)
        ),
    }
}

/// Harder systems: products of factors, shifted circles, rational relations, three unknowns.
fn mixed(rng: &mut Rng) -> String {
    let (a, b, c) = (rng.range(-2, 2), rng.range(-2, 2), rng.range(1, 4));
    match rng.below(6) {
        0 => format!("(x - {a})*(y - {b})*(x + y) {} 0", op(rng)),
        1 => format!("(x - {a})^2 + (y - {b})^2 {} {c}, y {} x", op(rng), op(rng)),
        2 => format!("(y - {a})/(x - {b}) {} {c}", op(rng)),
        3 => format!("y^2 {} x^3 - {c}*x + {a}", op(rng)),
        4 => format!("x^2 + y^2 + z^2 {} {c}, z {} x + y", op(rng), op(rng)),
        _ => format!("x*y {} {c}, x + y {} {}", op(rng), op(rng), a + b),
    }
}

#[test]
#[ignore = "fuzz: harder systems, run with --ignored"]
fn fuzz_mixed() {
    fuzz("fuzz mixed inequalities", 60, mixed, inequalities);
}

#[test]
#[ignore = "fuzz: random inequalities in one unknown, run with --ignored"]
fn fuzz_univariate() {
    fuzz(
        "fuzz univariate inequalities",
        100,
        univariate,
        inequalities,
    );
}

#[test]
#[ignore = "fuzz: random inequalities in two unknowns, run with --ignored"]
fn fuzz_bivariate() {
    fuzz("fuzz bivariate inequalities", 60, bivariate, inequalities);
}

fn regression(input: &str) {
    assert_pass(input, Duration::from_secs(60), inequalities);
}

#[test]
fn bug_sector_sampled_at_a_rounded_root() {
    // The sector `{$(-3/2, -4/3)$}` was sampled at `{$-4/3$}`, inside the interval between the approximations
    regression("y < -2*x - 3, y < x + 1");
    regression("(-2*x + -3) + -1*y != 0, x - y > -1");
}

#[test]
fn bug_vanishing_coefficients_over_sections() {
    // Over the roots of `{$x^3 - 3x + 1$}`, `{$y^2 - (x^3 - 3x + 1)$}` had roots `{$plus.minus sqrt(0)$}` with an
    // unsimplified zero, which couldn't be approximated. Over `{$x_0 = 2 cos(10 pi/9)$}`, the radicand
    // `{$8 cos(10 pi/9)^3 - 6 cos(10 pi/9) + 1$}` is proven zero by writing `{$cos(a)^3$}` as a sum
    regression("y^2 < x^3 - 3*x + 1");
    regression("y^2 >= x^3 - x - 2");
}

#[test]
fn bug_rational_coefficients_over_sections() {
    // Over a root of `{$256 x^4 - 256 x^3 - 1573$}`, the constant coefficient of `{$256 y^4 + 1280 y^2 + c$}` was
    // `{$c = 1600$}` written with nested radicals, on which `solve_for` didn't finish
    regression("y^4 + 5*y^2 + x^4 - x^3 + 27/256 < 0");
}
