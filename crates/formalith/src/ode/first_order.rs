//! First-order equations, solved for `{$y'$}` then as linear or separable equations.

use malachite::{
    Natural, Rational,
    base::num::{arithmetic::traits::Lcm, basic::traits::One},
};

use crate::{
    context::{Context, Symbol},
    field::real::{
        R,
        expr::{
            Expr, Real, depends, exp_of_ln, fun, map_tree, one, subs, unary, value, variable, zero,
        },
    },
    solve::{Equation, Solution, Solve},
    sum::is_rational_function,
    term::{Expand, Term},
};

use super::{OdeBranch, OdeError, OdeResult, integrate, placeholder, tidy};

/// Solve the first-order equation `{$e(x, y, y') = 0$}`, `y` and `{$y'$}` being the placeholders `@y0` and `@y1`,
/// with the integration constant `c`.
pub(super) fn solve(e: &Expr, x: Symbol, c: Symbol) -> OdeResult<Vec<OdeBranch<Real>>> {
    let (y, y1) = (placeholder(0), placeholder(1));
    let solution = R
        .solve_for(&[Equation::new(e.clone(), zero())], &[y1])
        .map_err(|err| {
            OdeError::Unsupported(format!(
                "can't solve the equation for the derivative: {err}"
            ))
        })?;
    let branches = match solution {
        Solution::NoSolution => vec![],
        Solution::Assignments(assignments) => vec![assignments],
        Solution::Alternatives(branches) => branches,
    };
    let slopes: Vec<_> = branches
        .into_iter()
        .filter_map(|assignments| assignments.into_iter().next().map(|(_, f)| f))
        .collect();
    if slopes.is_empty() {
        return Err(OdeError::Unsupported(
            "the equation doesn't determine the derivative".to_owned(),
        ));
    }
    let mut res = vec![];
    for f in &slopes {
        for branch in solve_explicit(f, x, y, c)? {
            if !res.contains(&branch) {
                res.push(branch);
            }
        }
    }
    Ok(res)
}

/// Solve `{$y' = f(x, y)$}`.
fn solve_explicit(f: &Expr, x: Symbol, y: Symbol, c: Symbol) -> OdeResult<Vec<OdeBranch<Real>>> {
    if let Some(res) = linear(f, x, y, c)? {
        return Ok(vec![res]);
    }
    let split = split(f, x, y).or_else(|| {
        is_rational_function(f)
            .then(|| f.factor())
            .and_then(|f| split(&f, x, y))
    });
    let Some((p, q)) = split else {
        return Err(OdeError::Unsupported(
            "only linear and separable first-order equations can be solved".to_owned(),
        ));
    };
    // `{$integral dy / q(y) = integral p(x) dx + c$}`
    let g = integrate(&(one() / &q), y)?;
    let h = integrate(&p, x)?;
    let mut res = invert(&g, &h, y, c);
    for root in constant_solutions(&q, x, y) {
        // Skip the roots already given by a constant `{$c = 0$}`
        let covered = res.iter().any(|branch| match branch {
            OdeBranch::Explicit(f) => (subs(f, c, &zero()) - &root).expand().is_zero(),
            OdeBranch::Implicit(_) => false,
        });
        if !covered {
            res.push(OdeBranch::Explicit(tidy(&root)));
        }
    }
    Ok(res)
}

/// The constant solutions `{$y = r$}` of a separable equation `{$y' = p(x) q(y)$}`, `r` being the roots of `q`.
fn constant_solutions(q: &Expr, x: Symbol, y: Symbol) -> Vec<Expr> {
    let branches = match R.solve_for(&[Equation::new(q.clone(), zero())], &[y]) {
        Ok(Solution::Assignments(assignments)) => vec![assignments],
        Ok(Solution::Alternatives(branches)) => branches,
        _ => vec![],
    };
    let mut roots: Vec<Expr> = vec![];
    for (_, root) in branches.into_iter().filter_map(|a| a.into_iter().next()) {
        if !depends(&root, x) && !depends(&root, y) && !roots.contains(&root) {
            roots.push(root);
        }
    }
    roots
}

/// Solve the linear equation `{$y' = a(x) y + b(x)$}` with the integrating factor `{$e^(-A)$}`, `{$A = integral a$}`:
/// `{$y = e^A (integral b e^(-A) + c)$}`. Returns `None` if `f` isn't linear in `y`.
fn linear(f: &Expr, x: Symbol, y: Symbol, c: Symbol) -> OdeResult<Option<OdeBranch<Real>>> {
    let a = f.derivative(y);
    if depends(&a, y) {
        return Ok(None);
    }
    let b = subs(f, y, &zero());
    // `{$e^A$}` is only needed up to a constant factor
    let big_a = without_abs_in_ln(&integrate(&a, x)?);
    let factor = exp_of_ln(&fun(Context::EXP, -big_a.clone()));
    let inverse = exp_of_ln(&fun(Context::EXP, big_a));
    let integral = integrate(&(b * factor), x)?;
    Ok(Some(OdeBranch::Explicit(tidy(
        &(inverse * (integral + variable(c))),
    ))))
}

/// Write `f` as `{$p(x) q(y)$}`, splitting products and exponentials of sums.
fn split(f: &Expr, x: Symbol, y: Symbol) -> Option<(Expr, Expr)> {
    let (mut p, mut q) = (one(), one());
    let factors: Vec<Expr> = match f {
        Term::Mul(mul) => {
            p = value(mul.coefficient.clone());
            mul.iter().cloned().collect()
        }
        _ => vec![f.clone()],
    };
    for factor in factors {
        match (depends(&factor, x), depends(&factor, y)) {
            (_, false) => p *= factor,
            (false, true) => q *= factor,
            (true, true) => {
                // `{$e^(u(x) + v(y)) = e^u e^v$}`
                let (Context::EXP, Term::Add(add)) = unary(&factor)? else {
                    return None;
                };
                let (mut u, mut v) = (zero(), zero());
                for term in add {
                    match (depends(term, x), depends(term, y)) {
                        (_, false) => u += term,
                        (false, true) => v += term,
                        (true, true) => return None,
                    }
                }
                p *= fun(Context::EXP, u);
                q *= fun(Context::EXP, v);
            }
        }
    }
    depends(&q, y).then_some((p, q))
}

/// Solve `{$g(y) = h(x) + c$}` for `y`, keeping the equation when it can't be solved.
fn invert(g: &Expr, h: &Expr, y: Symbol, c: Symbol) -> Vec<OdeBranch<Real>> {
    let c_term = variable(c);
    let (lhs, rhs) = if let Some((p, d)) = log_form(g, y) {
        // `{$ln |p^(1/d)| = h + c$}` gives `{$p = c e^(d h)$}`, the new `c` absorbing the sign
        let h = without_abs_in_ln(h);
        (p, c_term * exp_of_ln(&fun(Context::EXP, value(d) * h)))
    } else if let Some((alpha, u)) = exp_form(g, y) {
        (u, fun(Context::LN, (h + &c_term) / value(alpha)))
    } else {
        (g.clone(), h + &c_term)
    };
    if lhs == variable(y) {
        return vec![OdeBranch::Explicit(tidy(&rhs))];
    }
    let solutions = match R.solve_for(&[Equation::new(lhs, rhs)], &[y]) {
        Ok(Solution::Assignments(assignments)) if !assignments.is_empty() => vec![assignments],
        Ok(Solution::Alternatives(branches)) => branches,
        _ => vec![],
    };
    let solutions: Vec<_> = solutions
        .into_iter()
        .filter_map(|assignments| assignments.into_iter().next())
        .map(|(_, f)| OdeBranch::Explicit(tidy(&f)))
        .collect();
    if solutions.is_empty() {
        return vec![OdeBranch::Implicit(Equation::new(
            tidy(g),
            tidy(&(h + &variable(c))),
        ))];
    }
    solutions
}

/// Write `g` as `{$ln |p|^(1/d)$}`, `g` being a sum of rational multiples of logarithms of terms in `y` and `p` a
/// product of their integer powers.
fn log_form(g: &Expr, y: Symbol) -> Option<(Expr, Rational)> {
    let terms: Vec<&Expr> = match g {
        Term::Add(add) => add.iter().collect(),
        _ => vec![g],
    };
    let logs = terms
        .into_iter()
        .map(|term| {
            let (alpha, ln) = match term {
                Term::Mul(mul) => match mul.iter().collect::<Vec<_>>().as_slice() {
                    [ln] => (mul.coefficient.clone(), *ln),
                    _ => return None,
                },
                _ => (Rational::ONE, term),
            };
            let (Context::LN, u) = unary(ln)? else {
                return None;
            };
            let u = match unary(u) {
                Some((Context::ABS, u)) => u,
                _ => u,
            };
            depends(u, y).then(|| (alpha, u.clone()))
        })
        .collect::<Option<Vec<_>>>()?;
    let d = logs
        .iter()
        .fold(Natural::ONE, |d, (alpha, _)| d.lcm(alpha.denominator_ref()));
    let d = Rational::from(d);
    let p = logs
        .into_iter()
        .fold(one(), |p, (alpha, u)| p * u.pow(&value(alpha * &d)));
    Some((p, d))
}

/// Write `g` as `{$alpha e^u$}`, `u` depending on `y`.
fn exp_form(g: &Expr, y: Symbol) -> Option<(Rational, Expr)> {
    let (alpha, exp) = match g {
        Term::Mul(mul) => match mul.iter().collect::<Vec<_>>().as_slice() {
            [exp] => (mul.coefficient.clone(), *exp),
            _ => return None,
        },
        _ => (Rational::ONE, g),
    };
    let (Context::EXP, u) = unary(exp)? else {
        return None;
    };
    depends(u, y).then(|| (alpha, u.clone()))
}

/// Replace `{$ln |u|$}` by `{$ln u$}`, which only changes `{$e^g$}` by a constant factor.
fn without_abs_in_ln(g: &Expr) -> Expr {
    map_tree(g, &|t| match unary(t)? {
        (Context::LN, u) => match unary(u)? {
            (Context::ABS, u) => Some(fun(Context::LN, u.clone())),
            _ => None,
        },
        _ => None,
    })
}
