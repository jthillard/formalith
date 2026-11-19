//! Integration by substitution `{$u = g(x)$}`, when `{$f / g'$}` is an expression of `u` (derivative-divides).

use crate::field::real::expr::{
    Expr, depends, exp_of_ln, fun, map_tree, one, size, unary, variable,
};
use crate::{
    context::{Context, Symbol},
    term::Term,
};

use super::{Integrator, is_positive, linear, replace_symbol};

/// Maximum number of substitutions tried for an integrand.
const MAX_CANDIDATES: usize = 8;

pub(super) fn integrate(integrator: &mut Integrator, f: &Expr, x: Symbol) -> Option<Expr> {
    let mut candidates = vec![];
    collect_candidates(f, x, &mut candidates);
    // Larger subexpressions first, `{$u = x^2 + 1$}` before `{$u = x^2$}`
    candidates.sort_by_key(|u: &Expr| std::cmp::Reverse(size(u)));
    for u in candidates.iter().take(MAX_CANDIDATES) {
        if let Some(res) = substitute(integrator, f, x, u) {
            return Some(res);
        }
    }
    None
}

/// Subexpressions `u` of `f`, other than `x`: arguments of functions, bases and exponents of powers.
fn collect_candidates(f: &Expr, x: Symbol, candidates: &mut Vec<Expr>) {
    let push = |u: &Expr, candidates: &mut Vec<Expr>| {
        if depends(u, x) && *u != variable(x) && !candidates.contains(u) {
            candidates.push(u.clone());
        }
    };
    match f {
        Term::Value(_) | Term::Symbol(_) => {}
        Term::Add(add) => add
            .iter()
            .for_each(|t| collect_candidates(t, x, candidates)),
        Term::Mul(mul) => mul
            .iter()
            .for_each(|t| collect_candidates(t, x, candidates)),
        Term::Pow(pow) => {
            let (base, exponant) = (&*pow.base, &**pow.exponant);
            if depends(exponant, x) {
                push(exponant, candidates);
            } else if pow.exponant.to_i64().is_none() {
                // `{$u = sqrt(x + 1)$}`, but not `{$u = x^2$}` for `{$x^2 / (x^2 + 1)$}`
                push(f, candidates);
            }
            push(base, candidates);
            collect_candidates(base, x, candidates);
            collect_candidates(exponant, x, candidates);
        }
        Term::Fun(fun) => {
            push(f, candidates);
            for arg in fun.get_args::<super::Real>().into_iter().flatten() {
                push(arg, candidates);
                collect_candidates(arg, x, candidates);
            }
        }
    }
}

/// `{$integral f dif x = integral h(t) dif t$}` with `{$t = u(x)$}`, if `{$f / u'$}` is an expression `h` of `u`.
fn substitute(integrator: &mut Integrator, f: &Expr, x: Symbol, u: &Expr) -> Option<Expr> {
    let du = u.derivative(x);
    if du.is_zero() {
        return None;
    }
    let t_symbol = integrator.fresh_symbol();
    let t = variable(t_symbol);
    let quotient = f / &du;
    let mut h = replace(&quotient, u, &t, x);
    if depends(&h, x) {
        h = replace(&quotient.simplify(), u, &t, x);
    }
    // `{$x = (t - b) / a$}` for a linear `{$u = a x + b$}`, unless `x` already comes from one
    let mut affine = false;
    if depends(&h, x)
        && !integrator.affine.contains(&x)
        && let Some(a) = linear(u, x)
    {
        let b = (u - &(&a * &variable(x))).simplify();
        h = h.substitute(x, &((&t - &b) / a))?;
        affine = true;
    }
    if depends(&h, x) {
        return None;
    }
    if affine {
        integrator.affine.insert(t_symbol);
    }
    let res = integrator.integrate(&h, t_symbol);
    integrator.affine.remove(&t_symbol);
    Some(exp_of_ln(&replace_symbol(&res?, t_symbol, u)))
}

/// Replace `u` by `t` in `term`, also writing related subexpressions as powers of `t`: `{$b^q = t^(q/p)$}` for
/// `{$u = b^p$}` (and `{$b = t^(1/p)$}`) when `{$q / p$}` is an integer or `b` is positive (`{$x = sqrt(x^2)$}`
/// only holds for `{$x >= 0$}`), `{$exp(c) = t^(c/a)$}` for `{$u = exp(a)$}`, and `{$b = exp(t)$}` for `{$u = ln b$}`.
fn replace(term: &Expr, u: &Expr, t: &Expr, x: Symbol) -> Expr {
    map_tree(term, &|s| {
        if s == u {
            return Some(t.clone());
        }
        // `{$b = exp(t)$}` for `{$u = ln b$}`, `b` being positive
        if let Some((Context::LN, b)) = unary(u)
            && s == b
        {
            return Some(fun(Context::EXP, t.clone()));
        }
        if let Term::Pow(pu) = u {
            let valid = |ratio: &Expr| ratio.to_i64().is_some() || is_positive(&pu.base, x);
            if s == &*pu.base {
                let ratio = one() / &**pu.exponant;
                return valid(&ratio).then(|| t.pow(&ratio));
            }
            if let Term::Pow(ps) = s
                && ps.base == pu.base
                && let ratio @ Term::Value(_) = &**ps.exponant / &**pu.exponant
                && valid(&ratio)
            {
                return Some(t.pow(&ratio));
            }
        }
        if let (Some((Context::EXP, a)), Some((Context::EXP, c))) = (unary(u), unary(s))
            && let ratio @ Term::Value(_) = (c / a).simplify()
        {
            return Some(t.pow(&ratio));
        }
        None
    })
}
