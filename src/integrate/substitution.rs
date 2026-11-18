//! Integration by substitution `{$u = g(x)$}`, when `{$f / g'$}` is an expression of `u` (derivative-divides).

use crate::{
    context::{Context, Symbol},
    limit::{depends, variable},
    term::Term,
};

use super::{Expr, Integrator, linear, map_tree, replace_symbol, unary};

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
        Term::Add(add) => add.iter().for_each(|t| collect_candidates(t, x, candidates)),
        Term::Mul(mul) => mul.iter().for_each(|t| collect_candidates(t, x, candidates)),
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

/// The number of nodes of a term.
fn size(term: &Expr) -> usize {
    match term {
        Term::Value(_) | Term::Symbol(_) => 1,
        Term::Add(add) => 1 + add.iter().map(size).sum::<usize>(),
        Term::Mul(mul) => 1 + mul.iter().map(size).sum::<usize>(),
        Term::Pow(pow) => 1 + size(&pow.base) + size(&pow.exponant),
        Term::Fun(fun) => {
            1 + fun
                .get_args::<super::Real>()
                .map_or(0, |args| args.iter().map(size).sum())
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
    let mut h = replace(&quotient, u, &t);
    if depends(&h, x) {
        h = replace(&quotient.simplify(), u, &t);
    }
    // `{$x = (t - b) / a$}` for a linear `{$u = a x + b$}`
    if depends(&h, x)
        && let Some(a) = linear(u, x)
    {
        let b = (u - &(&a * &variable(x))).simplify();
        h = h.substitute(x, &((&t - &b) / a))?;
    }
    if depends(&h, x) {
        return None;
    }
    let res = integrator.integrate(&h, t_symbol)?;
    Some(replace_symbol(&res, t_symbol, u))
}

/// Replace `u` by `t` in `term`, also writing related subexpressions as powers of `t`: `{$b^q = t^(q/p)$}` for
/// `{$u = b^p$}` (and `{$b = t^(1/p)$}`), and `{$exp(c) = t^(c/a)$}` for `{$u = exp(a)$}`.
fn replace(term: &Expr, u: &Expr, t: &Expr) -> Expr {
    map_tree(term, &|s| {
        if s == u {
            return Some(t.clone());
        }
        if let Term::Pow(pu) = u {
            if s == &*pu.base {
                return Some(t.pow(&(Term::one(crate::field::real::R) / &**pu.exponant)));
            }
            if let Term::Pow(ps) = s
                && ps.base == pu.base
                && let ratio @ Term::Value(_) = &**ps.exponant / &**pu.exponant
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
