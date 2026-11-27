//! Atoms of relations which aren't polynomial in the unknowns: absolute values `{$abs(g)$}` and roots
//! `{$g^(p/q)$}`, like `{$sqrt(x) < 3$}` or `{$abs(x - 1) < 8$}`.
//!
//! Each atom is replaced by a new symbol `y`, with `{$y = abs(g)$}` or `{$y^q = g$}`, so that a relation becomes
//! `{$n / d op 0$}` with `n` and `d` polynomials in the unknowns and the atoms. Eliminating the atoms gives
//! polynomials in the unknowns vanishing wherever `n` (or `d`) does, for every choice of the signs of the absolute
//! values and of the conjugates of the roots: the relation, continuous on its domain away from them, has a constant
//! sign on the cells where they have one, found by evaluating it at a sample point.

use std::{cmp::Ordering, convert::Infallible};

use malachite::{Rational, base::num::basic::traits::One};

use crate::{
    context::{Context, Symbol},
    field::real::expr::{
        Expr, constant_sign, depends, has_function, subs, try_map_operands, unary, value, variable,
        zero,
    },
    solve::{SolveError, plain, polynomial::polynomial_form},
    term::{Expand, Normalize, Term},
};

/// The definition of an atom.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Kind {
    /// `{$y = abs(g)$}`.
    Abs,
    /// `{$y = g^(1/q)$}`, real for every `g` when `q` is odd, else for `{$g >= 0$}`.
    Root(u32),
}

/// An atom `{$abs(g)$}` or `{$g^(1/q)$}`.
#[derive(Clone, Debug)]
struct Atom {
    symbol: Symbol,
    kind: Kind,
    /// The base `g`, with its inner atoms replaced by their symbols.
    base: Expr,
    /// The atom itself, in the unknowns.
    original: Expr,
    /// The base in the unknowns, for the domain `{$g >= 0$}` of an even root.
    original_base: Expr,
}

/// The atoms of the relations of a decomposition, inner atoms first.
pub(super) struct Atoms {
    atoms: Vec<Atom>,
}

/// `term` with the absolute values of constants whose sign is known replaced by `{$plus.minus c$}`, from the inner
/// ones, so that zeros like `{$abs(sqrt(5) - 1) - (sqrt(5) - 1)$}` at a sample point can be proven.
pub(super) fn resolve_abs(term: &Expr) -> Expr {
    if !has_function(term, &[Context::ABS]) {
        return term.clone();
    }
    let Ok(term) = try_map_operands::<Infallible>(term, |operand| Ok(resolve_abs(operand)));
    if let Some((ident, arg)) = unary(&term)
        && ident == Context::ABS
        && arg
            .symbols()
            .iter()
            .all(|s| Context::is_builtin_constant(*s))
        && let Some(sign) = constant_sign(arg)
    {
        return if sign == Ordering::Less {
            (-arg.clone()).normalize()
        } else {
            arg.clone()
        };
    }
    term
}

/// The integer `n` as a value.
fn integer(n: i64) -> Expr {
    value(Rational::from(n))
}

impl Atoms {
    /// No atom.
    pub(super) const fn new() -> Self {
        Self { atoms: vec![] }
    }

    /// The symbols of the atoms.
    pub(super) fn symbols(&self) -> impl Iterator<Item = Symbol> + '_ {
        self.atoms.iter().map(|atom| atom.symbol)
    }

    /// The symbol of the atom `kind` of `base`, added if needed.
    fn atom(&mut self, kind: Kind, base: Expr, original: Expr, original_base: Expr) -> Symbol {
        if let Some(atom) = self
            .atoms
            .iter()
            .find(|atom| atom.kind == kind && atom.base == base)
        {
            return atom.symbol;
        }
        // Not a valid identifier, so it can't be a symbol of the relations
        let symbol = Symbol::new(format!("@r{}", self.atoms.len()));
        self.atoms.push(Atom {
            symbol,
            kind,
            base,
            original,
            original_base,
        });
        symbol
    }

    /// `term` with its atoms depending on `unknowns` replaced by symbols, bottom-up.
    pub(super) fn replace(&mut self, term: &Expr, unknowns: &[Symbol]) -> Expr {
        if !unknowns.iter().any(|x| depends(term, *x)) {
            return term.clone();
        }
        if let Term::Pow(pow) = term
            && let Term::Value(e) = &**pow.exponant
            && let Ok(q) = u32::try_from(e.value.denominator_ref())
            && q > 1
        {
            let p = &e.value * Rational::from(q);
            let base = self.replace(&pow.base, unknowns);
            let original = (*pow.base)
                .clone()
                .pow(&value(Rational::ONE / Rational::from(q)));
            let y = self.atom(Kind::Root(q), base, original, (*pow.base).clone());
            return variable(y).pow(&value(p));
        }
        if let Some((ident, arg)) = unary(term)
            && ident == Context::ABS
        {
            let base = self.replace(arg, unknowns);
            let y = self.atom(Kind::Abs, base, term.clone(), arg.clone());
            return variable(y);
        }
        let Ok(res) =
            try_map_operands::<Infallible>(term, |operand| Ok(self.replace(operand, unknowns)));
        res
    }

    /// The bases `g` of the even roots, whose domain is `{$g >= 0$}`, inner atoms first, from the `from`-th atom.
    pub(super) fn domains(&self, from: usize) -> Vec<Expr> {
        self.atoms[from..]
            .iter()
            .filter(|atom| matches!(atom.kind, Kind::Root(q) if q % 2 == 0))
            .map(|atom| atom.original_base.clone())
            .collect()
    }

    /// The number of atoms.
    pub(super) const fn len(&self) -> usize {
        self.atoms.len()
    }

    /// `term` with the symbols of the atoms replaced by the atoms themselves.
    pub(super) fn restore(&self, term: &Expr) -> Expr {
        self.atoms
            .iter()
            .fold(term.clone(), |term, atom| {
                subs(&term, atom.symbol, &atom.original)
            })
            .normalize()
    }

    /// Polynomials in the unknowns, whose roots contain those of the polynomial `p` in the unknowns and the atoms,
    /// for every value of the atoms (both signs of absolute values, every conjugate of roots).
    ///
    /// `resultant` gives the resultant of two polynomials by their coefficients.
    ///
    /// # Errors
    /// Returns an error if a resultant is too large, or vanishes identically.
    pub(super) fn eliminate(
        &self,
        p: &Expr,
        resultant: impl Fn(&[Expr], &[Expr]) -> Result<Expr, SolveError>,
    ) -> Result<Vec<Expr>, SolveError> {
        let mut polynomials = vec![p.expand()];
        // Outer atoms first, since their bases contain the inner ones
        for atom in self.atoms.iter().rev() {
            let y = atom.symbol;
            let (num, den) = atom.base.as_fraction(true);
            let (num, den) = (num.expand(), den.expand());
            let mut next = vec![];
            for p in polynomials {
                if !depends(&p, y) {
                    next.push(p);
                    continue;
                }
                match atom.kind {
                    Kind::Abs => {
                        for sign in [1, -1] {
                            let branch = subs(&p, y, &(integer(sign) * atom.base.clone()));
                            let branch = branch.normalize().as_fraction(true).0.expand();
                            if branch.is_zero() {
                                // The relation vanishes where the branch holds, which ends where `g` vanishes
                                next.push(num.clone());
                            } else {
                                next.push(branch);
                            }
                        }
                    }
                    Kind::Root(q) => {
                        // `{$d y^q - n$}`
                        let mut minimal = vec![zero(); q as usize + 1];
                        minimal[0] = (-num.clone()).normalize();
                        minimal[q as usize] = den.clone();
                        let eliminated = resultant(&polynomial_form(&p, y)?, &minimal)?.expand();
                        if eliminated.is_zero() {
                            return Err(SolveError::Inequality(format!(
                                "can't eliminate `{}` from `{}`",
                                plain(&atom.original),
                                plain(&self.restore(&p))
                            )));
                        }
                        next.push(eliminated);
                    }
                }
            }
            polynomials = next;
        }
        Ok(polynomials)
    }
}
