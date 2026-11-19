//! Function expression.

use std::{cmp::Ordering, collections::BTreeSet, fmt::Debug, hash::Hash};

use dyn_clone::DynClone;
use dyn_eq::DynEq;
use dyn_hash::DynHash;
use owo_colors::colors::Cyan;

use crate::{
    context::{Context, Symbol},
    field::{Derivable, Group, Ring, Set, matrix::M},
    iter,
    printer::{PrettyPrint, PrettyPrinter, Print, PrintOptions},
    term::{Expand, Normalize, TermSet},
};

use super::{Flags, Term};

/// To allow function from any set to the set `T`, a dynamic dispatch is used with this trait, implementing needed methods.
///
/// See [Fun] for a structure implementing this trait.
pub trait Function<T: Set>: Debug + DynClone + DynEq + DynHash + Flags + PrettyPrint {
    /// Normalize arguments of the function.
    fn normalize(&self) -> Term<T>;
    /// Expand arguments of the function.
    fn expand(&self) -> Term<T>;
    /// Get the set where the function lives.
    fn get_set(&self) -> T;
    /// Get the identifier of the function.
    fn get_ident(&self) -> Symbol;
    /// Compare two functions, by identifier then by arguments.
    fn cmp_dyn(&self, other: &dyn Function<T>) -> Ordering;
    /// Add the symbols of the arguments to `symbols`.
    fn collect_symbols(&self, symbols: &mut BTreeSet<Symbol>);
    /// Get the identifier of the function as a string.
    fn get_ident_as_str(&self) -> &str {
        self.get_ident().name()
    }
}

impl<T: Set> dyn Function<T> {
    /// Try to get arguments of the function in set `From`
    pub fn get_args<From: Set>(&self) -> Option<&Vec<Term<From>>> {
        self.as_any()
            .downcast_ref::<Fun<From, T>>()
            .map(|fun| &fun.args)
    }
    /// Try to get first argument of the function in set `From`
    pub fn get_arg<From: Set>(&self) -> Option<&Term<From>> {
        self.as_any()
            .downcast_ref::<Fun<From, T>>()
            .map(|fun| fun.args.first())?
    }
}

impl<From: Set, T: Set> Function<T> for Fun<From, T> {
    fn normalize(&self) -> Term<T> {
        self.map_args(Normalize::normalize)
    }
    fn expand(&self) -> Term<T> {
        self.map_args(Expand::expand)
    }
    fn get_set(&self) -> T {
        self.set
    }
    fn get_ident(&self) -> Symbol {
        self.ident
    }
    fn collect_symbols(&self, symbols: &mut BTreeSet<Symbol>) {
        for arg in &self.args {
            arg.collect_symbols(symbols);
        }
    }
    fn cmp_dyn(&self, other: &dyn Function<T>) -> Ordering {
        self.ident.cmp(&other.get_ident()).then_with(|| {
            other
                .get_args::<From>()
                .map_or(Ordering::Equal, |args| Term::cmp_args(&self.args, args))
        })
    }
}

/// Comparison of function arguments, only possible when arguments are ordered.
trait CmpArgs: Sized {
    fn cmp_args(a: &[Self], b: &[Self]) -> Ordering;
}

impl<T: Set> CmpArgs for Term<T> {
    default fn cmp_args(a: &[Self], b: &[Self]) -> Ordering {
        a.len().cmp(&b.len())
    }
}

impl<T: Group> CmpArgs for Term<T> {
    fn cmp_args(a: &[Self], b: &[Self]) -> Ordering {
        a.len()
            .cmp(&b.len())
            .then_with(|| iter::cmp_by(a, b, Self::cmp))
    }
}

dyn_hash::hash_trait_object!(<T> Function<T>);
dyn_clone::clone_trait_object!(<T> Function<T> );
dyn_eq::eq_trait_object!(<T: 'static> Function<T>);

/// A function called in a mathematical expression, like `sqrt(x)`
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Fun<From: Set, T = From> {
    flags: u8,
    pub(crate) ident: Symbol,
    pub(crate) args: Vec<Term<From>>,
    pub(crate) set: T,
}

impl<From: Set, T> Fun<From, T> {
    /// Create a new function expression
    pub const fn new(ident: Symbol, args: Vec<Term<From>>, set: T) -> Self {
        Self {
            flags: 0,
            ident,
            args,
            set,
        }
    }
}

impl<From: Set, T: Set> Fun<From, T> {
    /// Apply `f` to every argument, building a new function term.
    fn map_args(&self, f: impl Fn(&Term<From>) -> Term<From>) -> Term<T> {
        Term::Fun(Box::new(Self::new(
            self.ident,
            self.args.iter().map(f).collect(),
            self.set,
        )))
    }
}

impl<From: Set, T> Flags for Fun<From, T> {
    fn get_flags(&self) -> u8 {
        self.flags
    }
    fn get_flags_mut(&mut self) -> &mut u8 {
        &mut self.flags
    }
}

impl<From: Set, T: Set> Print for Fun<From, T> {
    fn print(&self, options: &PrintOptions, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut args: Vec<_> = self.args.iter().collect();
        if options.typst {
            let name = self.get_ident_as_str();
            if let (Context::LIM, [fun, x, point, direction @ ..]) = (self.ident, args.as_slice()) {
                let side = match direction {
                    [] => Some(""),
                    [direction] => {
                        match direction
                            .with_options(PrintOptions::typst())
                            .to_string()
                            .as_str()
                        {
                            "1" => Some("^+"),
                            "-1" => Some("^-"),
                            _ => None,
                        }
                    }
                    _ => None,
                };
                if let Some(side) = side {
                    // `{$lim_(x -> a^+) (f)$}`
                    f.write_str("lim_(")?;
                    x.print(options, f)?;
                    f.write_str(" -> ")?;
                    point.print(options, f)?;
                    write!(f, "{side}) (")?;
                    fun.print(options, f)?;
                    return f.write_str(")");
                }
            }
            if let (Context::FACTORIAL, [n]) = (self.ident, args.as_slice()) {
                // `{$n!$}`
                Self::group(*n, options, f)?;
                return f.write_str("!");
            }
            if let (Context::POLYGAMMA, [m, u]) = (self.ident, args.as_slice()) {
                // `{$psi(u)$}`, or `{$psi^((m))(u)$}`
                f.write_str("psi")?;
                let order = m.with_options(PrintOptions::typst()).to_string();
                if order != "0" {
                    write!(f, "^(({order}))")?;
                }
                f.write_str("(")?;
                u.print(options, f)?;
                return f.write_str(")");
            }
            if matches!(self.ident, Context::SUM | Context::PRODUCT)
                && let [fun, k, a, b] = args.as_slice()
            {
                // `{$sum_(k = a)^b f$}`
                write!(f, "{}_(", if self.ident == Context::SUM { "sum" } else { "product" })?;
                k.print(options, f)?;
                f.write_str(" = ")?;
                a.print(options, f)?;
                f.write_str(")^(")?;
                b.print(options, f)?;
                f.write_str(") ")?;
                if matches!(fun, Term::Add(_)) {
                    f.write_str("(")?;
                    fun.print(options, f)?;
                    return f.write_str(")");
                }
                return fun.print(options, f);
            }
            if self.ident == Context::INTEGRATE
                && let [fun, x, bounds @ ..] = args.as_slice()
                && matches!(bounds.len(), 0 | 2)
            {
                // `{$integral_a^b f dif x$}`
                f.write_str("integral")?;
                if let [a, b] = bounds {
                    f.write_str("_(")?;
                    a.print(options, f)?;
                    f.write_str(")^(")?;
                    b.print(options, f)?;
                    f.write_str(")")?;
                }
                f.write_str(" ")?;
                if matches!(fun, Term::Add(_)) {
                    f.write_str("(")?;
                    fun.print(options, f)?;
                    f.write_str(")")?;
                } else {
                    fun.print(options, f)?;
                }
                f.write_str(" dif ")?;
                return x.print(options, f);
            }
            match self.ident {
                Context::CONJ => f.write_str("overline")?,
                Context::RE => f.write_str("Re")?,
                Context::IM => f.write_str("Im")?,
                Context::ROOT => {
                    // Typst takes the index first: `root(n, x)`
                    args.reverse();
                    f.write_str("root")?;
                }
                Context::BINOMIAL => f.write_str("binom")?,
                Context::GAMMA => f.write_str("Gamma")?,
                Context::BETA => f.write_str("Beta")?,
                Context::ZETA => f.write_str("zeta")?,
                Context::ASIN => f.write_str("arcsin")?,
                Context::ACOS => f.write_str("arccos")?,
                Context::ATAN => f.write_str("arctan")?,
                Context::ABS
                | Context::DET
                | Context::SQRT
                | Context::FLOOR
                | Context::CEIL
                | Context::MIN
                | Context::MAX
                | Context::GCD
                | Context::LCM
                | Context::EXP
                | Context::LN
                | Context::SIN
                | Context::COS
                | Context::TAN
                | Context::SINH
                | Context::COSH
                | Context::TANH => f.write_str(name)?,
                _ if name.chars().count() == 1 => f.write_str(name)?,
                _ => write!(f, "op(\"{name}\")")?,
            }
        } else {
            Self::fg::<Cyan>(self.get_ident_as_str(), options, f)?;
        }
        Self::group_delim("(", options, f)?;
        for (i, term) in args.iter().enumerate() {
            term.print(options, f)?;
            if i != self.args.len() - 1 {
                Self::delimiter(", ", options, f)?;
            }
        }
        Self::group_delim(")", options, f)
    }
}
impl<From: Set, T: Set> PrettyPrint for Fun<From, T> {
    fn pretty_print(&self, options: &PrintOptions) -> crate::printer::PrettyPrinter {
        if self.ident == Context::INTEGRATE
            && let [fun, x, bounds @ ..] = self.args.as_slice()
            && matches!(bounds.len(), 0 | 2)
        {
            let mut res = fun.pretty_print(options);
            if matches!(fun, Term::Add(_)) {
                res.paren();
            }
            res.concat(" d", false, &x.pretty_print(options));
            let bounds = bounds
                .iter()
                .map(|bound| bound.pretty_print(options))
                .collect::<Vec<_>>();
            res.integral(match bounds.as_slice() {
                [lower, upper] => Some((lower, upper)),
                _ => None,
            });
            return res;
        }
        if matches!(self.ident, Context::SUM | Context::PRODUCT)
            && let [fun, k, a, b] = self.args.as_slice()
        {
            let mut res = fun.pretty_print(options);
            if matches!(fun, Term::Add(_)) {
                res.paren();
            }
            let mut lower = k.pretty_print(options);
            lower.concat("=", false, &a.pretty_print(options));
            let sign = if self.ident == Context::SUM { '∑' } else { '∏' };
            res.big_operator(sign, &lower, &b.pretty_print(options));
            return res;
        }
        let mut args = self.args.iter().map(|x| x.pretty_print(options));
        let mut res = args.next().unwrap();
        for mut arg in args {
            arg.left(' ');
            res.concat(",", false, &arg);
        }
        res.paren();
        if self.ident == Context::ABS {
            let mut res = self.args.first().unwrap().pretty_print(options);
            res.group('|', '|');
            res
        } else {
            let mut fun = PrettyPrinter::from(self.get_ident_as_str().to_string());
            fun.concat("", false, &res);
            fun
        }
    }
}

/// Evaluate the builtins `expand(u)` and `simplify(u)`, which rewrite their argument in any ring. Returns `None`
/// for other functions.
pub(crate) fn eval_rewrite_builtin<T: Ring>(fun: &dyn Function<T>) -> Option<Term<T>> {
    match fun.get_ident() {
        Context::EXPAND => fun.get_arg::<T>().map(Expand::expand),
        Context::SIMPLIFY => fun.get_arg::<T>().map(Term::simplify),
        _ => None,
    }
}

/// Evaluate the builtins `diff(f, x)` and `det(m)` in a field of scalars. Returns `None` for other functions,
/// or when they can't be evaluated.
pub(crate) fn eval_calculus_builtin<T>(fun: &dyn Function<T>) -> Option<Term<T>>
where
    T: Derivable<ExponantSet = T, ProductCoefficientSet = T>,
{
    match fun.get_ident() {
        Context::DIFF => {
            let Some([f, Term::Symbol(x)]) = fun.get_args::<T>().map(Vec::as_slice) else {
                return None;
            };
            let res = f.derivative(x.symbol);
            // `f` can't be differentiated, keep the term to avoid normalizing forever
            let unevaluated = matches!(&res, Term::Fun(inner)
                if inner.get_ident() == Context::DIFF && inner.get_arg::<T>() == Some(f));
            (!unevaluated).then_some(res)
        }
        Context::DET => match fun.get_arg::<M<TermSet<T>>>() {
            Some(Term::Value(matrix)) => matrix.value.det().ok(),
            _ => None,
        },
        _ => None,
    }
}
