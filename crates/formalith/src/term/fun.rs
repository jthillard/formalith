//! Function expression.

use std::{cmp::Ordering, collections::BTreeSet, fmt::Debug, hash::Hash};

use dyn_clone::DynClone;
use dyn_eq::DynEq;
use dyn_hash::DynHash;
use owo_colors::colors::Cyan;

use crate::{
    context::{Context, Symbol},
    field::{
        Derivable, Monoid, Ring, Set,
        matrix::{M, MatrixEntries, VectorSpaceElement},
        real::{Real, rootof},
    },
    iter,
    printer::{PrettyPrint, PrettyPrinter, Print, PrintOptions},
    term::{Expand, Normalize, TermSet},
};

use super::{Flags, Term, Value, relation::Relation};
use crate::solve::polynomial::{polynomial_form, sylvester_determinant};

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
    /// Whether the function is `ident` or one of its arguments mentions it, see [`Term::mentions_function`].
    fn mentions_function(&self, ident: Symbol) -> bool;
    /// Get the identifier of the function as a string.
    fn get_ident_as_str(&self) -> &str {
        // A held sum prints like a sum, so that it can be parsed back
        if self.get_ident() == Context::held_sum() {
            return Context::SUM.name();
        }
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
    fn mentions_function(&self, ident: Symbol) -> bool {
        self.ident == ident || self.args.iter().any(|arg| arg.mentions_function(ident))
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

impl<T: Monoid> CmpArgs for Term<T> {
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
        if let Some(display) = self.real_root_display() {
            return display.print(options, f);
        }
        let mut args: Vec<_> = self.args.iter().collect();
        if let (Some(relation), [lhs, rhs]) = (Relation::from_symbol(self.ident), args.as_slice()) {
            // A condition `lhs < rhs`
            lhs.print(options, f)?;
            f.write_str(" ")?;
            Self::operator(relation.operator(), options, f)?;
            f.write_str(" ")?;
            return rhs.print(options, f);
        }
        if let (Context::FACTORIAL, [n]) = (self.ident, args.as_slice()) {
            // `{$n!$}`, `(-1)!` and `(1/2)!`, since the parser reads `-1!` as `-(1!)` and `1/2!` as `1/(2!)`
            if let Term::Value(value) = n
                && !value
                    .with_options(PrintOptions::plain())
                    .to_string()
                    .chars()
                    .all(char::is_alphanumeric)
            {
                Self::group_delim("(", options, f)?;
                n.print(options, f)?;
                Self::group_delim(")", options, f)?;
            } else {
                Self::group(*n, options, f)?;
            }
            return Self::operator("!", options, f);
        }
        if self.ident == Context::lambertw_m1()
            && let [u] = args.as_slice()
        {
            // `{$W_(-1)(u)$}`, printed `lambertw(u, -1)` to be parsed back
            if options.typst {
                f.write_str("W_(-1)(")?;
                u.print(options, f)?;
                return f.write_str(")");
            }
            Self::fg::<Cyan>(Context::LAMBERTW.name(), options, f)?;
            Self::group_delim("(", options, f)?;
            u.print(options, f)?;
            Self::delimiter(", ", options, f)?;
            f.write_str("-1")?;
            return Self::group_delim(")", options, f);
        }
        if options.typst && self.ident == Context::PIECEWISE {
            // `{$cases(v_1 & "if" c_1, ..., d & "otherwise")$}`
            f.write_str("cases(")?;
            for (i, pair) in args.chunks(2).enumerate() {
                if i != 0 {
                    f.write_str(", ")?;
                }
                pair[pair.len() - 1].print(options, f)?;
                if let [condition, _] = pair {
                    f.write_str(" & \"if \" ")?;
                    condition.print(options, f)?;
                } else {
                    f.write_str(" & \"otherwise\"")?;
                }
            }
            return f.write_str(")");
        }
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
            if let (Context::BERNOULLI | Context::EULER, [n]) = (self.ident, args.as_slice()) {
                // `{$B_n$}`, `{$E_n$}`
                f.write_str(if self.ident == Context::BERNOULLI {
                    "B_("
                } else {
                    "E_("
                })?;
                n.print(options, f)?;
                return f.write_str(")");
            }
            if (matches!(self.ident, Context::SUM | Context::PRODUCT)
                || self.ident == Context::held_sum())
                && let [fun, k, a, b] = args.as_slice()
            {
                // `{$sum_(k = a)^b f$}`
                write!(
                    f,
                    "{}_(",
                    if self.ident == Context::PRODUCT {
                        "product"
                    } else {
                        "sum"
                    }
                )?;
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
            if self.ident == Context::ROOT {
                // Typst takes the index first: `root(n, x)`
                args.reverse();
            }
            f.write_str(&crate::printer::typst_function_name(self.ident, name))?;
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
        if let Some(display) = self.real_root_display() {
            return display.pretty_print(options);
        }
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
        if (matches!(self.ident, Context::SUM | Context::PRODUCT)
            || self.ident == Context::held_sum())
            && let [fun, k, a, b] = self.args.as_slice()
        {
            let mut res = fun.pretty_print(options);
            if matches!(fun, Term::Add(_)) {
                res.paren();
            }
            let mut lower = k.pretty_print(options);
            lower.concat("=", false, &a.pretty_print(options));
            let sign = if self.ident == Context::PRODUCT {
                '∏'
            } else {
                '∑'
            };
            res.big_operator(&sign.to_string(), &lower, Some(&b.pretty_print(options)));
            return res;
        }
        if let Some(res) = self.pretty_print_special(*options) {
            return res;
        }
        if let (Some(relation), [lhs, rhs]) =
            (Relation::from_symbol(self.ident), self.args.as_slice())
        {
            let mut res = lhs.pretty_print(options);
            res.concat(relation.pretty_operator(), true, &rhs.pretty_print(options));
            return res;
        }
        let mut args = self.args.iter().map(|x| x.pretty_print(options));
        let mut res = args.next().unwrap();
        for mut arg in args {
            arg.left(' ');
            res.concat(",", false, &arg);
        }
        res.paren();
        let name = match self.ident {
            Context::GAMMA => "Γ".into(),
            Context::BETA => "B".into(),
            Context::ZETA => "ζ".into(),
            Context::LAMBERTW => "W".into(),
            ident if ident == Context::lambertw_m1() => "W₋₁".into(),
            _ => crate::printer::pretty_name(self.get_ident_as_str()),
        };
        let mut fun = PrettyPrinter::from(name.into_owned());
        fun.concat("", false, &res);
        fun
    }
}

impl<From: Set, T: Set> Fun<From, T> {
    /// `rootof(p, k)` for the internal function `@rootof(j, c_0, ..., c_n)`, printed so to be parsed back.
    fn real_root_display(&self) -> Option<Term<Real>> {
        if self.ident != Context::real_root() {
            return None;
        }
        let fun = (self as &dyn std::any::Any).downcast_ref::<Fun<Real, Real>>()?;
        rootof::display(&fun.args)
    }

    /// Pretty print the builtins drawn with their own notation, like `{$n!$}`, `{$floor(x)$}` or `{$binom(n, k)$}`.
    fn pretty_print_special(&self, options: PrintOptions) -> Option<PrettyPrinter> {
        let pretty = |term: &Term<From>| term.pretty_print(&options);
        Some(match (self.ident, self.args.as_slice()) {
            (Context::ABS, [u]) => {
                let mut res = pretty(u);
                res.group('|', '|');
                res
            }
            (Context::FLOOR, [u]) => {
                let mut res = pretty(u);
                res.group('⌊', '⌋');
                res
            }
            (Context::CEIL, [u]) => {
                let mut res = pretty(u);
                res.group('⌈', '⌉');
                res
            }
            (Context::FACTORIAL, [n]) => {
                let mut res = pretty(n);
                if match n {
                    Term::Add(_) | Term::Mul(_) | Term::Pow(_) => true,
                    Term::Value(value) => {
                        !value.set.is_atomic(&value.value)
                            || value.typst().to_string().starts_with('-')
                    }
                    Term::Symbol(_) | Term::Fun(_) => false,
                } || res.height() > 1
                {
                    res.paren();
                }
                res.concat("!", false, &PrettyPrinter::empty());
                res
            }
            (Context::BINOMIAL, [n, k]) => {
                let mut res = pretty(n);
                res.over(&pretty(k));
                res.paren();
                res
            }
            (Context::POLYGAMMA, [m, u]) => {
                let mut res = PrettyPrinter::from("ψ".to_string());
                if m.with_options(PrintOptions::plain()).to_string() != "0" {
                    let mut order = pretty(m);
                    order.paren();
                    res.pow(&order);
                }
                let mut arg = pretty(u);
                arg.paren();
                res.concat("", false, &arg);
                res
            }
            (Context::LIM, [f, x, point, direction @ ..]) => {
                let side = match direction {
                    [] => "",
                    [direction] => match direction
                        .with_options(PrintOptions::plain())
                        .to_string()
                        .as_str()
                    {
                        "1" => "⁺",
                        "-1" => "⁻",
                        _ => return None,
                    },
                    _ => return None,
                };
                let mut lower = pretty(x);
                lower.concat("→", true, &pretty(point));
                lower.concat(side, false, &PrettyPrinter::empty());
                let mut res = pretty(f);
                if matches!(f, Term::Add(_)) {
                    res.paren();
                }
                res.big_operator("lim", &lower, None);
                res
            }
            (Context::PIECEWISE, args) if !args.is_empty() => PrettyPrinter::cases(
                args.chunks(2)
                    .map(|pair| match pair {
                        [condition, value] => (pretty(value), Some(pretty(condition))),
                        [default] => (pretty(default), None),
                        _ => unreachable!("chunks of two"),
                    })
                    .collect(),
            ),
            (Context::DIFF, [f, x, order @ ..]) if order.len() <= 1 => {
                let order = order.first().map(pretty);
                let order = order.filter(|order| order.lines != ["1"]);
                let mut d = PrettyPrinter::from("d".to_string());
                let mut dx = PrettyPrinter::from("d".to_string());
                dx.concat("", false, &pretty(x));
                if let Some(order) = &order {
                    d.pow(order);
                    dx.pow(order);
                }
                d.vertical_concat("─", &dx);
                let mut res = pretty(f);
                if !matches!(f, Term::Symbol(_) | Term::Fun(_)) {
                    res.paren();
                }
                d.concat("", false, &res);
                d
            }
            _ => return None,
        })
    }
}

/// Evaluate the builtins shared by the rings with scalar elements: `expand` and `simplify`
/// ([`eval_rewrite_builtin`]), the scalars of matrices ([`eval_matrix_builtin`]), `degree` ([`eval_degree`]) and
/// the algebraic ones ([`eval_algebra_builtin`]). Sets evaluating some of them their own way do it before.
pub(crate) fn eval_ring_builtin<T>(fun: &dyn Function<T>) -> Option<Term<T>>
where
    T: Ring<ExponantSet: Ring, ProductCoefficientSet = T>,
{
    match fun.get_ident() {
        Context::EXPAND | Context::SIMPLIFY => eval_rewrite_builtin(fun),
        Context::DET | Context::TRACE | Context::RANK | Context::CHARPOLY => {
            eval_matrix_builtin(fun)
        }
        Context::DEGREE => eval_degree(fun),
        _ => eval_algebra_builtin(fun),
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

/// Get the polynomial and the variable of the builtin `degree(f, x)`, the variable being the only symbol of `f`
/// when it is omitted (any symbol if `f` has none). Returns `None` for other functions or arguments.
pub(crate) fn degree_args<T: Set>(fun: &dyn Function<T>) -> Option<(&Term<T>, Symbol)> {
    if fun.get_ident() != Context::DEGREE {
        return None;
    }
    match fun.get_args::<T>()?.as_slice() {
        [f, Term::Symbol(x)] => Some((f, x.symbol)),
        [f] => {
            let symbols: Vec<_> = f
                .symbols()
                .into_iter()
                .filter(|s| !Context::is_builtin_constant(*s))
                .collect();
            match symbols.as_slice() {
                [x] => Some((f, *x)),
                [] => Some((f, Symbol::new("x"))),
                _ => None,
            }
        }
        _ => None,
    }
}

/// Get the exponents of `x` in the terms of the expanded polynomial `f` (0 for terms without `x`). Exponents which
/// aren't natural values must satisfy `accept`. Returns `None` if `f` is zero or isn't a polynomial in `x`, like
/// `{$sin x$}`, `{$1/x$}` or `{$sqrt(x)$}`, its coefficients being assumed non-zero.
pub(crate) fn degree_exponents<T>(
    f: &Term<T>,
    x: Symbol,
    accept: impl Fn(&Term<T::ExponantSet>) -> bool,
) -> Option<Vec<Term<T::ExponantSet>>>
where
    T: Ring<ExponantSet: Ring, ProductCoefficientSet = T>,
{
    let exponant_set = f.get_set().get_exponant_set();
    let polynomial = f.to_polynomial();
    if polynomial.is_zero() {
        return None;
    }
    let mut exponents = vec![];
    for (monomial, _) in polynomial.terms() {
        let mut exponent = Term::zero(exponant_set);
        for (base, e) in monomial {
            if matches!(base, Term::Symbol(s) if s.symbol == x) {
                let natural = matches!(e, Term::Value(v)
                    if exponant_set.to_i64(&v.value).is_some_and(|n| n >= 0));
                if !natural && (e.symbols().contains(&x) || !accept(e)) {
                    return None;
                }
                exponent = e.clone();
            } else if base.symbols().contains(&x) || e.symbols().contains(&x) {
                return None;
            }
        }
        if !exponents.contains(&exponent) {
            exponents.push(exponent);
        }
    }
    Some(exponents)
}

/// Get the integer `n` as a constant of `set`, `None` if it would be equal to a smaller natural number, like `7` in
/// `{$ZZ/7ZZ$}`.
pub(crate) fn natural_constant<T: Ring>(set: T, n: i64) -> Option<Term<T>> {
    let value = set.nth(n);
    (set.to_i64(&value) == Some(n) || (1..=n).all(|k| !set.is_zero(&set.nth(k))))
        .then(|| Term::constant(value, set))
}

/// Evaluate the builtin `degree(f, x)` when every exponent of `x` is a natural value. Returns `None` for other
/// functions, or when it can't be evaluated.
pub(crate) fn eval_degree<T>(fun: &dyn Function<T>) -> Option<Term<T>>
where
    T: Ring<ExponantSet: Ring, ProductCoefficientSet = T>,
{
    let (f, x) = degree_args(fun)?;
    let exponant_set = f.get_set().get_exponant_set();
    let degree = degree_exponents(f, x, |_| false)?
        .iter()
        .filter_map(|e| match e {
            Term::Value(v) => exponant_set.to_i64(&v.value),
            _ => None,
        })
        .max()?;
    natural_constant(fun.get_set(), degree)
}

/// Evaluate the builtin `diff(f, x)`, or `diff(f, x, n)` for the `n`-th derivative with a natural `n`, in a field
/// of scalars. Returns `None` for other functions, or when they can't be evaluated.
pub(crate) fn eval_calculus_builtin<T>(fun: &dyn Function<T>) -> Option<Term<T>>
where
    T: Derivable<ExponantSet = T, ProductCoefficientSet = T>,
{
    match fun.get_ident() {
        Context::DIFF => {
            let (f, x, order) = match fun.get_args::<T>()?.as_slice() {
                [f, Term::Symbol(x)] => (f.clone(), x.symbol, 1),
                [f, Term::Symbol(x), Term::Value(n)] => {
                    let n = usize::try_from(fun.get_set().to_i64(&n.value)?).ok()?;
                    (f.clone(), x.symbol, n)
                }
                _ => return None,
            };
            let mut res = f;
            for _ in 0..order {
                let derivative = res.derivative(x);
                // `f` can't be differentiated, keep the term to avoid normalizing forever
                if matches!(&derivative, Term::Fun(inner)
                    if inner.get_ident() == Context::DIFF && inner.get_arg::<T>() == Some(&res))
                {
                    return None;
                }
                res = derivative;
            }
            Some(res)
        }
        _ => None,
    }
}

/// Evaluate the builtins `det(m)`, `trace(m)`, `rank(m)` and `charpoly(m, x)`, whose argument is a matrix with
/// entries in `T`. Returns `None` for other functions, or when they can't be evaluated.
pub(crate) fn eval_matrix_builtin<T: Ring>(fun: &dyn Function<T>) -> Option<Term<T>> {
    let set = fun.get_set();
    let args = fun.get_args::<M<TermSet<T>>>()?;
    let value = match args.first()? {
        Term::Value(value) => &value.value,
        _ => return None,
    };
    let VectorSpaceElement::Vector(matrix) = value else {
        return (fun.get_ident() == Context::DET).then(|| value.det().ok())?;
    };
    match fun.get_ident() {
        Context::DET => matrix.det().ok(),
        Context::TRACE => matrix.trace().ok(),
        Context::RANK => {
            let rank = <TermSet<T> as MatrixEntries>::rank(matrix)?;
            Some(Term::constant(set.nth(i64::try_from(rank).ok()?), set))
        }
        Context::CHARPOLY => {
            let x = match args.get(1) {
                None => Symbol::new("x"),
                Some(Term::Symbol(x)) => x.symbol,
                Some(Term::Value(Value {
                    value: VectorSpaceElement::Scalar(Term::Symbol(x), _),
                    ..
                })) => x.symbol,
                Some(_) => return None,
            };
            <TermSet<T> as MatrixEntries>::charpoly(matrix, x)
        }
        _ => None,
    }
}

/// The variable of a polynomial builtin like `resultant(p, q, [x])`: `x` when it is given, otherwise the only symbol
/// of the polynomials (`x` when they have none). Returns `None` when there are several symbols.
fn polynomial_variable<T: Set>(polynomials: &[&Term<T>], x: Option<&Term<T>>) -> Option<Symbol> {
    match x {
        Some(Term::Symbol(x)) => Some(x.symbol),
        Some(_) => None,
        None => {
            let symbols: BTreeSet<_> = polynomials
                .iter()
                .flat_map(|p| p.symbols())
                .filter(|s| !Context::is_builtin_constant(*s))
                .collect();
            match symbols.len() {
                0 => Some(Symbol::new("x")),
                1 => symbols.into_iter().next(),
                _ => None,
            }
        }
    }
}

/// Bound on the size `{$m + n$}` of the Sylvester matrix of the builtins `resultant` and `discriminant`, whose
/// determinant is computed with a minor per subset of columns.
const MAX_SYLVESTER_SIZE: usize = 14;

/// The resultant of `p` and `q` in `x`, `None` if they aren't polynomials in `x`, if one of them is zero or if
/// their Sylvester matrix is too large.
fn resultant<T: Ring>(p: &Term<T>, q: &Term<T>, x: Symbol) -> Option<Term<T>> {
    let p = polynomial_form(&p.expand(), x).ok()?;
    let q = polynomial_form(&q.expand(), x).ok()?;
    if p.iter().all(Term::is_zero) || q.iter().all(Term::is_zero) {
        return None;
    }
    if p.len() + q.len() - 2 > MAX_SYLVESTER_SIZE {
        return None;
    }
    if p.len() == 1 && q.len() == 1 {
        return Some(Term::one(p[0].get_set()));
    }
    Some(sylvester_determinant(&p, &q).expand())
}

/// The discriminant `{$(-1)^(n (n - 1)/2) "res"(p, p') / a_n$}` of a polynomial `p` of degree `{$n >= 1$}` in `x`
/// with leading coefficient `{$a_n$}`, `None` if it can't be computed.
// Degrees are small
#[allow(clippy::cast_possible_wrap)]
fn discriminant<T: Ring>(p: &Term<T>, x: Symbol) -> Option<Term<T>> {
    let coefficients = polynomial_form(&p.expand(), x).ok()?;
    let n = coefficients.len() - 1;
    if n == 0 || 2 * n - 1 > MAX_SYLVESTER_SIZE {
        return None;
    }
    let set = p.get_set();
    if n == 1 {
        return Some(Term::one(set));
    }
    let derivative: Vec<_> = coefficients
        .iter()
        .enumerate()
        .skip(1)
        .map(|(i, c)| (Term::constant(set.nth(i as i64), set) * c).expand())
        .collect();
    let resultant = sylvester_determinant(&coefficients, &derivative).expand();
    let signed = if (n * (n - 1) / 2) % 2 == 0 {
        resultant
    } else {
        -resultant
    };
    let leading = &coefficients[n];
    let res = (signed * leading.inv()).expand();
    Some(if matches!(leading, Term::Value(_)) {
        res
    } else {
        res.simplify()
    })
}

/// Evaluate the builtins `subs(f, x, a)`, `numer(f)`, `denom(f)`, `resultant(p, q, [x])` and
/// `discriminant(p, [x])`, which work in any ring. Returns `None` for other functions, or when they can't be
/// evaluated.
pub(crate) fn eval_algebra_builtin<T: Ring>(fun: &dyn Function<T>) -> Option<Term<T>> {
    let args = fun.get_args::<T>()?;
    match (fun.get_ident(), args.as_slice()) {
        (Context::SUBS, [f, Term::Symbol(x), a]) => f.substitute(x.symbol, a),
        (Context::NUMER, [f]) => Some(f.as_fraction(true).0),
        (Context::DENOM, [f]) => Some(f.as_fraction(true).1),
        (Context::RESULTANT, [p, q, x @ ..]) => {
            resultant(p, q, polynomial_variable(&[p, q], x.first())?)
        }
        (Context::DISCRIMINANT, [p, x @ ..]) => {
            discriminant(p, polynomial_variable(&[p], x.first())?)
        }
        _ => None,
    }
}
