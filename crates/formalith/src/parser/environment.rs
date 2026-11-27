//! User definitions of variables and functions, like `a := x^2` or `f(x, y) := x*y + a`.
//!
//! Definitions are stored as source code and parsed again wherever they are used, in the set in use there, so a
//! definition isn't tied to a set. A definition captures the definitions existing when it is made: redefining `a`
//! later doesn't change `b := a + 1`, and `a := a + 1` refers to the previous `a`. Arguments of a function are
//! passed by name: each use of a parameter parses the argument again.

use std::{
    collections::{BTreeMap, BTreeSet},
    fmt,
    rc::Rc,
};

use crate::{
    context::{
        Context, Symbol,
        assumptions::{Assumption, Assumptions, SignSet, linear::LinearForm},
    },
    field::{Set, SetParseExpression, real::R, real::sign::linear_form},
    ode::{Condition, Dsolve, OdeSolution},
    optimize::{Extrema, Extremum, Optimize},
    solve::{
        Equation, Solution, Solve,
        inequality::{Inequality, Region, SolveInequality},
        is_integer_parameter, is_natural_parameter, plain,
    },
    term::{Expand, Normalize, Term, relation::Relation},
};

use super::{Op, ParseExpression, Parser, ParserError, lexer::TokenKind};

/// Whether `source` is a single identifier.
fn is_identifier(source: &str) -> bool {
    let mut parser = Parser::new(source);
    if !matches!(parser.token.kind, TokenKind::Ident(_)) {
        return false;
    }
    parser.next_token();
    parser.token.kind == TokenKind::Eof
}

/// The variable of the unknown function of a differential equation: its argument where it is called with a
/// symbol, like `y(t)`, `x` otherwise.
fn ode_variable(args: &[String], function: Symbol) -> Symbol {
    for source in args {
        let mut parser = Parser::new(source);
        let mut window: Vec<TokenKind> = vec![];
        while parser.token.kind != TokenKind::Eof {
            window.push(parser.token.kind.clone());
            parser.next_token();
        }
        for tokens in window.windows(4) {
            if let [
                TokenKind::Ident(f),
                TokenKind::OpenParen,
                TokenKind::Ident(t),
                TokenKind::CloseParen,
            ] = tokens
                && Symbol::new(f.as_str()) == function
            {
                return Symbol::new(t.as_str());
            }
        }
    }
    Symbol::new("x")
}

/// A definition `name(params) := body`.
#[derive(Debug)]
pub struct Definition {
    name: Symbol,
    params: Vec<Symbol>,
    body: String,
    env: Environment,
}

impl Definition {
    /// The defined name.
    #[must_use]
    pub const fn name(&self) -> Symbol {
        self.name
    }
    /// The parameters, empty for a variable.
    #[must_use]
    pub fn params(&self) -> &[Symbol] {
        &self.params
    }
    /// The source code of the body.
    #[must_use]
    pub fn body(&self) -> &str {
        &self.body
    }
    /// The definitions the body can refer to.
    pub(crate) const fn env(&self) -> &Environment {
        &self.env
    }
}

impl fmt::Display for Definition {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{} := {}",
            head(self.name, &self.params, false),
            self.body
        )
    }
}

/// Return `name(x, y)`, or `name` if there is no parameter.
pub(crate) fn head(name: Symbol, params: &[Symbol], typst: bool) -> String {
    let print = |symbol: &Symbol| {
        if typst {
            crate::printer::typst_name(symbol.name())
        } else {
            symbol.name().into()
        }
    };
    if params.is_empty() {
        return print(&name).into_owned();
    }
    // A function name as `Fun` prints it in Typst, `op("name")` for several letters
    let name = if typst && name.name().chars().count() != 1 {
        format!("op(\"{}\")", name.name())
    } else {
        name.name().to_owned()
    };
    let params: Vec<_> = params.iter().map(print).collect();
    format!("{name}({})", params.join(", "))
}

/// Variables and functions defined by the user, used by a parser with [`Parser::with_environment`].
///
/// ```
/// use formalith::{field::real::R, parse, parser::environment::Environment};
///
/// let mut env = Environment::new();
/// env.eval("a := 3", R).unwrap();
/// env.eval("f(x) := x^2 + a", R).unwrap();
/// assert_eq!(parse!("f(2)", R, &env), parse!("7", R));
/// ```
#[derive(Debug, Clone, Default)]
pub struct Environment {
    definitions: BTreeMap<Symbol, Rc<Definition>>,
    assumptions: Assumptions,
    defaults: Assumptions,
}

impl Environment {
    /// Create an environment without definitions.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Create an environment without definitions, with the assumptions `defaults`, restored by
    /// [`Environment::clear`].
    #[must_use]
    pub fn with_default_assumptions(defaults: Assumptions) -> Self {
        Self {
            definitions: BTreeMap::new(),
            assumptions: defaults.clone(),
            defaults,
        }
    }

    /// Return the definition of `name`, if any.
    #[must_use]
    pub fn get(&self, name: Symbol) -> Option<&Definition> {
        self.definitions.get(&name).map(Rc::as_ref)
    }

    /// Iterate over the definitions.
    pub fn definitions(&self) -> impl Iterator<Item = &Definition> {
        self.definitions.values().map(Rc::as_ref)
    }

    /// Remove the definition of `name`, returning whether it existed.
    ///
    /// Definitions made before still use it.
    pub fn remove(&mut self, name: &str) -> bool {
        self.definitions.remove(&Symbol::new(name)).is_some()
    }

    /// Remove every definition, and restore the default assumptions.
    pub fn clear(&mut self) {
        self.definitions.clear();
        self.assumptions.clone_from(&self.defaults);
    }

    /// The assumptions on symbols, made with `assume(...)`, used while parsing with this environment.
    #[must_use]
    pub const fn assumptions(&self) -> &Assumptions {
        &self.assumptions
    }

    /// The assumptions the environment started with, see [`Environment::with_default_assumptions`].
    #[must_use]
    pub const fn default_assumptions(&self) -> &Assumptions {
        &self.defaults
    }

    /// Add an assumption on `symbol`.
    ///
    /// # Errors
    /// Returns an error message if it contradicts the existing assumptions on `symbol`.
    pub fn assume(&mut self, symbol: Symbol, assumption: Assumption) -> Result<(), String> {
        self.assumptions.assume(symbol, assumption)
    }

    /// Remove the assumptions on `name`, returning whether there were some.
    pub fn remove_assumptions(&mut self, name: &str) -> bool {
        self.assumptions.remove(Symbol::new(name))
    }

    /// Define `name(params) := body`, capturing the current definitions. Prefer [`Environment::eval`], which
    /// checks the definition.
    pub fn insert(&mut self, name: Symbol, params: Vec<Symbol>, body: String) {
        let env = self.clone();
        self.definitions.insert(
            name,
            Rc::new(Definition {
                name,
                params,
                body,
                env,
            }),
        );
    }

    /// Bind each parameter to the source of an argument, parsed with the definitions of `caller`.
    pub(crate) fn bind(&mut self, params: &[Symbol], args: Vec<String>, caller: &Self) {
        for (&param, arg) in params.iter().zip(args) {
            self.definitions.insert(
                param,
                Rc::new(Definition {
                    name: param,
                    params: vec![],
                    body: arg,
                    env: caller.clone(),
                }),
            );
        }
    }

    /// Parse a statement in `set`, a definition like `f(x) := x^2`, assumptions like `assume(a > 0)` or an
    /// expression, and store definitions and assumptions.
    ///
    /// # Errors
    /// Returns an error if the parsing failed.
    pub fn eval<E: SetParseExpression>(
        &mut self,
        input: &str,
        set: E,
    ) -> Result<Statement<E>, ParserError> {
        let statement = Parser::new(input)
            .with_environment(self)
            .parse_statement(set)?;
        if let Statement::Definition {
            name,
            params,
            source,
            ..
        } = &statement
        {
            self.insert(*name, params.clone(), source.clone());
        }
        if let Statement::Assume(assumptions) = &statement {
            self.assumptions
                .merge(assumptions)
                .map_err(ParserError::new)?;
        }
        Ok(statement)
    }
}

/// A parsed statement, see [`Parser::parse_statement`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Statement<E: Set> {
    /// An expression, evaluated.
    Expression(Term<E>),
    /// A definition `name(params) := body`.
    Definition {
        /// The defined name.
        name: Symbol,
        /// The parameters, empty for a variable.
        params: Vec<Symbol>,
        /// The source code of the body.
        source: String,
        /// The body evaluated with its parameters as symbols.
        body: Term<E>,
    },
    /// A system of equations, like `x + y = 3, x - y = 1`, solved for every symbol, or the extrema of a function,
    /// like `argmin(x^2 - 2 x, x)`.
    System {
        /// The equations, those of the critical points for an extremum.
        equations: Vec<Equation<E>>,
        /// The solutions of the system.
        solution: Solution<E>,
        /// The new integer parameters of the solutions, like `k` in `{$x = pi/6 + 2 k pi$}`.
        integers: Vec<Symbol>,
    },
    /// The global or local minima and maxima of a function with its values there, like `extrema(x^2, x, -1, 2)`
    /// or `localextrema(x^3 - 3 x, x)`.
    Extrema {
        /// The extrema.
        extrema: Extrema<E>,
        /// The new integer parameters of the points, like `k` in `{$x = 2 k pi$}`.
        integers: Vec<Symbol>,
    },
    /// A differential equation `dsolve(y' = y, y(0) = 1)`, solved.
    Ode {
        /// The equation, with the unknown function and its derivatives written `y(x)` and `diff(y(x), x)`.
        equation: Equation<E>,
        /// The solutions of the equation.
        solution: OdeSolution<E>,
    },
    /// Assumptions `assume(a > 0, n integer)`, with every assumption on the listed symbols, the new and previous ones.
    Assume(Assumptions),
    /// Inequalities, like `x^2 < 4`, `x > 0, x^2 < 4` or `x^2 + y^2 < 1, y > 0`, solved.
    Inequalities {
        /// The relations, which may contain equations.
        inequalities: Vec<Inequality<E>>,
        /// The values of the unknowns satisfying every relation.
        solution: Region<E>,
    },
}

/// The integer parameters `k`, `k_1`... and natural parameters `n`, `n_1`... of the periodic solutions of
/// `equations` (see `solve::inverse`), the symbols of `solution` named like them which aren't in the equations.
fn integer_parameters<E: Set>(equations: &[Equation<E>], solution: &Solution<E>) -> Vec<Symbol> {
    new_integer_parameters(equations, solution.symbols())
}

/// The integer and natural parameters among `symbols` which aren't in `equations`.
fn new_integer_parameters<E: Set>(
    equations: &[Equation<E>],
    symbols: BTreeSet<Symbol>,
) -> Vec<Symbol> {
    let used: BTreeSet<Symbol> = equations
        .iter()
        .flat_map(|equation| [&equation.lhs, &equation.rhs])
        .flat_map(Term::symbols)
        .collect();
    symbols
        .into_iter()
        .filter(|symbol| {
            !used.contains(symbol)
                && (is_integer_parameter(*symbol) || is_natural_parameter(*symbol))
        })
        .collect()
}

/// The line `k, k_1 ∈ ℤ, n ∈ ℕ` stating that `integers` are integers, natural parameters being natural numbers,
/// `k, k_1 in ZZ, n in NN` in Typst.
#[must_use]
pub fn integers_line(integers: &[Symbol], typst: bool) -> String {
    let (naturals, integers): (Vec<Symbol>, Vec<Symbol>) = integers
        .iter()
        .partition(|symbol| is_natural_parameter(**symbol));
    let (zz, nn) = if typst {
        ("in ZZ", "in NN")
    } else {
        ("∈ ℤ", "∈ ℕ")
    };
    [(integers, zz), (naturals, nn)]
        .into_iter()
        .filter(|(symbols, _)| !symbols.is_empty())
        .map(|(symbols, set)| {
            let names: Vec<_> = symbols
                .iter()
                .map(|symbol| {
                    if typst {
                        crate::printer::typst_name(symbol.name())
                    } else {
                        symbol.name().into()
                    }
                })
                .collect();
            format!("{} {set}", names.join(", "))
        })
        .collect::<Vec<_>>()
        .join(", ")
}

/// An expression, or a relation `lhs op rhs`, in a list of equations.
type Item<E> = (Term<E>, Option<(Relation, Term<E>)>);

impl<E: Set> fmt::Display for Statement<E> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Expression(term) => write!(f, "{term}"),
            Self::Definition {
                name, params, body, ..
            } => write!(f, "{} := {body}", head(*name, params, false)),
            Self::System {
                solution, integers, ..
            } => {
                write!(f, "{solution}")?;
                if !integers.is_empty() {
                    write!(f, "\n{}", integers_line(integers, false))?;
                }
                Ok(())
            }
            Self::Extrema { extrema, integers } => {
                write!(f, "{extrema}")?;
                if !integers.is_empty() {
                    write!(f, "\n{}", integers_line(integers, false))?;
                }
                Ok(())
            }
            Self::Ode { solution, .. } => write!(f, "{solution}"),
            Self::Inequalities { solution, .. } => write!(f, "{solution}"),
            Self::Assume(assumptions) if assumptions.is_empty() => f.write_str("no assumption"),
            Self::Assume(assumptions) => write!(f, "{assumptions}"),
        }
    }
}

impl Parser<'_> {
    /// Parse a statement: a definition like `f(x) := x^2`, a system of equations like `x + y = 3, x - y = 1`
    /// (solved), or an expression. The definition is checked by parsing its body in `set`, but isn't stored, see
    /// [`Environment::eval`].
    ///
    /// # Errors
    /// This method can return an error if the parsing failed, if the defined name or a parameter is a
    /// builtin, a constant of the set (like `i` in `C`), or a repeated parameter, or if the system can't be solved.
    pub fn parse_statement<E: SetParseExpression>(
        &mut self,
        set: E,
    ) -> Result<Statement<E>, ParserError> {
        profile_scope!("parse_statement");
        let _assumptions = self.env.map(|env| env.assumptions().enter());
        let Some((name, params, body_start)) = self.clone().definition_head() else {
            return self.parse_equations(set);
        };
        let source = self.input[body_start..].trim().to_owned();
        for (i, &symbol) in params.iter().chain([&name]).enumerate() {
            let symbol_name = symbol.name();
            if Context::is_builtin_constant(symbol) {
                return Err(ParserError::new(format!(
                    "`{symbol_name}` is a builtin constant"
                )));
            }
            if Context::builtin_arity(symbol).is_some() {
                return Err(ParserError::new(format!(
                    "`{symbol_name}` is a builtin function"
                )));
            }
            if i < params.len() && params[..i].contains(&symbol) {
                return Err(ParserError::new(format!(
                    "Parameter `{symbol_name}` is repeated"
                )));
            }
            if set.is_constant(symbol_name) {
                return Err(ParserError::new(format!(
                    "`{symbol_name}` is a constant of this set"
                )));
            }
        }
        // Parameters are plain symbols in the body
        let mut env = self.env.cloned().unwrap_or_default();
        for param in &params {
            env.definitions.remove(param);
        }
        let body = Parser::new(&source).with_environment(&env).parse(set)?;
        Ok(Statement::Definition {
            name,
            params,
            source,
            body,
        })
    }

    /// Parse comma-separated equations `lhs = rhs` and solve them, a call to `solve`, or a single expression.
    fn parse_equations<E: SetParseExpression>(
        &mut self,
        set: E,
    ) -> Result<Statement<E>, ParserError> {
        if self.token.kind == TokenKind::Eof {
            return Err(ParserError::new("Input was empty"));
        }
        if self.is_call(Context::SOLVE) {
            return self.parse_solve(set);
        }
        if self.is_call(Context::ASSUME) {
            return self.parse_assume(set);
        }
        if self.is_call(Context::DSOLVE) {
            return self.parse_dsolve(set);
        }
        if [
            Context::ARGMIN,
            Context::ARGMAX,
            Context::LOCALMIN,
            Context::LOCALMAX,
            Context::EXTREMA,
            Context::LOCALEXTREMA,
        ]
        .into_iter()
        .any(|function| self.is_call(function))
        {
            return self.parse_argmin(set);
        }
        let mut items = self.parse_items(set)?;
        self.expect_eof()?;
        if let [(_, None)] = items.as_slice() {
            let (term, _) = items.pop().expect("There is one item");
            return Ok(Statement::Expression(term));
        }
        if let Some(statement) = Self::inequalities(&items, &[], set)? {
            return Ok(statement);
        }
        let equations = items
            .into_iter()
            .map(|(lhs, rhs)| {
                let (relation, rhs) = rhs
                    .ok_or_else(|| ParserError::new("expected `=` in each equation of a system"))?;
                Self::equation(lhs, relation, rhs)
            })
            .collect::<Result<Vec<_>, _>>()?;
        let solution = {
            profile_scope!("solve");
            set.solve(&equations)?
        };
        let integers = integer_parameters(&equations, &solution);
        Ok(Statement::System {
            equations,
            solution,
            integers,
        })
    }

    /// Check if the input starts with `function(`.
    fn is_call(&self, function: Symbol) -> bool {
        let TokenKind::Ident(name) = &self.token.kind else {
            return false;
        };
        let mut parser = self.clone();
        parser.next_token();
        Symbol::new(name.as_str()) == function && parser.token.kind == TokenKind::OpenParen
    }

    /// Parse `assume(a > 0, b != 0, n integer)`, combining the assumptions with those of the environment. Each
    /// argument compares a symbol with 0 (`>`, `<`, `>=`, `<=`, `!=`, on either side), or is `symbol integer`; a
    /// symbol alone only shows its assumptions.
    fn parse_assume<E: SetParseExpression>(&mut self, set: E) -> Result<Statement<E>, ParserError> {
        // `assume(`
        self.next_token();
        self.next_token();
        let mut items = vec![];
        loop {
            items.push(self.parse_assumption(set)?);
            match self.token.kind {
                TokenKind::Comma => self.next_token(),
                TokenKind::CloseParen => break,
                _ => {
                    return Err(ParserError::new(format!(
                        "Unexpected token at position {}, expected `,` or `)`",
                        self.start_span
                    )));
                }
            }
        }
        self.next_token();
        self.expect_eof()?;
        // The previous assumptions on the symbols mentioned, then the new ones
        let symbols: BTreeSet<Symbol> = items
            .iter()
            .flat_map(|item| match item {
                AssumeItem::Listed(s) | AssumeItem::Integer(s) => vec![*s],
                AssumeItem::Relation(form, _) => form.symbols().collect(),
            })
            .collect();
        let mut assumptions = self
            .env
            .map_or_else(Assumptions::new, |env| env.assumptions().restrict(&symbols));
        for item in items {
            match item {
                AssumeItem::Listed(_) => Ok(()),
                AssumeItem::Integer(s) => assumptions
                    .assume_integer(s)
                    .map_err(|err| format!("`{}`: {err}", s.name())),
                AssumeItem::Relation(form, signs) => assumptions.assume_relation(&form, signs),
            }
            .map_err(ParserError::new)?;
        }
        Ok(Statement::Assume(assumptions))
    }

    /// Parse an argument of `assume`: a symbol, `symbol integer`, or a linear relation like `a > 2*b + 1`.
    fn parse_assumption<E: SetParseExpression>(
        &mut self,
        set: E,
    ) -> Result<AssumeItem, ParserError> {
        let symbol = |term: &Term<E>| {
            let Term::Symbol(symbol) = term else {
                return Err(ParserError::new(format!(
                    "`{}` is not a symbol, assumptions are about symbols",
                    plain(term)
                )));
            };
            let symbol = symbol.symbol;
            if Context::is_builtin_constant(symbol) || set.is_constant(symbol.name()) {
                return Err(ParserError::new(format!(
                    "`{}` is a constant",
                    symbol.name()
                )));
            }
            Ok(symbol)
        };
        // `n integer`, read before the side, where it would be the implicit product `n*integer`
        let mut ahead = self.clone();
        if let Some(lhs) =
            ParseExpression::<E>::parse_expression(&mut ahead, Op::Multiply.get_priority(), set)?
            && matches!(&ahead.token.kind, TokenKind::Ident(word) if word == "integer")
        {
            ahead.next_token();
            *self = ahead;
            return Ok(AssumeItem::Integer(symbol(&lhs.normalize())?));
        }
        let lhs_start = self.start_span;
        let lhs = self.parse_side(set)?;
        let lhs_source = self.input[lhs_start..self.start_span].trim().to_owned();
        let signs = match self.token.kind {
            TokenKind::Less => SignSet::NEGATIVE,
            TokenKind::LessEqual => SignSet::NONPOSITIVE,
            TokenKind::Greater => SignSet::POSITIVE,
            TokenKind::GreaterEqual => SignSet::NONNEGATIVE,
            TokenKind::NotEqual => SignSet::NONZERO,
            TokenKind::Equal => SignSet::ZERO,
            _ => return Ok(AssumeItem::Listed(symbol(&lhs)?)),
        };
        self.next_token();
        let rhs_start = self.start_span;
        self.parse_side(set)?;
        let rhs_source = self.input[rhs_start..self.start_span].trim().to_owned();
        // Read again as real expressions, whatever the set
        let parse = |source: &str| {
            let parser = Parser::new(source);
            let mut parser = match self.env {
                Some(env) => parser.with_environment(env),
                None => parser,
            };
            parser.parse(R)
        };
        let difference = (parse(&lhs_source)? - parse(&rhs_source)?).expand();
        if let Some(constant) = difference
            .symbols()
            .into_iter()
            .find(|s| Context::is_builtin_constant(*s) || set.is_constant(s.name()))
        {
            return Err(ParserError::new(format!(
                "`{}` is a constant",
                constant.name()
            )));
        }
        let form = linear_form(&difference).ok_or_else(|| {
            ParserError::new(
                "assumptions are linear relations with rational coefficients, like `a > 2*b + 1`",
            )
        })?;
        if form.is_constant() {
            return Err(ParserError::new("this assumption has no symbol"));
        }
        Ok(AssumeItem::Relation(form, signs))
    }

    /// Parse `solve(equations, unknowns)`, where the unknowns are symbols to solve for, other symbols being
    /// parameters. Without unknowns, every symbol is an unknown.
    fn parse_solve<E: Set>(&mut self, set: E) -> Result<Statement<E>, ParserError> {
        // `solve(`
        self.next_token();
        self.next_token();
        let items = self.parse_items(set)?;
        self.expect_token(&TokenKind::CloseParen)?;
        self.expect_eof()?;
        let mut relations = vec![];
        let mut unknowns = vec![];
        for (lhs, rhs) in items {
            if rhs.is_some() {
                relations.push((lhs, rhs));
                continue;
            }
            let Term::Symbol(symbol) = lhs else {
                return Err(ParserError::new(format!(
                    "`{}` is not an unknown, expected an equation or a symbol",
                    plain(&lhs)
                )));
            };
            if Context::is_builtin_constant(symbol.symbol) {
                return Err(ParserError::new(format!(
                    "`{}` is a builtin constant, not an unknown",
                    symbol.symbol.name()
                )));
            }
            if unknowns.contains(&symbol.symbol) {
                return Err(ParserError::new(format!(
                    "Unknown `{}` is repeated",
                    symbol.symbol.name()
                )));
            }
            unknowns.push(symbol.symbol);
        }
        if relations.is_empty() {
            return Err(ParserError::new("solve expects at least one equation"));
        }
        if let Some(statement) = Self::inequalities(&relations, &unknowns, set)? {
            return Ok(statement);
        }
        let equations = relations
            .into_iter()
            .map(|(lhs, rhs)| {
                let (relation, rhs) = rhs.expect("Relations have a right side");
                Self::equation(lhs, relation, rhs)
            })
            .collect::<Result<Vec<_>, _>>()?;
        let solution = {
            profile_scope!("solve");
            if unknowns.is_empty() {
                set.solve(&equations)?
            } else {
                set.solve_for(&equations, &unknowns)?
            }
        };
        let integers = integer_parameters(&equations, &solution);
        Ok(Statement::System {
            equations,
            solution,
            integers,
        })
    }

    /// Parse `argmin(f, x_1, ..., x_n)`, `argmin(f, x, a, b)` or the same with `argmax`, `localmin`, `localmax`,
    /// `extrema` or `localextrema`, finding the points where `f` reaches its global or local extrema (both kinds
    /// with the values of `f` for the last two). The variables are every symbol of `f` sorted by name when there
    /// is none. With one variable and two more arguments which aren't both symbols of `f`, they are the bounds.
    fn parse_argmin<E: SetParseExpression>(&mut self, set: E) -> Result<Statement<E>, ParserError> {
        // `None` for both kinds, global or local
        let (function, extremum) = [
            (Context::ARGMIN, Some(Extremum::GlobalMin)),
            (Context::ARGMAX, Some(Extremum::GlobalMax)),
            (Context::LOCALMIN, Some(Extremum::LocalMin)),
            (Context::LOCALMAX, Some(Extremum::LocalMax)),
            (Context::EXTREMA, None),
            (Context::LOCALEXTREMA, None),
        ]
        .into_iter()
        .find(|(function, _)| self.is_call(*function))
        .expect("The statement is a call to an extremum function");
        let name = function.name();
        // `argmin(`
        self.next_token();
        self.next_token();
        let items = self.parse_items(set)?;
        self.expect_token(&TokenKind::CloseParen)?;
        self.expect_eof()?;
        let mut args = vec![];
        for (term, rhs) in items {
            if rhs.is_some() {
                return Err(ParserError::new(format!(
                    "{name} expects a function and its variables, not a relation"
                )));
            }
            args.push(term);
        }
        let f = args.remove(0);
        let symbols = f.symbols();
        let symbol_of_f =
            |term: &Term<E>| matches!(term, Term::Symbol(s) if symbols.contains(&s.symbol));
        let (variables, bounds) = match args.as_slice() {
            [x, a, b] if !(symbol_of_f(a) && symbol_of_f(b)) => {
                (std::slice::from_ref(x), Some((a.clone(), b.clone())))
            }
            variables => (variables, None),
        };
        let mut unknowns = vec![];
        for variable in variables {
            let Term::Symbol(symbol) = variable else {
                return Err(ParserError::new(format!(
                    "`{}` is not a variable, expected a symbol",
                    plain(variable)
                )));
            };
            let symbol = symbol.symbol;
            if Context::is_builtin_constant(symbol) || set.is_constant(symbol.name()) {
                return Err(ParserError::new(format!(
                    "`{}` is a constant, not a variable",
                    symbol.name()
                )));
            }
            if unknowns.contains(&symbol) {
                return Err(ParserError::new(format!(
                    "Variable `{}` is repeated",
                    symbol.name()
                )));
            }
            unknowns.push(symbol);
        }
        if unknowns.is_empty() {
            unknowns = symbols
                .iter()
                .copied()
                .filter(|s| !Context::is_builtin_constant(*s) && !set.is_constant(s.name()))
                .collect();
            unknowns.sort_by(|a, b| a.name().cmp(b.name()));
            if unknowns.is_empty() {
                return Err(ParserError::new(format!(
                    "{name} expects a function of at least one variable"
                )));
            }
        }
        let Some(extremum) = extremum else {
            let extrema = set.extrema(
                &f,
                &unknowns,
                bounds.as_ref(),
                function == Context::LOCALEXTREMA,
            )?;
            let symbols = extrema
                .points
                .iter()
                .flat_map(|point| {
                    point
                        .point
                        .iter()
                        .map(|(_, value)| value)
                        .chain([&point.value])
                })
                .flat_map(Term::symbols)
                .collect();
            let integers = new_integer_parameters(&extrema.equations, symbols);
            return Ok(Statement::Extrema { extrema, integers });
        };
        let optimum = set.optimize(&f, &unknowns, bounds.as_ref(), extremum)?;
        let integers = integer_parameters(&optimum.equations, &optimum.solution);
        Ok(Statement::System {
            equations: optimum.equations,
            solution: optimum.solution,
            integers,
        })
    }

    /// Parse `dsolve(equation, conditions, y, x)`, solving the differential equation for `y(x)` with initial
    /// conditions like `y(0) = 1` or `y'(0) = 0`. In the equation, `y'`, `y''`... are the derivatives of `y`, and
    /// `y` stands for `y(x)`. Without `y` and `x`, `y` is the first identifier followed by `'`, or else called
    /// like a function, and `x` is its argument if it is a symbol, `x` otherwise.
    fn parse_dsolve<E: SetParseExpression>(&mut self, set: E) -> Result<Statement<E>, ParserError> {
        // `dsolve(`
        self.next_token();
        self.next_token();
        let mut args = self.parse_args_source()?;
        self.expect_eof()?;
        let mut names = vec![];
        while names.len() < 2 && args.len() > 1 && args.last().is_some_and(|arg| is_identifier(arg))
        {
            names.insert(0, Symbol::new(args.pop().expect("There is an argument")));
        }
        let function = match names.first() {
            Some(&function) => function,
            None => self.ode_function(&args).ok_or_else(|| {
                ParserError::new(
                    "can't find the unknown function, name it like in `dsolve(y' = y, y, x)`",
                )
            })?,
        };
        let x = names
            .get(1)
            .copied()
            .unwrap_or_else(|| ode_variable(&args, function));
        for symbol in [function, x] {
            if Context::is_builtin_constant(symbol)
                || Context::builtin_arity(symbol).is_some()
                || set.is_constant(symbol.name())
            {
                return Err(ParserError::new(format!(
                    "`{}` is a builtin or a constant",
                    symbol.name()
                )));
            }
        }
        if function == x {
            return Err(ParserError::new(
                "the function and its variable must be different",
            ));
        }
        let mut equation = None;
        let mut conditions = vec![];
        for source in &args {
            if let Some(condition) = self.parse_condition(source, function, x, set)? {
                conditions.push(condition);
                continue;
            }
            if equation.is_some() {
                return Err(ParserError::new(
                    "dsolve expects a single equation, then initial conditions",
                ));
            }
            let mut parser = Parser::new(source).with_ode(function, x);
            parser.env = self.env;
            let lhs = parser.parse_side(set)?;
            parser.expect_token(&TokenKind::Equal).map_err(|_| {
                ParserError::new(format!("expected `=` in the equation `{source}`"))
            })?;
            let rhs = parser.parse_side(set)?;
            parser.expect_eof()?;
            equation = Some(Equation::new(lhs, rhs));
        }
        let equation = equation.ok_or_else(|| ParserError::new("dsolve expects an equation"))?;
        let solution = {
            profile_scope!("dsolve");
            set.dsolve(&equation, &conditions, function, x)?
        };
        Ok(Statement::Ode { equation, solution })
    }

    /// The unknown function of a differential equation: the first identifier followed by `'`, or else the first
    /// one called like a function which isn't a builtin, a definition or a constant.
    fn ode_function(&self, args: &[String]) -> Option<Symbol> {
        let identifiers = |source: &str| {
            let mut parser = Parser::new(source);
            let mut res = vec![];
            while parser.token.kind != TokenKind::Eof {
                parser.next_token();
                if let TokenKind::Ident(name) = &parser.prev_token.kind {
                    res.push((Symbol::new(name.as_str()), parser.token.kind.clone()));
                }
            }
            res
        };
        let calls: Vec<_> = args.iter().flat_map(|arg| identifiers(arg)).collect();
        // Derivatives of builtins and definitions, like `f'(x)`, aren't the unknown function
        let unknown = |symbol: Symbol| {
            Context::builtin_arity(symbol).is_none()
                && self.env.is_none_or(|env| env.get(symbol).is_none())
        };
        calls
            .iter()
            .find(|(symbol, next)| *next == TokenKind::Prime && unknown(*symbol))
            .or_else(|| {
                calls
                    .iter()
                    .find(|(symbol, next)| *next == TokenKind::OpenParen && unknown(*symbol))
            })
            .map(|(symbol, _)| *symbol)
    }

    /// Parse an initial condition `y''(a) = b`, returning `None` if `source` isn't one (like `y(x) = ...`).
    fn parse_condition<E: SetParseExpression>(
        &self,
        source: &str,
        function: Symbol,
        x: Symbol,
        set: E,
    ) -> Result<Option<Condition<E>>, ParserError> {
        let mut parser = Parser::new(source);
        parser.env = self.env;
        if !matches!(&parser.token.kind, TokenKind::Ident(name) if Symbol::new(name.as_str()) == function)
        {
            return Ok(None);
        }
        parser.next_token();
        let mut order = 0;
        while parser.token.kind == TokenKind::Prime {
            order += 1;
            parser.next_token();
        }
        if parser.token.kind != TokenKind::OpenParen {
            return Ok(None);
        }
        parser.next_token();
        let point = parser.parse_side(set)?;
        if parser.token.kind != TokenKind::CloseParen
            || matches!(&point, Term::Symbol(s) if s.symbol == x)
        {
            return Ok(None);
        }
        parser.next_token();
        if parser.token.kind != TokenKind::Equal {
            return Ok(None);
        }
        parser.next_token();
        let value = parser.parse_side(set)?;
        parser.expect_eof()?;
        if [&point, &value].iter().any(|t| t.symbols().contains(&x)) {
            return Err(ParserError::new(format!(
                "the initial condition `{source}` can't depend on `{}`",
                x.name()
            )));
        }
        Ok(Some(Condition {
            order,
            point,
            value,
        }))
    }

    /// Parse comma-separated items, which are equations `lhs = rhs` or expressions.
    fn parse_items<E: Set>(&mut self, set: E) -> Result<Vec<Item<E>>, ParserError> {
        let mut items = vec![];
        loop {
            let lhs = self.parse_side(set)?;
            let rhs = match Relation::from_token(&self.token.kind) {
                Some(relation) => {
                    self.next_token();
                    Some((relation, self.parse_side(set)?))
                }
                None => None,
            };
            items.push((lhs, rhs));
            if self.token.kind != TokenKind::Comma {
                return Ok(items);
            }
            self.next_token();
        }
    }

    /// Solve `items` as inequalities if one of them is an inequality, for `unknowns` or all their symbols.
    fn inequalities<E: Set>(
        items: &[Item<E>],
        unknowns: &[Symbol],
        set: E,
    ) -> Result<Option<Statement<E>>, ParserError> {
        let is_inequality = |item: &Item<E>| matches!(item, (_, Some((relation, _))) if *relation != Relation::Equal);
        if !items.iter().any(is_inequality) {
            return Ok(None);
        }
        let inequalities = items
            .iter()
            .map(|(lhs, rhs)| match rhs {
                Some((relation, rhs)) => Ok(Inequality::new(lhs.clone(), *relation, rhs.clone())),
                None => Err(ParserError::new(format!(
                    "`{}` is not a relation, expected `=`, `<`, `<=`, `>`, `>=` or `!=`",
                    plain(lhs)
                ))),
            })
            .collect::<Result<Vec<_>, _>>()?;
        let solution = set.solve_inequalities(&inequalities, unknowns)?;
        Ok(Some(Statement::Inequalities {
            inequalities,
            solution,
        }))
    }

    /// Equations `lhs = rhs` of `items`, or an error for other relations.
    fn equation<E: Set>(
        lhs: Term<E>,
        relation: Relation,
        rhs: Term<E>,
    ) -> Result<Equation<E>, ParserError> {
        if relation == Relation::NotEqual {
            return Err(ParserError::new("`!=` is only allowed in inequalities"));
        }
        Ok(Equation::new(lhs, rhs))
    }

    /// Parse a side of an equation, normalized.
    fn parse_side<E: Set>(&mut self, set: E) -> Result<Term<E>, ParserError> {
        let position = self.start_span;
        self.parse_operand(set)?
            .map(|term| term.normalize())
            .ok_or_else(|| ParserError::new(format!("Expression expected at position {position}")))
    }

    /// Check if the input is a definition, like `f(x) := x^2`, without checking its body.
    #[must_use]
    pub fn is_definition(&self) -> bool {
        self.clone().definition_head().is_some()
    }

    /// Check if the input declares assumptions, like `assume(a > 0)`, without checking them.
    #[must_use]
    pub fn is_assumption(&self) -> bool {
        self.is_call(Context::ASSUME)
    }

    /// Parse `name :=` or `name(params) :=`, returning the name, the parameters and the position of the body.
    fn definition_head(&mut self) -> Option<(Symbol, Vec<Symbol>, usize)> {
        let TokenKind::Ident(name) = &self.token.kind else {
            return None;
        };
        let name = Symbol::new(name.as_str());
        self.next_token();
        let mut params = vec![];
        if self.token.kind == TokenKind::OpenParen {
            loop {
                self.next_token();
                let TokenKind::Ident(param) = &self.token.kind else {
                    return None;
                };
                params.push(Symbol::new(param.as_str()));
                self.next_token();
                match self.token.kind {
                    TokenKind::Comma => {}
                    TokenKind::CloseParen => break,
                    _ => return None,
                }
            }
            self.next_token();
        }
        (self.token.kind == TokenKind::Define).then_some((name, params, self.end_span))
    }
}

/// An argument of `assume`, see [`Parser::parse_assumption`].
enum AssumeItem {
    /// A symbol, whose assumptions are shown.
    Listed(Symbol),
    /// `symbol integer`.
    Integer(Symbol),
    /// A linear form in symbols with the signs it has.
    Relation(LinearForm, SignSet),
}
