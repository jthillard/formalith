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
        assumptions::{Assumption, Assumptions, SignSet},
    },
    field::{Set, SetParseExpression},
    ode::{Condition, Dsolve, OdeSolution},
    solve::{
        Equation, Solution, Solve,
        inequality::{Inequality, Intervals, SolveInequality},
        is_integer_parameter, plain,
    },
    term::{Normalize, Term, relation::Relation},
};

use super::{Parser, ParserError, lexer::TokenKind};

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
        write!(f, "{} := {}", head(self.name, &self.params), self.body)
    }
}

/// Return `name(x, y)`, or `name` if there is no parameter.
pub(crate) fn head(name: Symbol, params: &[Symbol]) -> String {
    let name = name.name();
    if params.is_empty() {
        return name.to_owned();
    }
    let params: Vec<&str> = params.iter().map(|param| param.name()).collect();
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
}

impl Environment {
    /// Create an environment without definitions.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
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

    /// Remove every definition and assumption.
    pub fn clear(&mut self) {
        self.definitions.clear();
        self.assumptions.clear();
    }

    /// The assumptions on symbols, made with `assume(...)`, used while parsing with this environment.
    #[must_use]
    pub const fn assumptions(&self) -> &Assumptions {
        &self.assumptions
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
            for (symbol, assumption) in assumptions.iter() {
                self.assume(symbol, assumption).map_err(ParserError::new)?;
            }
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
    /// A system of equations, like `x + y = 3, x - y = 1`, solved for every symbol.
    System {
        /// The equations.
        equations: Vec<Equation<E>>,
        /// The solutions of the system.
        solution: Solution<E>,
        /// The new integer parameters of the solutions, like `k` in `{$x = pi/6 + 2 k pi$}`.
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
    /// Inequalities in one unknown, like `x^2 < 4` or `x > 0, x^2 < 4`, solved.
    Inequalities {
        /// The relations, which may contain equations.
        inequalities: Vec<Inequality<E>>,
        /// The values of the unknown satisfying every relation.
        solution: Intervals<E>,
    },
}

/// The integer parameters `k`, `k_1`... of the periodic solutions of `equations` (see `solve::inverse`), the
/// symbols of `solution` named like them which aren't in the equations.
fn integer_parameters<E: Set>(equations: &[Equation<E>], solution: &Solution<E>) -> Vec<Symbol> {
    let used: BTreeSet<Symbol> = equations
        .iter()
        .flat_map(|equation| [&equation.lhs, &equation.rhs])
        .flat_map(Term::symbols)
        .collect();
    solution
        .symbols()
        .into_iter()
        .filter(|symbol| !used.contains(symbol) && is_integer_parameter(*symbol))
        .collect()
}

/// The line `k, k_1 ∈ ℤ` stating that `integers` are integers, `k, k_1 in ZZ` in Typst.
#[must_use]
pub fn integers_line(integers: &[Symbol], typst: bool) -> String {
    let names: Vec<_> = integers.iter().map(|symbol| symbol.name()).collect();
    if typst {
        format!("{} in ZZ", names.join(", "))
    } else {
        format!("{} ∈ ℤ", names.join(", "))
    }
}

/// An expression, or a relation `lhs op rhs`, in a list of equations.
type Item<E> = (Term<E>, Option<(Relation, Term<E>)>);

impl<E: Set> fmt::Display for Statement<E> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Expression(term) => write!(f, "{term}"),
            Self::Definition {
                name, params, body, ..
            } => write!(f, "{} := {body}", head(*name, params)),
            Self::System {
                solution, integers, ..
            } => {
                write!(f, "{solution}")?;
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

impl<'a> Parser<'a> {
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
        let mut items = self.parse_items(set)?;
        self.expect_eof()?;
        if let [(_, None)] = items.as_slice() {
            let (term, _) = items.pop().expect("There is one item");
            return Ok(Statement::Expression(term));
        }
        if let Some(statement) = Self::inequalities(&items, None, set)? {
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
        let solution = set.solve(&equations)?;
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
        let mut assumptions = Assumptions::new();
        loop {
            let (symbol, assumption) = self.parse_assumption(set)?;
            let previous = self
                .env
                .map_or(Assumption::NONE, |env| env.assumptions().get(symbol));
            if assumptions.get(symbol) == Assumption::NONE {
                assumptions
                    .assume(symbol, previous)
                    .map_err(ParserError::new)?;
            }
            assumptions
                .assume(symbol, assumption)
                .map_err(|err| ParserError::new(format!("`{}`: {err}", symbol.name())))?;
            if previous == Assumption::NONE && assumptions.get(symbol) == Assumption::NONE {
                // Listed, but without assumption
                assumptions.remove(symbol);
            }
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
        Ok(Statement::Assume(assumptions))
    }

    /// Parse an argument of `assume`, returning the symbol and what is assumed.
    fn parse_assumption<E: SetParseExpression>(
        &mut self,
        set: E,
    ) -> Result<(Symbol, Assumption), ParserError> {
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
        let lhs_start = self.start_span;
        let lhs = self.parse_side(set)?;
        let lhs_source = self.input[lhs_start..self.start_span].trim().to_owned();
        let relation = match self.token.kind {
            TokenKind::Less => SignSet::NEGATIVE,
            TokenKind::LessEqual => SignSet::NONPOSITIVE,
            TokenKind::Greater => SignSet::POSITIVE,
            TokenKind::GreaterEqual => SignSet::NONNEGATIVE,
            TokenKind::NotEqual => SignSet::NONZERO,
            TokenKind::Ident(ref name) if name == "integer" => {
                self.next_token();
                return Ok((symbol(&lhs)?, Assumption::INTEGER));
            }
            _ => return Ok((symbol(&lhs)?, Assumption::NONE)),
        };
        self.next_token();
        let rhs_start = self.start_span;
        let rhs = self.parse_side(set)?;
        let rhs_source = self.input[rhs_start..self.start_span].trim();
        // `0 < a` is `a > 0`
        let (term, relation) = if lhs_source == "0" {
            (rhs, relation.neg())
        } else if rhs_source == "0" {
            (lhs, relation)
        } else {
            return Err(ParserError::new(
                "assumptions compare a symbol with 0, like `a > 0`",
            ));
        };
        Ok((symbol(&term)?, Assumption::sign(relation)))
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
        if let Some(statement) = Self::inequalities(&relations, unknowns.first().copied(), set)? {
            if unknowns.len() > 1 {
                return Err(ParserError::new(
                    "inequalities are solved for a single unknown",
                ));
            }
            return Ok(statement);
        }
        let equations = relations
            .into_iter()
            .map(|(lhs, rhs)| {
                let (relation, rhs) = rhs.expect("Relations have a right side");
                Self::equation(lhs, relation, rhs)
            })
            .collect::<Result<Vec<_>, _>>()?;
        let solution = if unknowns.is_empty() {
            set.solve(&equations)?
        } else {
            set.solve_for(&equations, &unknowns)?
        };
        let integers = integer_parameters(&equations, &solution);
        Ok(Statement::System {
            equations,
            solution,
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
        let solution = set.dsolve(&equation, &conditions, function, x)?;
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
        calls
            .iter()
            .find(|(_, next)| *next == TokenKind::Prime)
            .or_else(|| {
                calls.iter().find(|(symbol, next)| {
                    *next == TokenKind::OpenParen
                        && Context::builtin_arity(*symbol).is_none()
                        && self.env.is_none_or(|env| env.get(*symbol).is_none())
                })
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

    /// Solve `items` as inequalities if one of them is an inequality, for `unknown` or their only symbol.
    fn inequalities<E: Set>(
        items: &[Item<E>],
        unknown: Option<Symbol>,
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
        let solution = set.solve_inequalities(&inequalities, unknown)?;
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
