//! User definitions of variables and functions, like `a := x^2` or `f(x, y) := x*y + a`.
//!
//! Definitions are stored as source code and parsed again wherever they are used, in the set in use there, so a
//! definition isn't tied to a set. A definition captures the definitions existing when it is made: redefining `a`
//! later doesn't change `b := a + 1`, and `a := a + 1` refers to the previous `a`. Arguments of a function are
//! passed by name: each use of a parameter parses the argument again.

use std::{collections::BTreeMap, fmt, rc::Rc};

use crate::{
    context::{
        Context, Symbol,
        assumptions::{Assumption, Assumptions, SignSet},
    },
    field::{Set, SetParseExpression},
    solve::{Equation, Solution, Solve, plain},
    term::{Normalize, Term},
};

use super::{Parser, ParserError, lexer::TokenKind};

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
    },
    /// Assumptions `assume(a > 0, n integer)`, with every assumption on the listed symbols, the new and previous ones.
    Assume(Assumptions),
}

impl<E: Set> fmt::Display for Statement<E> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Expression(term) => write!(f, "{term}"),
            Self::Definition {
                name, params, body, ..
            } => write!(f, "{} := {body}", head(*name, params)),
            Self::System { solution, .. } => write!(f, "{solution}"),
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
    fn parse_equations<E: SetParseExpression>(&mut self, set: E) -> Result<Statement<E>, ParserError> {
        if self.token.kind == TokenKind::Eof {
            return Err(ParserError::new("Input was empty"));
        }
        if self.is_call(Context::SOLVE) {
            return self.parse_solve(set);
        }
        if self.is_call(Context::ASSUME) {
            return self.parse_assume(set);
        }
        let mut items = self.parse_items(set)?;
        self.expect_eof()?;
        if let [(_, None)] = items.as_slice() {
            let (term, _) = items.pop().expect("There is one item");
            return Ok(Statement::Expression(term));
        }
        let equations = items
            .into_iter()
            .map(|(lhs, rhs)| {
                rhs.map(|rhs| Equation::new(lhs, rhs))
                    .ok_or_else(|| ParserError::new("expected `=` in each equation of a system"))
            })
            .collect::<Result<Vec<_>, _>>()?;
        let solution = set.solve(&equations)?;
        Ok(Statement::System {
            equations,
            solution,
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
    fn parse_assumption<E: SetParseExpression>(&mut self, set: E) -> Result<(Symbol, Assumption), ParserError> {
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
        let mut equations = vec![];
        let mut unknowns = vec![];
        for (lhs, rhs) in items {
            if let Some(rhs) = rhs {
                equations.push(Equation::new(lhs, rhs));
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
        if equations.is_empty() {
            return Err(ParserError::new("solve expects at least one equation"));
        }
        let solution = if unknowns.is_empty() {
            set.solve(&equations)?
        } else {
            set.solve_for(&equations, &unknowns)?
        };
        Ok(Statement::System {
            equations,
            solution,
        })
    }

    /// Parse comma-separated items, which are equations `lhs = rhs` or expressions.
    fn parse_items<E: Set>(
        &mut self,
        set: E,
    ) -> Result<Vec<(Term<E>, Option<Term<E>>)>, ParserError> {
        let mut items = vec![];
        loop {
            let lhs = self.parse_side(set)?;
            let rhs = if self.token.kind == TokenKind::Equal {
                self.next_token();
                Some(self.parse_side(set)?)
            } else {
                None
            };
            items.push((lhs, rhs));
            if self.token.kind != TokenKind::Comma {
                return Ok(items);
            }
            self.next_token();
        }
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
