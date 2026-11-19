//! User definitions of variables and functions, like `a := x^2` or `f(x, y) := x*y + a`.
//!
//! Definitions are stored as source code and parsed again wherever they are used, in the set in use there, so a
//! definition isn't tied to a set. A definition captures the definitions existing when it is made: redefining `a`
//! later doesn't change `b := a + 1`, and `a := a + 1` refers to the previous `a`. Arguments of a function are
//! passed by name: each use of a parameter parses the argument again.

use std::{collections::BTreeMap, fmt, rc::Rc};

use crate::{
    context::{Context, Symbol},
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

    /// Remove every definition.
    pub fn clear(&mut self) {
        self.definitions.clear();
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

    /// Parse a statement in `set`, a definition like `f(x) := x^2` or an expression, and store definitions.
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
}

impl<E: Set> fmt::Display for Statement<E> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Expression(term) => write!(f, "{term}"),
            Self::Definition {
                name, params, body, ..
            } => write!(f, "{} := {body}", head(*name, params)),
            Self::System { solution, .. } => write!(f, "{solution}"),
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
    fn parse_equations<E: Set>(&mut self, set: E) -> Result<Statement<E>, ParserError> {
        if self.token.kind == TokenKind::Eof {
            return Err(ParserError::new("Input was empty"));
        }
        if self.is_solve_call() {
            return self.parse_solve(set);
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

    /// Check if the input starts with `solve(`.
    fn is_solve_call(&self) -> bool {
        let TokenKind::Ident(name) = &self.token.kind else {
            return false;
        };
        let mut parser = self.clone();
        parser.next_token();
        Symbol::new(name.as_str()) == Context::SOLVE && parser.token.kind == TokenKind::OpenParen
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
