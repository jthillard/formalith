//! The syntax of an input line, parsed without evaluating it, so that it can be shown as it was typed.
//!
//! [`Parser`](super::Parser) normalizes while parsing (`{$x - y$}` is `{$x + (-1) y$}`, calls are evaluated,
//! definitions expanded), so its terms can't print the input. This module parses the same grammar into a syntax tree
//! with the same priorities and implicit products, printed as Typst math by [`input_typst`].

use std::fmt::Write;

use crate::{
    context::{Context, Symbol},
    printer::{typst_function_name, typst_name},
    term::relation::Relation,
};

use super::{
    Op, implicit_product,
    lexer::{Lexer, LiteralTokenKind, TokenKind},
};

/// The input `input` as Typst math source, or `None` if it isn't a valid input.
///
/// Nothing is evaluated: definitions and calls are shown as they were typed, `integrate(x^2, x, 0, 1)` as
/// `{$integral_(0)^(1) x^(2) dif x$}`.
///
/// ```
/// use formalith::parser::syntax::input_typst;
///
/// assert_eq!(input_typst("(x + 1)/2").as_deref(), Some("frac(x + 1, 2)"));
/// assert_eq!(input_typst("x +"), None);
/// ```
#[must_use]
pub fn input_typst(input: &str) -> Option<String> {
    let mut parser = SyntaxParser::new(input)?;
    let statement = parser.statement()?;
    let mut res = String::new();
    match statement {
        Statement::Definition(head, body) => {
            print(&head, &mut res);
            res.push_str(" := ");
            print(&body, &mut res);
        }
        Statement::Items(items) => {
            for (i, item) in items.iter().enumerate() {
                if i != 0 {
                    res.push_str(", quad ");
                }
                print(item, &mut res);
            }
        }
    }
    Some(res)
}

/// A node of the syntax tree of an input.
#[derive(Debug)]
enum Node<'a> {
    /// A number literal, as written.
    Number(&'a str),
    /// A boolean literal.
    Bool(&'a str),
    /// An identifier.
    Ident(&'a str),
    /// An expression in parentheses.
    Group(Box<Self>),
    /// `-u`
    Neg(Box<Self>),
    /// A binary operation, explicit or an implicit product.
    Binary(Op, Box<Self>, Box<Self>),
    /// `u!`
    Factorial(Box<Self>),
    /// `f(a, b)`, or `f''(a)` with `primes` primes.
    Call {
        name: &'a str,
        primes: usize,
        args: Vec<Self>,
    },
    /// `[[a, b], [c, d]]`
    Matrix(Vec<Vec<Self>>),
    /// `lhs < rhs`
    Relation(Relation, Box<Self>, Box<Self>),
}

/// A whole input: a definition `head := body`, or comma-separated expressions and relations.
enum Statement<'a> {
    Definition(Node<'a>, Node<'a>),
    Items(Vec<Node<'a>>),
}

/// A Pratt parser over the tokens of an input, see [`Parser`](super::Parser).
struct SyntaxParser<'a> {
    /// The tokens, without whitespace, with their text.
    tokens: Vec<(TokenKind, &'a str)>,
    pos: usize,
}

impl<'a> SyntaxParser<'a> {
    /// The parser over the tokens of `input`, `None` if it has an unknown character.
    fn new(input: &'a str) -> Option<Self> {
        let mut tokens = vec![];
        let mut start = 0;
        for token in Lexer::new(input) {
            let text = &input[start..start + token.len];
            start += token.len;
            match token.kind {
                TokenKind::Whitespace => {}
                TokenKind::Unknown => return None,
                kind => tokens.push((kind, text)),
            }
        }
        Some(Self { tokens, pos: 0 })
    }

    fn peek(&self) -> &TokenKind {
        self.tokens
            .get(self.pos)
            .map_or(&TokenKind::Eof, |(kind, _)| kind)
    }

    /// The current token and its text, moving to the next one.
    fn next(&mut self) -> (TokenKind, &'a str) {
        let token = self
            .tokens
            .get(self.pos)
            .cloned()
            .unwrap_or((TokenKind::Eof, ""));
        self.pos += 1;
        token
    }

    /// Move past the current token if it is `kind`.
    fn eat(&mut self, kind: &TokenKind) -> Option<()> {
        (self.peek() == kind).then(|| {
            self.pos += 1;
        })
    }

    /// The operator at the current token, juxtaposed operands being an implicit product, like
    /// [`Parser::get_op`](super::Parser).
    fn op(&self) -> Option<Op> {
        if let Some((prev, _)) = self.pos.checked_sub(1).and_then(|i| self.tokens.get(i))
            && implicit_product(prev, self.peek())
        {
            return Some(Op::Multiply);
        }
        match self.peek() {
            TokenKind::Plus => Some(Op::Add),
            TokenKind::Minus => Some(Op::Subtract),
            TokenKind::Star => Some(Op::Multiply),
            TokenKind::Slash => Some(Op::Divide),
            TokenKind::Caret => Some(Op::Pow),
            _ => None,
        }
    }

    /// The whole input, `None` if tokens are left.
    fn statement(&mut self) -> Option<Statement<'a>> {
        let statement = if self
            .tokens
            .iter()
            .any(|(kind, _)| *kind == TokenKind::Define)
        {
            let head = self.expression(0)?;
            let is_head = match &head {
                Node::Ident(_) => true,
                Node::Call {
                    primes: 0, args, ..
                } => args.iter().all(|arg| matches!(arg, Node::Ident(_))),
                _ => false,
            };
            if !is_head {
                return None;
            }
            self.eat(&TokenKind::Define)?;
            Statement::Definition(head, self.expression(0)?)
        } else {
            Statement::Items(self.items()?)
        };
        (*self.peek() == TokenKind::Eof).then_some(statement)
    }

    /// Comma-separated expressions or relations.
    fn items(&mut self) -> Option<Vec<Node<'a>>> {
        let mut items = vec![];
        loop {
            let lhs = self.expression(0)?;
            items.push(match Relation::from_token(self.peek()) {
                Some(relation) => {
                    self.pos += 1;
                    Node::Relation(relation, Box::new(lhs), Box::new(self.expression(0)?))
                }
                None => lhs,
            });
            if self.eat(&TokenKind::Comma).is_none() {
                return Some(items);
            }
        }
    }

    /// An expression whose operators bind tighter than `priority`.
    fn expression(&mut self, priority: usize) -> Option<Node<'a>> {
        let mut node = self.operand()?;
        while *self.peek() == TokenKind::Bang {
            self.pos += 1;
            node = Node::Factorial(Box::new(node));
        }
        while let Some(op) = self.op()
            && priority < op.get_priority()
        {
            if !matches!(self.peek(), TokenKind::OpenParen | TokenKind::Ident(_)) {
                self.pos += 1;
            }
            // `^` is right-associative
            let right = self.expression(if op == Op::Pow {
                op.get_priority() - 1
            } else {
                op.get_priority()
            })?;
            node = Node::Binary(op, Box::new(node), Box::new(right));
        }
        Some(node)
    }

    /// An operand: a literal, an identifier, a call, a group, a matrix or a signed operand.
    fn operand(&mut self) -> Option<Node<'a>> {
        match self.next() {
            (TokenKind::Plus, _) => self.expression(Op::Multiply.get_priority()),
            (TokenKind::Minus, _) => Some(Node::Neg(Box::new(
                self.expression(Op::Multiply.get_priority())?,
            ))),
            (
                TokenKind::Literal {
                    kind: LiteralTokenKind::Bool,
                },
                text,
            ) => Some(Node::Bool(text)),
            (TokenKind::Literal { .. }, text) => Some(Node::Number(text)),
            (TokenKind::Ident(_), name) => {
                let mut primes = 0;
                while self.eat(&TokenKind::Prime).is_some() {
                    primes += 1;
                }
                if self.eat(&TokenKind::OpenParen).is_none() {
                    return (primes == 0).then_some(Node::Ident(name));
                }
                let args = self.items()?;
                self.eat(&TokenKind::CloseParen)?;
                Some(Node::Call { name, primes, args })
            }
            (TokenKind::OpenParen, _) => {
                let content = self.expression(0)?;
                self.eat(&TokenKind::CloseParen)?;
                Some(Node::Group(Box::new(content)))
            }
            (TokenKind::OpenBracket, _) => self.matrix(),
            _ => None,
        }
    }

    /// The rest of a matrix `[[a, b], [c, d]]` after its first `[`, with rows of the same size.
    fn matrix(&mut self) -> Option<Node<'a>> {
        let mut rows: Vec<Vec<Node<'a>>> = vec![];
        loop {
            self.eat(&TokenKind::OpenBracket)?;
            let mut row = vec![];
            loop {
                row.push(self.expression(0)?);
                if self.eat(&TokenKind::Comma).is_none() {
                    break;
                }
            }
            self.eat(&TokenKind::CloseBracket)?;
            if rows.first().is_some_and(|first| first.len() != row.len()) {
                return None;
            }
            rows.push(row);
            if self.eat(&TokenKind::Comma).is_none() {
                break;
            }
        }
        self.eat(&TokenKind::CloseBracket)?;
        Some(Node::Matrix(rows))
    }
}

/// `node` without its parentheses, for places where Typst drops a layer of parentheses (fractions, exponents).
fn ungrouped<'n, 'a>(node: &'n Node<'a>) -> &'n Node<'a> {
    match node {
        Node::Group(content) => content,
        _ => node,
    }
}

/// Whether `node` prints as a sum or a relation, so it needs parentheses before an operator like `dif x`.
const fn is_sum(node: &Node) -> bool {
    matches!(
        node,
        Node::Binary(Op::Add | Op::Subtract, ..) | Node::Relation(..)
    )
}

/// Print `node`, in parentheses if it is a sum.
fn print_grouped_sum(node: &Node, res: &mut String) {
    if is_sum(node) {
        res.push('(');
        print(node, res);
        res.push(')');
    } else {
        print(node, res);
    }
}

/// Print `node` as an operand of `+`, `-` or a product: a negation in parentheses, since `x + -y` would read
/// `x + (-y)` but `x -y` a difference.
fn print_operand(node: &Node, res: &mut String) {
    if matches!(node, Node::Neg(_)) {
        res.push('(');
        print(node, res);
        res.push(')');
    } else {
        print(node, res);
    }
}

/// Print `node` as Typst math source.
fn print(node: &Node, res: &mut String) {
    match node {
        Node::Number(text) => print_number(text, res),
        Node::Bool(text) => {
            let _ = write!(res, "\"{text}\"");
        }
        Node::Ident(name) => print_ident(name, res),
        Node::Group(content) => {
            res.push('(');
            print(content, res);
            res.push(')');
        }
        Node::Neg(operand) => {
            res.push('-');
            print_operand(operand, res);
        }
        Node::Binary(op, left, right) => print_binary(*op, left, right, res),
        Node::Factorial(operand) => {
            if matches!(
                **operand,
                Node::Number(_)
                    | Node::Ident(_)
                    | Node::Group(_)
                    | Node::Call { .. }
                    | Node::Factorial(_)
            ) {
                print(operand, res);
            } else {
                res.push('(');
                print(operand, res);
                res.push(')');
            }
            res.push('!');
        }
        Node::Call { name, primes, args } => print_call(name, *primes, args, res),
        Node::Matrix(rows) => {
            res.push_str("mat(");
            for (i, row) in rows.iter().enumerate() {
                if i != 0 {
                    res.push_str("; ");
                }
                print_list(row, res);
            }
            res.push(')');
        }
        Node::Relation(relation, lhs, rhs) => {
            print(lhs, res);
            let _ = write!(res, " {} ", relation.operator());
            print(rhs, res);
        }
    }
}

/// Print a number literal, `1.5e-20` as `{$1.5 times 10^(-20)$}`.
fn print_number(text: &str, res: &mut String) {
    match text.split_once(['e', 'E']) {
        Some((mantissa, exponent)) => {
            let exponent = exponent.strip_prefix('+').unwrap_or(exponent);
            let _ = write!(res, "{mantissa} times 10^({exponent})");
        }
        None => res.push_str(text),
    }
}

/// Print an identifier like the symbol it stands for.
fn print_ident(name: &str, res: &mut String) {
    match Symbol::new(name) {
        Context::UNDEFINED => res.push_str("\"undefined\""),
        Context::EULER_GAMMA => res.push_str("gamma"),
        _ => res.push_str(&typst_name(name)),
    }
}

fn print_binary(op: Op, left: &Node, right: &Node, res: &mut String) {
    match op {
        Op::Add | Op::Subtract => {
            print(left, res);
            res.push_str(if op == Op::Add { " + " } else { " - " });
            print_operand(right, res);
        }
        Op::Multiply => {
            print(left, res);
            let mut right_text = String::new();
            print_operand(right, &mut right_text);
            // Juxtaposed numbers would read as one
            res.push_str(if right_text.starts_with(|c: char| c.is_ascii_digit()) {
                " dot "
            } else {
                " "
            });
            res.push_str(&right_text);
        }
        Op::Divide => {
            res.push_str("frac(");
            print(ungrouped(left), res);
            res.push_str(", ");
            print(ungrouped(right), res);
            res.push(')');
        }
        Op::Pow => {
            // `-x^2` is `-(x^2)`, so a negative base is in parentheses
            print_operand(left, res);
            res.push_str("^(");
            print(ungrouped(right), res);
            res.push(')');
        }
    }
}

/// Print comma-separated nodes.
fn print_list(nodes: &[Node], res: &mut String) {
    for (i, node) in nodes.iter().enumerate() {
        if i != 0 {
            res.push_str(", ");
        }
        print(node, res);
    }
}

/// Print a call, with the layout of the result printer (`Fun::print`) for builtins like `integrate`, `sum` or `lim`.
fn print_call(name: &str, primes: usize, args: &[Node], res: &mut String) {
    let ident = Symbol::new(name);
    if primes == 0 && print_builtin_call(ident, args, res) {
        return;
    }
    let mut args: Vec<&Node> = args.iter().collect();
    if ident == Context::ROOT {
        // Typst takes the index first: `root(n, x)`
        args.reverse();
    }
    res.push_str(&typst_function_name(ident, name));
    res.push_str(&"'".repeat(primes));
    res.push('(');
    for (i, arg) in args.iter().enumerate() {
        if i != 0 {
            res.push_str(", ");
        }
        if ident == Context::ASSUME
            && let Node::Binary(Op::Multiply, symbol, word) = arg
            && matches!(**word, Node::Ident("integer"))
        {
            // `assume(n integer)`
            print(symbol, res);
            res.push_str(" in ZZ");
        } else {
            print(arg, res);
        }
    }
    res.push(')');
}

/// Print a call to a builtin with a layout of its own, returning `false` for other calls.
fn print_builtin_call(ident: Symbol, args: &[Node], res: &mut String) -> bool {
    match (ident, args) {
        (Context::INTEGRATE, [fun, x, bounds @ ..]) if matches!(bounds.len(), 0 | 2) => {
            // `{$integral_a^b f dif x$}`
            res.push_str("integral");
            if let [a, b] = bounds {
                res.push_str("_(");
                print(ungrouped(a), res);
                res.push_str(")^(");
                print(ungrouped(b), res);
                res.push(')');
            }
            res.push(' ');
            print_grouped_sum(fun, res);
            res.push_str(" dif ");
            print(x, res);
        }
        (Context::SUM | Context::PRODUCT, [fun, k, a, b]) => {
            // `{$sum_(k = a)^b f$}`
            res.push_str(if ident == Context::SUM {
                "sum_("
            } else {
                "product_("
            });
            print(k, res);
            res.push_str(" = ");
            print(a, res);
            res.push_str(")^(");
            print(ungrouped(b), res);
            res.push_str(") ");
            print_grouped_sum(fun, res);
        }
        (Context::LIM, [fun, x, point, direction @ ..]) => {
            let side = match direction {
                [] => "",
                [Node::Number("1")] => "^+",
                [Node::Neg(one)] if matches!(**one, Node::Number("1")) => "^-",
                _ => return false,
            };
            // `{$lim_(x -> a^+) (f)$}`
            res.push_str("lim_(");
            print(x, res);
            res.push_str(" -> ");
            print(point, res);
            let _ = write!(res, "{side}) (");
            print(ungrouped(fun), res);
            res.push(')');
        }
        (Context::DIFF, [fun, x, order @ ..]) if order.len() <= 1 => {
            // `{$(dif^n)/(dif x^n) f$}`
            if let [n] = order {
                let mut n_text = String::new();
                print(ungrouped(n), &mut n_text);
                let _ = write!(res, "frac(dif^({n_text}), dif ");
                print_operand(x, res);
                let _ = write!(res, "^({n_text})) ");
            } else {
                res.push_str("frac(dif, dif ");
                print(x, res);
                res.push_str(") ");
            }
            print_grouped_sum(fun, res);
        }
        (Context::PIECEWISE, [_, ..]) => {
            // `{$cases(v_1 & "if" c_1, ..., d & "otherwise")$}`
            res.push_str("cases(");
            for (i, pair) in args.chunks(2).enumerate() {
                if i != 0 {
                    res.push_str(", ");
                }
                print(&pair[pair.len() - 1], res);
                if let [condition, _] = pair {
                    res.push_str(" & \"if \" ");
                    print(condition, res);
                } else {
                    res.push_str(" & \"otherwise\"");
                }
            }
            res.push(')');
        }
        (Context::POLYGAMMA, [m, u]) => {
            // `{$psi(u)$}`, or `{$psi^((m))(u)$}`
            res.push_str("psi");
            if !matches!(m, Node::Number("0")) {
                res.push_str("^((");
                print(ungrouped(m), res);
                res.push_str("))");
            }
            res.push('(');
            print(u, res);
            res.push(')');
        }
        (Context::BERNOULLI | Context::EULER, [n]) => {
            // `{$B_n$}`, `{$E_n$}`
            res.push_str(if ident == Context::BERNOULLI {
                "B_("
            } else {
                "E_("
            });
            print(ungrouped(n), res);
            res.push(')');
        }
        (Context::LAMBERTW, [u, Node::Neg(one)]) if matches!(**one, Node::Number("1")) => {
            // `{$W_(-1)(u)$}`
            res.push_str("W_(-1)(");
            print(u, res);
            res.push(')');
        }
        _ => return false,
    }
    true
}
