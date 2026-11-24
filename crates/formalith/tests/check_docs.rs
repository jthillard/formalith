//! The examples of the documentation of the builtins (`context/docs.rs`) checked against what they compute: every
//! example evaluates without error or panic, and its hand-written result is the computed one, as the same Typst
//! text up to spaces or as a numerically equivalent expression.

use crate::common::{
    guard::no_panic,
    harness::case_rng,
    numeric::{Check, Domain, env_with, equivalent, split_top, symbols},
};
use formalith::{
    context::docs::{BUILTIN_DOCS, Example},
    dynamic::SetChoice,
    parser::environment::Environment,
};

/// Examples whose hand-written result can't be converted to an expression (held sums, lines of integers, complex
/// results), only checked to evaluate.
const UNCONVERTIBLE: [&str; 6] = [
    "series(exp(x), x, 0, oo)",
    "series(sin(x), x, 0, oo)",
    "series(ln(1 + x), x, 0, oo)",
    "localmin(cos(x), x)",
    "apart(1/(x^2 + 1))",
    "arg(-1 - sqrt(3)*i)",
];

/// The result of `example`, printed as Typst.
fn run(example: &Example) -> Result<String, String> {
    let set: SetChoice = example.set.parse().map_err(|e| format!("{e:?}"))?;
    let mut env = Environment::new();
    let mut result = Err("no line".to_owned());
    for line in example.input.lines() {
        result =
            no_panic(|| set.eval(line, true, &mut env)).unwrap_or_else(|| Err("panic".to_owned()));
    }
    result
}

/// The text without whitespace.
fn compact(text: &str) -> String {
    text.chars().filter(|c| !c.is_whitespace()).collect()
}

/// Typst math as an expression to parse, without spaces: `frac(a, b)` as a quotient, juxtaposition as a product,
/// `gamma` alone as Euler's constant, and remainders `o(u)` left out.
fn to_expression(typst: &str) -> String {
    // `frac(a, b)`, innermost last
    let mut text = typst.to_owned();
    while let Some(start) = text.find("frac(") {
        let after = &text[start + 5..];
        let mut depth = 1;
        let Some(end) = after.char_indices().find_map(|(i, c)| {
            match c {
                '(' => depth += 1,
                ')' => depth -= 1,
                _ => {}
            }
            (depth == 0).then_some(i)
        }) else {
            break;
        };
        let parts = split_top(&after[..end], ',');
        let replaced = match parts.as_slice() {
            [a, b] => format!("(({a})/({b}))"),
            _ => break,
        };
        text = format!("{}{replaced}{}", &text[..start], &after[end + 1..]);
    }
    // Juxtaposition: an operand, spaces, an operand
    let chars: Vec<char> = text.chars().collect();
    let mut res = String::new();
    for (i, &c) in chars.iter().enumerate() {
        if c == ' ' {
            let previous = chars[..i].iter().rev().find(|c| **c != ' ');
            let next = chars[i + 1..].iter().find(|c| **c != ' ');
            let ends = |c: &char| c.is_alphanumeric() || matches!(c, ')' | '_' | '!');
            let starts = |c: &char| c.is_alphanumeric() || *c == '(';
            if previous.is_some_and(ends) && next.is_some_and(starts) && !res.ends_with('*') {
                res.push('*');
            }
            continue;
        }
        res.push(c);
    }
    // `gamma` without arguments is Euler's constant in Typst
    let mut out = String::new();
    let mut rest = res.as_str();
    while let Some(i) = rest.find("gamma") {
        let before = rest[..i].chars().last();
        let after = rest[i + 5..].chars().next();
        out.push_str(&rest[..i]);
        let word = !before.is_some_and(|c| c.is_alphanumeric() || c == '_')
            && !after.is_some_and(|c| c.is_alphanumeric() || c == '_' || c == '(');
        out.push_str(if word { "euler_gamma" } else { "gamma" });
        rest = &rest[i + 5..];
    }
    out.push_str(rest);
    // The remainder `{$o(u)$}` of series can't be evaluated, it is left out on both sides
    let mut res = String::new();
    let chars: Vec<char> = out.chars().collect();
    for (i, &c) in chars.iter().enumerate() {
        let word_start = i == 0 || !(chars[i - 1].is_alphanumeric() || chars[i - 1] == '_');
        if c == 'o' && word_start && chars.get(i + 1) == Some(&'(') {
            res.push_str("0*");
        } else {
            res.push(c);
        }
    }
    res
}

/// Whether the hand-written `expected` and the computed `actual` results are equivalent, comparing their sides of
/// `=` and their comma-separated parts.
fn equivalent_results(input: &str, expected: &str, actual: &str) -> Result<(), String> {
    let (expected, actual) = (to_expression(expected), to_expression(actual));
    let (e_parts, a_parts) = (split_top(&expected, ','), split_top(&actual, ','));
    if e_parts.len() != a_parts.len() {
        return Err(format!("`{expected}` and `{actual}` have different parts"));
    }
    let mut rng = case_rng(input);
    for (e, a) in e_parts.iter().zip(&a_parts) {
        let (e, a) = match (e.split_once('='), a.split_once('=')) {
            (Some((el, er)), Some((al, ar))) if compact(el) == compact(al) => {
                (er.trim(), ar.trim())
            }
            (None, None) => (e.as_str(), a.as_str()),
            _ => return Err(format!("`{e}` and `{a}` aren't comparable")),
        };
        let names = symbols(&format!("{e} + {a}"));
        let vars: Vec<(&str, Domain)> = names
            .iter()
            .map(|n| (n.as_str(), Domain::Positive))
            .collect();
        match equivalent(&env_with(&[]), e, a, &vars, &mut rng) {
            Check::Equal => {}
            other => return Err(format!("`{e}` vs `{a}`: {other:?}")),
        }
    }
    Ok(())
}

#[test]
fn documented_examples_are_computed() {
    let mut failures = vec![];
    for doc in &BUILTIN_DOCS {
        for example in doc.examples {
            let actual = match run(example) {
                Ok(actual) => actual,
                Err(e) => {
                    failures.push(format!("[{}] `{}`: {e}", example.set, example.input));
                    continue;
                }
            };
            if compact(&actual) == compact(example.result) || UNCONVERTIBLE.contains(&example.input)
            {
                continue;
            }
            if let Err(e) = equivalent_results(example.input, example.result, &actual) {
                failures.push(format!(
                    "[{}] `{}` documented as `{}`, computed `{actual}`: {e}",
                    example.set, example.input, example.result
                ));
            }
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

#[test]
fn typst_conversion() {
    assert_eq!(to_expression("frac(1, 2) pi"), "((1)/(2))*pi");
    assert_eq!(to_expression("a d - b c"), "a*d-b*c");
    assert_eq!(to_expression("1 + x + o(x)"), "1+x+0*(x)");
    assert_eq!(to_expression("1 - gamma"), "1-euler_gamma");
    assert_eq!(to_expression("gamma(x)"), "gamma(x)");
    // A wrong documented result is caught
    assert!(equivalent_results("t", "pi/3", "frac(1, 4) pi").is_err());
    assert!(equivalent_results("t", "x = pi/4", "x = frac(1, 4) pi").is_ok());
}
