//! Commands and evaluation of a session.
use formalith_session::{Output, Session, SetChoice, formalith::printer::PrintOptions};

/// The output of `line` on one line (or as Typst), and whether it is replayed.
fn run(session: &mut Session, line: &str) -> (String, bool) {
    let response = session.run(line);
    let options = if session.typst() {
        PrintOptions::typst()
    } else {
        PrintOptions::plain()
    };
    (response.output.print(options), response.replay)
}

#[test]
fn commands() {
    let mut session = Session::new();
    assert_eq!(run(&mut session, ":set Z/7"), (String::new(), true));
    assert_eq!(session.set(), SetChoice::Zn(7));
    assert_eq!(run(&mut session, "3*5"), ("1".to_owned(), false));
    assert!(matches!(session.run(":set Q").output, Output::Error(_)));
    assert_eq!(session.set(), SetChoice::Zn(7));
    assert!(run(&mut session, ":set").0.starts_with("current set: Z/7"));

    assert_eq!(
        run(&mut session, ":typst"),
        ("typst output enabled".to_owned(), true)
    );
    assert_eq!(run(&mut session, ":set R").0, "");
    assert_eq!(run(&mut session, "x/2").0, "frac(1, 2) x");
    assert_eq!(run(&mut session, "abc := 2").0, "\"abc\" := 2");
    assert_eq!(
        run(&mut session, "fun(xy) := xy").0,
        "op(\"fun\")(\"xy\") := \"xy\""
    );
    assert_eq!(run(&mut session, "rho > 1").0, "rho in (1, +oo)");
    assert_eq!(run(&mut session, "ab > 1").0, "\"ab\" in (1, +oo)");
    assert_eq!(run(&mut session, ":typst").0, "typst output disabled");

    assert!(matches!(session.run(":unknown").output, Output::Error(_)));
    assert!(matches!(session.run(":settings").output, Output::Error(_)));
    assert!(run(&mut session, "help").0.contains(":clear [name]"));
    assert!(matches!(session.run("").output, Output::None));
}

#[test]
fn definitions() {
    let mut session = Session::new();
    assert_eq!(run(&mut session, ":defs").0, "no definitions");
    assert_eq!(
        run(&mut session, "f(x) := x^2"),
        ("f(x) := x^2".to_owned(), true)
    );
    assert!(run(&mut session, "assume(a > 0)").1);
    assert_eq!(run(&mut session, "f(3)"), ("9".to_owned(), false));
    assert_eq!(run(&mut session, ":defs").0, "f(x) := x^2\nassume(a > 0)");
    assert_eq!(run(&mut session, ":clear f"), (String::new(), true));
    assert!(matches!(session.run(":clear f").output, Output::Error(_)));
    assert!(run(&mut session, ":clear").1);
    assert_eq!(run(&mut session, ":defs").0, "no definitions");
}

#[test]
fn default_assumptions() {
    let mut session = Session::new();
    assert_eq!(run(&mut session, "sin(n*pi)").0, "0");
    assert_eq!(run(&mut session, "floor(k + m)").0, "k+m");
    assert_eq!(
        run(&mut session, ":assumptions"),
        (
            "k integer (default)\nm integer (default)\nn integer (default)".to_owned(),
            false
        )
    );
    assert_eq!(run(&mut session, ":defs").0, "no definitions");

    run(&mut session, "assume(a > 0, n > 0)");
    assert_eq!(
        run(&mut session, ":assumptions").0,
        "a > 0\nk integer (default)\nm integer (default)\nn >= 1, n integer"
    );
    assert_eq!(
        run(&mut session, ":defs").0,
        "assume(a > 0, n >= 1, n integer)"
    );

    assert_eq!(run(&mut session, ":clear n"), (String::new(), true));
    assert_ne!(run(&mut session, "sin(n*pi)").0, "0");
    assert_eq!(
        run(&mut session, ":assumptions").0,
        "a > 0\nk integer (default)\nm integer (default)"
    );

    run(&mut session, ":clear");
    assert_eq!(run(&mut session, "sin(n*pi)").0, "0");
    run(&mut session, ":clear k");
    run(&mut session, ":clear m");
    run(&mut session, ":clear n");
    assert_eq!(run(&mut session, ":assumptions").0, "no assumptions");
}

#[test]
fn replay() {
    let mut session = Session::new();
    let lines = ["a := 2", ":set Z/5", "b := a + 4", "1/0", "b*3"];
    let replayed: Vec<_> = lines
        .into_iter()
        .filter(|line| session.run(line).replay)
        .collect();
    assert_eq!(replayed, ["a := 2", ":set Z/5", "b := a + 4"]);
    let mut restored = Session::new();
    replayed.into_iter().for_each(|line| {
        restored.run(line);
    });
    assert_eq!(restored.set(), SetChoice::Zn(5));
    assert_eq!(run(&mut restored, "b*3").0, run(&mut session, "b*3").0);
}

#[test]
fn builtins_help() {
    let mut session = Session::new();
    let list = run(&mut session, "help builtins").0;
    assert!(list.contains("Calculus:"));
    assert!(list.contains("integrate"));
    let help = run(&mut session, "help integrate").0;
    assert!(help.starts_with("integrate(f, x, [a, b])"));
    assert!(help.contains("integrate(x^2, x) → x^3/3"));
    assert!(run(&mut session, ":help gcd").0.contains("(in Z)"));
    assert!(matches!(session.run("help nope").output, Output::Error(_)));
}

/// A tiny deterministic generator for the random sessions.
struct Lcg(u64);

impl Lcg {
    fn below(&mut self, n: usize) -> usize {
        self.0 = self
            .0
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1);
        ((self.0 >> 33) % n as u64) as usize
    }
}

/// Lines changing or using the state of a session.
const LINES: [&str; 22] = [
    "a := 3",
    "a := 5",
    "b := a + 1",
    "f(x) := x^2 + a",
    "g(x, y) := f(x) - y",
    "assume(c > 0)",
    "assume(c < 0)",
    "assume(n integer)",
    ":set R",
    ":set Z/7",
    ":set C",
    ":set Z",
    ":clear a",
    ":clear f",
    ":clear",
    ":typst",
    "f(2)",
    "g(1, b)",
    "abs(c)",
    "sqrt(c^2)",
    "1/0",
    "x +",
];

/// Probes of the state: the set, the definitions and values using them.
const PROBES: [&str; 7] = [":set", ":defs", "a", "b", "f(4)", "g(2, 3)", "sqrt(c^2)"];

#[test]
fn replayed_lines_restore_random_sessions() {
    for seed in 0..60 {
        let mut rng = Lcg(seed);
        let mut session = Session::new();
        let mut replayed = vec![];
        let mut history = vec![];
        for _ in 0..12 {
            let line = LINES[rng.below(LINES.len())];
            history.push(line);
            if session.run(line).replay {
                replayed.push(line);
            }
        }
        let mut restored = Session::new();
        for line in &replayed {
            restored.run(line);
        }
        for probe in PROBES {
            assert_eq!(
                run(&mut restored, probe),
                run(&mut session, probe),
                "`{probe}` after {history:?}, replaying {replayed:?}"
            );
        }
    }
}

#[test]
fn errors_and_the_session_goes_on() {
    let mut session = Session::new();
    assert!(run(&mut session, "a := 2").1);
    assert!(run(&mut session, ":set N").1);
    assert_eq!(run(&mut session, "a + 3").0, "5");
    // `N` has no subtraction
    let response = session.run("a - 3");
    assert!(matches!(response.output, Output::Error(_)));
    assert!(!response.replay);
    assert!(run(&mut session, ":set R").1);
    assert_eq!(run(&mut session, "a - 3").0, "-1");
}

#[test]
fn typeset_input() {
    let mut session = Session::new();
    assert_eq!(session.typeset_input("x/2"), None);
    session.set_typst(true);
    assert_eq!(
        session.typeset_input(" x/2 ").as_deref(),
        Some("frac(x, 2)")
    );
    assert_eq!(
        session.typeset_input("f(x) := x^2").as_deref(),
        Some("f(x) := x^(2)")
    );
    for line in ["", ":set Z/7", ":typst", "help", "help sin", "x +"] {
        assert_eq!(session.typeset_input(line), None, "{line}");
    }
}

/// The error message of `line`.
fn error(session: &mut Session, line: &str) -> String {
    match session.run(line).output {
        Output::Error(err) => err,
        output => panic!("{line} isn't an error: {output:?}"),
    }
}

/// Errors underline the part of the line they are about, and give a hint naming a set where the line means
/// something.
#[test]
fn error_reports() {
    let mut session = Session::new();
    assert_eq!(
        error(&mut session, "2 $ 3"),
        "unexpected `$`\n  2 $ 3\n    ^"
    );
    // Columns are counted in characters
    assert_eq!(
        error(&mut session, "α + )"),
        "expected an expression, found `α`\n  α + )\n  ^"
    );
    assert_eq!(
        error(&mut session, "[[1, 2], [3, 4]]"),
        "expected an expression, found `[`\n  [[1, 2], [3, 4]]\n  ^\nhint: matrices are in `M(R)`: `:set M(R)`"
    );
    // In the body of a definition
    assert_eq!(
        error(&mut session, "f(x) := x +"),
        "expected an expression after `+`, found the end of the input\n  f(x) := x +\n            ^"
    );
    // Without a part of the line
    assert!(run(&mut session, "g(x) := x").1);
    assert_eq!(
        error(&mut session, "g(1, 2)"),
        "`g` expects 1 argument, found 2"
    );
    // In the sides of a relation drawn by the GUI
    assert_eq!(
        error(&mut session, "y = x +"),
        "expected an expression after `+`, found the end of the input\n  y = x +\n        ^"
    );
    assert!(run(&mut session, ":set N").1);
    assert_eq!(
        error(&mut session, "1 - 2"),
        "subtraction isn't defined in this set, which has no additive inverses\n  1 - 2\n    ^\nhint: \
         negative numbers are in `Z`: `:set Z`"
    );
}
