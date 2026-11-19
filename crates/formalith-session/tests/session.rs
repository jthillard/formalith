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
    assert_eq!(run(&mut session, "assume(a > 0)").1, true);
    assert_eq!(run(&mut session, "f(3)"), ("9".to_owned(), false));
    assert_eq!(run(&mut session, ":defs").0, "f(x) := x^2\nassume(a > 0)");
    assert_eq!(run(&mut session, ":clear f"), (String::new(), true));
    assert!(matches!(session.run(":clear f").output, Output::Error(_)));
    assert_eq!(run(&mut session, ":clear").1, true);
    assert_eq!(run(&mut session, ":defs").0, "no definitions");
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
