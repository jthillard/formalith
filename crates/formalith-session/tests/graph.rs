use formalith_session::{
    Output, Session,
    formalith::printer::PrintOptions,
    graph::{Comparison, Graph, GraphKind},
};

/// The text and graph of `line` in `session`.
fn draw(session: &mut Session, line: &str) -> (String, Option<Graph>) {
    let (response, graph) = session.graph(line);
    (response.output.print(PrintOptions::plain()), graph)
}

fn assert_close(a: f64, b: f64) {
    assert!((a - b).abs() < 1e-9, "{a} != {b}");
}

#[test]
fn test_function() {
    let mut session = Session::new();
    for line in ["sin(x)", "y = sin(x)", "sin(x) = y"] {
        let (_, graph) = draw(&mut session, line);
        let Some(Graph {
            kind: GraphKind::Function { expr, derivative },
            params,
        }) = graph
        else {
            panic!("{line} is not a function");
        };
        assert!(params.is_empty());
        assert_close(expr.eval(&[1., f64::NAN]), 1f64.sin());
        assert_close(derivative.unwrap().eval(&[1., f64::NAN]), 1f64.cos());
    }
    // Constants aren't drawn, `y = 2` is
    assert_eq!(draw(&mut session, "2 + 3"), ("5".to_owned(), None));
    assert!(matches!(
        draw(&mut session, "y = 2").1.unwrap().kind,
        GraphKind::Function { .. }
    ));
}

#[test]
fn test_definitions() {
    let mut session = Session::new();
    let (text, graph) = draw(&mut session, "f(t) := t^3 - a*t");
    assert_eq!(text, "f(t) := t^3-t*a");
    let graph = graph.unwrap();
    assert_eq!(graph.params, ["a"]);
    let GraphKind::Function { expr, .. } = &graph.kind else {
        panic!("not a function");
    };
    assert_close(expr.eval(&[2., f64::NAN, 1.]), 6.);
    // Definitions are used by the next lines
    let (_, graph) = draw(&mut session, "f(x - 1)");
    let GraphKind::Function { expr, .. } = graph.unwrap().kind else {
        panic!("not a function");
    };
    assert_close(expr.eval(&[3., f64::NAN, 1.]), 6.);
    assert!(session.graph("b := 2").0.replay);
    assert_eq!(draw(&mut session, "b").1, None);
}

#[test]
fn test_relations() {
    let mut session = Session::new();
    let (text, graph) = draw(&mut session, "x = y^2");
    assert_eq!(text, "x = y^2");
    let GraphKind::InverseFunction { expr } = graph.unwrap().kind else {
        panic!("not an inverse function");
    };
    assert_close(expr.eval(&[f64::NAN, 3.]), 9.);

    let (text, graph) = draw(&mut session, "x^2+y^2 = r^2");
    assert_eq!(text, "x^2+y^2 = r^2");
    let graph = graph.unwrap();
    assert_eq!(graph.params, ["r"]);
    let GraphKind::Implicit { expr, relation } = graph.kind else {
        panic!("not implicit");
    };
    assert_eq!(relation, Comparison::Equal);
    assert_close(expr.eval(&[3., 4., 5.]), 0.);

    let (_, graph) = draw(&mut session, "y < sin(x)");
    let GraphKind::Implicit { expr, relation } = graph.unwrap().kind else {
        panic!("not implicit");
    };
    assert_eq!(relation, Comparison::Less);
    assert!(relation.holds(expr.eval(&[1., 0.])));
    assert!(!relation.holds(expr.eval(&[1., 1.])));

    // Relations without `y` are solved, and drawn as vertical lines or bands
    let (text, graph) = draw(&mut session, "x^2 = 4");
    assert!(text.contains('2'), "{text}");
    assert!(matches!(graph.unwrap().kind, GraphKind::Implicit { .. }));
    let (text, graph) = draw(&mut session, "x > 1");
    assert_eq!(text, "x ∈ (1, oo)");
    assert!(matches!(graph.unwrap().kind, GraphKind::Implicit { .. }));
    // Systems are only solved
    assert_eq!(draw(&mut session, "x + y = 3, x - y = 1").1, None);
}

#[test]
fn test_points() {
    let mut session = Session::new();
    session.graph("f(x) := x^2");
    for line in ["point(2, f(2))", "(2, f(a))"] {
        let (text, graph) = draw(&mut session, line);
        let GraphKind::Point { x, y } = graph.unwrap().kind else {
            panic!("{line} is not a point");
        };
        assert!(text.starts_with("(2, "), "{text}");
        assert_close(x.eval(&[f64::NAN, f64::NAN, 2.]), 2.);
        assert_close(y.eval(&[f64::NAN, f64::NAN, 2.]), 4.);
    }
}

#[test]
fn test_errors() {
    let mut session = Session::new();
    assert!(matches!(session.graph("1 +").0.output, Output::Error(_)));
    assert!(matches!(session.graph("y = ").0.output, Output::Error(_)));
    let (_, graph) = draw(&mut session, "integrate(exp(x^3), x)");
    assert_eq!(graph.unwrap().unsupported(), Some("integrate"));
    // Graphs only exist in R
    session.run(":set Z/7");
    assert_eq!(draw(&mut session, "x + 8"), ("x+1".to_owned(), None));
}
