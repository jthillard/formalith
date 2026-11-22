use formalith_session::{
    Output, Session,
    formalith::printer::PrintOptions,
    graph::{Comparison, Graph, GraphKind, ImplicitRelation},
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
    // The order of `t` and `a` depends on when they were created, and tests run in parallel
    let body = draw(&mut Session::new(), "t^3 - a*t").0;
    assert_eq!(text, format!("f(t) := {body}"));
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
    let GraphKind::Implicit { relations } = graph.kind else {
        panic!("not implicit");
    };
    let [ImplicitRelation { expr, relation }] = relations.as_slice() else {
        panic!("not a single relation");
    };
    assert_eq!(*relation, Comparison::Equal);
    assert_close(expr.eval(&[3., 4., 5.]), 0.);

    let (_, graph) = draw(&mut session, "y < sin(x)");
    let GraphKind::Implicit { relations } = graph.unwrap().kind else {
        panic!("not implicit");
    };
    let [relation] = relations.as_slice() else {
        panic!("not a single relation");
    };
    assert_eq!(relation.relation, Comparison::Less);
    assert!(relation.holds(&[1., 0.]));
    assert!(!relation.holds(&[1., 1.]));

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

/// The relations of the region drawn for `line`, with its text.
fn region(session: &mut Session, line: &str) -> (String, Vec<ImplicitRelation>) {
    let (text, graph) = draw(session, line);
    let Some(GraphKind::Implicit { relations }) = graph.map(|graph| graph.kind) else {
        panic!("{line} is not a region");
    };
    (text, relations)
}

#[test]
fn test_regions() {
    let mut session = Session::new();
    let inside = |relations: &[ImplicitRelation], x: f64, y: f64| {
        relations.iter().all(|relation| relation.holds(&[x, y]))
    };
    // Solved when possible, drawn as the intersection
    let (text, relations) = region(&mut session, "x > 0, y > 0");
    assert_eq!(text, "x ∈ (0, oo), y ∈ (0, oo)");
    assert_eq!(relations.len(), 2);
    assert!(inside(&relations, 1., 1.));
    assert!(!inside(&relations, 1., -1.));
    assert!(!inside(&relations, -1., 1.));
    let (text, relations) = region(&mut session, "x^2 + y^2 < 4, y > 0");
    assert_eq!(text, "x ∈ (-2, 2), y ∈ (0, (-(x^2)+4)^(1/2))");
    assert!(inside(&relations, 0., 1.));
    assert!(!inside(&relations, 0., -1.));
    let (text, relations) = region(&mut session, "x > 1, x < 3");
    assert_eq!(text, "x ∈ (1, 3)");
    assert_eq!(relations.len(), 2);
    // Kept as they are when they can't be solved
    let (text, relations) = region(&mut session, "y > sin(x), y < 1");
    assert_eq!(text, "y > sin(x), y < 1");
    assert!(inside(&relations, 0., 0.5));
    assert!(!inside(&relations, 0., -0.5));
    // `!=` doesn't change the drawn region
    let (_, relations) = region(&mut session, "x^2 + y^2 <= 1, x != 0");
    assert_eq!(relations.len(), 1);
    assert_eq!(draw(&mut session, "x != 0, y != 0").1, None);
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
fn test_integrals() {
    let mut session = Session::new();
    let (text, graph) = draw(&mut session, "integrate(exp(x), x, 0, 1)");
    assert_eq!(text, "exp(1)-1");
    let GraphKind::Integral {
        expr,
        derivative,
        a,
        b,
    } = graph.unwrap().kind
    else {
        panic!("not an integral");
    };
    assert_close(expr.eval(&[1., f64::NAN]), 1f64.exp());
    assert_close(derivative.unwrap().eval(&[1., f64::NAN]), 1f64.exp());
    assert_close(a.eval(&[f64::NAN, f64::NAN]), 0.);
    assert_close(b.eval(&[f64::NAN, f64::NAN]), 1.);
    // In another variable, with parameters in the bounds
    let (_, graph) = draw(&mut session, "integrate(t^2, t, -oo, c)");
    let graph = graph.unwrap();
    assert_eq!(graph.params, ["c"]);
    let GraphKind::Integral { expr, a, b, .. } = graph.kind else {
        panic!("not an integral");
    };
    assert_close(expr.eval(&[3., f64::NAN, 2.]), 9.);
    assert_eq!(a.eval(&[f64::NAN, f64::NAN, 2.]), f64::NEG_INFINITY);
    assert_close(b.eval(&[f64::NAN, f64::NAN, 2.]), 2.);
    // Bounds depending on the variable give functions, integrands in two variables nothing
    assert!(matches!(
        draw(&mut session, "integrate(t, t, 0, x)").1.unwrap().kind,
        GraphKind::Function { .. }
    ));
    assert_eq!(draw(&mut session, "integrate(x*y, x, 0, 1)").1, None);
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
