//! Messages between the interface and the worker evaluating the lines, natively in a thread and in a Web Worker
//! in the browser, where a panic aborts the whole wasm instance.
//!
//! Each [`Request`] carries every line, evaluated in order in a fresh session, so definitions are always made
//! before the lines using them. The worker answers with a [`Reply::Line`] per line, as soon as it is evaluated,
//! then [`Reply::Done`]: after a crash, the first line without an answer is the one which crashed.

use formalith_session::{Output, Session, formalith::printer::PrintOptions, graph::Graph};
use serde::{Deserialize, Serialize};

/// A line to evaluate, with an identifier to match its result.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct RequestLine {
    /// The identifier of the line in the interface.
    pub id: u64,
    /// The input.
    pub text: String,
}

/// A request to evaluate lines.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Request {
    /// Increases with each request, to drop the answers to outdated ones.
    pub generation: u64,
    /// The set lines are evaluated in, like `R` or `Z/7`.
    pub set: String,
    /// The lines, in order.
    pub lines: Vec<RequestLine>,
    /// Inputs which crashed the worker, not evaluated again.
    pub skip: Vec<String>,
    /// Whether to record a profile of the evaluation, sent back in a [`Reply::Profile`] by a worker in the
    /// browser (feature `profile`). Natively, the worker thread is recorded with the interface.
    #[serde(default)]
    pub profile: bool,
}

/// The kind of result of a line.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum ResultKind {
    /// Nothing to show, like for an empty line.
    None,
    /// An evaluated statement.
    Result,
    /// Information, like a help text.
    Message,
    /// An error.
    Error,
}

/// The result of a line.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct LineResult {
    /// The kind of result.
    pub kind: ResultKind,
    /// The text to show, possibly on several lines.
    pub text: String,
    /// What to draw.
    pub graph: Option<Graph>,
}

impl LineResult {
    /// An error with `message`.
    #[must_use]
    pub fn error(message: impl Into<String>) -> Self {
        Self {
            kind: ResultKind::Error,
            text: message.into(),
            graph: None,
        }
    }
}

/// An answer of the worker.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub enum Reply {
    /// The result of a line.
    Line {
        /// The generation of the request.
        generation: u64,
        /// The identifier of the line.
        id: u64,
        /// Its result.
        result: LineResult,
    },
    /// The profile of the evaluation, recorded by a worker in the browser when the request asked for it, just
    /// before [`Reply::Done`].
    #[cfg(feature = "profile")]
    Profile {
        /// The lanes recorded.
        lanes: Vec<crate::profiler::Lane>,
    },
    /// Every line of the request was evaluated.
    Done {
        /// The generation of the request.
        generation: u64,
    },
}

/// The error shown for a line which crashed the worker.
pub const CRASHED: &str = "this operation is not supported (the evaluation crashed)";

/// The options of the printed results: 2D layout, without colors.
const PRINT_OPTIONS: PrintOptions = PrintOptions {
    colors: false,
    typst: false,
    pretty_print: true,
};

/// A line evaluated by an earlier request.
struct Cached {
    text: String,
    result: LineResult,
    /// Whether the line changed the state of its session, so it must run again to evaluate the next lines.
    replay: bool,
}

/// The state of a worker: the results of the last request, reused for the lines of the next one which follow
/// the same lines.
#[derive(Default)]
pub struct Worker {
    set: String,
    cache: Vec<Cached>,
}

impl Worker {
    /// A worker without results.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Evaluate `request`, giving each reply to `emit` as soon as it is known. Stops early when `emit` returns
    /// `false`, if the interface doesn't wait for the replies anymore.
    pub fn evaluate(&mut self, request: &Request, mut emit: impl FnMut(Reply) -> bool) {
        #[cfg(all(feature = "profile", target_arch = "wasm32"))]
        if request.profile {
            crate::profiler::start();
        }
        if !self.evaluate_lines(request, &mut emit) {
            return;
        }
        #[cfg(all(feature = "profile", target_arch = "wasm32"))]
        if request.profile {
            // The worker's only thread, which another instance calls `main` too
            let mut lanes = crate::profiler::stop(true);
            for lane in &mut lanes {
                lane.name = "worker".to_owned();
            }
            if !emit(Reply::Profile { lanes }) {
                return;
            }
        }
        emit(Reply::Done {
            generation: request.generation,
        });
    }

    /// Evaluate the lines of `request`, returning `false` if [`Self::evaluate`] must stop.
    fn evaluate_lines(&mut self, request: &Request, emit: &mut impl FnMut(Reply) -> bool) -> bool {
        profile_scope!("evaluate request");
        let mut session = Session::new();
        let set_result = session.run(&format!(":set {}", request.set));
        if let Output::Error(error) = set_result.output {
            for line in &request.lines {
                if !emit(Reply::Line {
                    generation: request.generation,
                    id: line.id,
                    result: LineResult::error(error.clone()),
                }) {
                    return false;
                }
            }
            return true;
        }
        if self.set != request.set {
            self.cache.clear();
            self.set.clone_from(&request.set);
        }
        // Lines after the first one which changed can't reuse their results
        let same = self
            .cache
            .iter()
            .zip(&request.lines)
            .take_while(|(cached, line)| {
                cached.text == line.text && !request.skip.contains(&line.text)
            })
            .count();
        self.cache.truncate(same);
        for (index, line) in request.lines.iter().enumerate() {
            let result = if index < same {
                let cached = &self.cache[index];
                if cached.replay {
                    session.graph(&line.text);
                }
                cached.result.clone()
            } else {
                let (result, replay) = evaluate_line(&mut session, &line.text, &request.skip);
                self.cache.push(Cached {
                    text: line.text.clone(),
                    result: result.clone(),
                    replay,
                });
                result
            };
            if !emit(Reply::Line {
                generation: request.generation,
                id: line.id,
                result,
            }) {
                return false;
            }
        }
        true
    }
}

/// Evaluate a line in `session`, with whether it changed the state of the session.
fn evaluate_line(session: &mut Session, text: &str, skip: &[String]) -> (LineResult, bool) {
    profile_scope!("line", text);
    if skip.iter().any(|skipped| skipped == text) {
        return (LineResult::error(CRASHED), false);
    }
    let (response, graph) = session.graph(text);
    let kind = match &response.output {
        Output::None => ResultKind::None,
        Output::Result { .. } => ResultKind::Result,
        Output::Message(_) => ResultKind::Message,
        Output::Error(_) => ResultKind::Error,
    };
    let result = LineResult {
        kind,
        text: response.output.print(PRINT_OPTIONS),
        graph,
    };
    (result, response.replay)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn request(generation: u64, lines: &[&str]) -> Request {
        Request {
            generation,
            set: "R".to_owned(),
            lines: lines
                .iter()
                .zip(0..)
                .map(|(text, id)| RequestLine {
                    id,
                    text: (*text).to_owned(),
                })
                .collect(),
            skip: vec![],
            profile: false,
        }
    }

    fn run(worker: &mut Worker, request: &Request) -> Vec<Reply> {
        let mut replies = vec![];
        worker.evaluate(request, |reply| {
            replies.push(reply);
            true
        });
        replies
    }

    #[test]
    fn test_evaluate() {
        let mut worker = Worker::new();
        let replies = run(
            &mut worker,
            &request(1, &["f(x) := x^2", "f(3)", "y = f(x)", "1 +"]),
        );
        assert_eq!(replies.len(), 5);
        let Reply::Line { result, .. } = &replies[1] else {
            panic!("not a line");
        };
        assert_eq!(result.text, "9");
        let Reply::Line { result, .. } = &replies[2] else {
            panic!("not a line");
        };
        assert!(result.graph.is_some());
        let Reply::Line { result, .. } = &replies[3] else {
            panic!("not a line");
        };
        assert_eq!(result.kind, ResultKind::Error);
        assert_eq!(replies[4], Reply::Done { generation: 1 });

        // Cached lines replay definitions, so a changed later line sees them
        let replies = run(&mut worker, &request(2, &["f(x) := x^2", "f(4)"]));
        let Reply::Line { result, .. } = &replies[1] else {
            panic!("not a line");
        };
        assert_eq!(result.text, "16");

        // Skipped lines aren't evaluated
        let mut skipped = request(3, &["f(x) := x^2", "f(5)"]);
        skipped.skip.push("f(5)".to_owned());
        let replies = run(&mut worker, &skipped);
        let Reply::Line { result, .. } = &replies[1] else {
            panic!("not a line");
        };
        assert_eq!(result.text, CRASHED);
    }

    #[test]
    fn test_serialize() {
        let mut worker = Worker::new();
        for reply in run(&mut worker, &request(1, &["y = a*sin(x)", "x^2 + y^2 < 1"])) {
            let json = serde_json::to_string(&reply).unwrap();
            assert_eq!(serde_json::from_str::<Reply>(&json).unwrap(), reply);
        }
    }
}
