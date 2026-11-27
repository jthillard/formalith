//! Messages between the interface and the worker evaluating the lines, natively in a thread and in a Web Worker
//! in the browser, where a panic aborts the whole wasm instance.
//!
//! Each [`Request`] carries every line, evaluated in order in a fresh session, so definitions are always made
//! before the lines using them. The worker answers with a [`Reply::Line`] per line, as soon as it is evaluated,
//! then [`Reply::Done`]: after a crash, the first line without an answer is the one which crashed.

use std::{
    collections::HashMap,
    hash::{DefaultHasher, Hash, Hasher},
};

use formalith_session::{Output, Session, formalith::printer::PrintOptions, graph::Graph};
use serde::{Deserialize, Serialize};

/// The name of the thread evaluating requests natively, also given to the lane of a Web Worker's profile.
pub const WORKER_THREAD: &str = "formalith-worker";

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
    /// browser (feature `profile`). Natively, the worker thread is recorded with the interface. Lines are then all
    /// evaluated again, without reusing the results of the last request.
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
    /// The result printed as Typst math, for results, typeset by the interface.
    #[serde(default)]
    pub typst: Option<String>,
    /// The result printed in Formalith syntax, so that it parses back, copied when clicked.
    #[serde(default)]
    pub plain: Option<String>,
}

impl LineResult {
    /// An error with `message`.
    #[must_use]
    pub fn error(message: impl Into<String>) -> Self {
        Self {
            kind: ResultKind::Error,
            text: message.into(),
            graph: None,
            typst: None,
            plain: None,
        }
    }
}

/// An answer of the worker.
// Replies are sent once per line, boxing wouldn't save anything
#[allow(clippy::large_enum_variant)]
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub enum Reply {
    /// The result of a line.
    Line {
        /// The generation of the request.
        generation: u64,
        /// The identifier of the line.
        id: u64,
        /// The key of the line, see [`line_key`]: the interface compares it with the key of the line's current text
        /// to tell whether the result is up to date.
        key: u64,
        /// Whether the line changed the state of its session, so the lines after it depend on it.
        replay: bool,
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

/// The state of a session evaluating lines in `set`, before any line, see [`line_key`].
#[must_use]
pub fn initial_state(set: &str) -> u64 {
    let mut hasher = DefaultHasher::new();
    set.hash(&mut hasher);
    hasher.finish()
}

/// The key of a line with input `text` evaluated in the session state `state`: a line's result only depends on its
/// text and on the state of the session, which only lines with `replay` change. The state after a line is its key
/// if it changed the state, `state` otherwise; it starts at [`initial_state`].
#[must_use]
pub fn line_key(state: u64, text: &str) -> u64 {
    let mut hasher = DefaultHasher::new();
    (state, text).hash(&mut hasher);
    hasher.finish()
}

/// The options of the printed results: 2D layout, without colors.
const PRINT_OPTIONS: PrintOptions = PrintOptions {
    colors: false,
    typst: false,
    pretty_print: true,
    width: None,
};

/// A line evaluated by an earlier request.
struct Cached {
    result: LineResult,
    /// Whether the line changed the state of its session, so it must run again to evaluate the next lines.
    replay: bool,
}

/// The state of a worker: the results of the last request, reused for the lines of the next one evaluated in
/// the same state, by their text and a key of the state-changing lines before them.
#[derive(Default)]
pub struct Worker {
    set: String,
    /// The results by key, see [`line_key`].
    cache: HashMap<u64, Cached>,
    /// The number of lines evaluated, not reused.
    #[cfg(test)]
    evaluations: usize,
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
                WORKER_THREAD.clone_into(&mut lane.name);
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
        let mut state = initial_state(&request.set);
        if let Output::Error(error) = set_result.output {
            for line in &request.lines {
                if !emit(Reply::Line {
                    generation: request.generation,
                    id: line.id,
                    key: line_key(state, &line.text),
                    replay: false,
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
        // `state` identifies the sequence of the state-changing lines before the current line, see `line_key`. No
        // result is reused when profiling.
        let mut previous = std::mem::take(&mut self.cache);
        if request.profile {
            previous.clear();
        }
        for line in &request.lines {
            let key = line_key(state, &line.text);
            let reused = if request.skip.contains(&line.text) {
                None
            } else if let Some(cached) = self.cache.get(&key) {
                Some(cached)
            } else if let Some(cached) = previous.remove(&key) {
                Some(&*self.cache.entry(key).or_insert(cached))
            } else {
                None
            };
            let (result, replay) = if let Some(cached) = reused {
                if cached.replay {
                    session.graph(&line.text);
                }
                (cached.result.clone(), cached.replay)
            } else {
                #[cfg(test)]
                {
                    self.evaluations += 1;
                }
                let (result, replay) = evaluate_line(&mut session, &line.text, &request.skip);
                self.cache.insert(
                    key,
                    Cached {
                        result: result.clone(),
                        replay,
                    },
                );
                (result, replay)
            };
            if replay {
                state = key;
            }
            if !emit(Reply::Line {
                generation: request.generation,
                id: line.id,
                key,
                replay,
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
    let is_result = kind == ResultKind::Result;
    let typst = is_result.then(|| response.output.print(PrintOptions::typst()));
    let plain = is_result.then(|| response.output.print(PrintOptions::plain()));
    let result = LineResult {
        kind,
        text: response.output.print(PRINT_OPTIONS),
        graph,
        typst,
        plain,
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
        // Copied in Formalith syntax rather than pretty printed
        let Reply::Line { result, .. } = &replies[0] else {
            panic!("not a line");
        };
        assert_eq!(result.plain.as_deref(), Some("f(x) := x^2"));
        let Reply::Line { result, .. } = &replies[1] else {
            panic!("not a line");
        };
        assert_eq!(result.text, "9");
        assert_eq!(result.typst.as_deref(), Some("9"));
        let Reply::Line { result, .. } = &replies[2] else {
            panic!("not a line");
        };
        assert!(result.graph.is_some());
        let Reply::Line { result, .. } = &replies[3] else {
            panic!("not a line");
        };
        assert_eq!(result.kind, ResultKind::Error);
        assert!(result.typst.is_none());
        assert!(result.plain.is_none());
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

    fn texts(replies: &[Reply]) -> Vec<&str> {
        replies
            .iter()
            .filter_map(|reply| match reply {
                Reply::Line { result, .. } => Some(result.text.as_str()),
                _ => None,
            })
            .collect()
    }

    /// The keys of the lines, with whether they changed the state.
    fn keys(replies: &[Reply]) -> Vec<(u64, bool)> {
        replies
            .iter()
            .filter_map(|reply| match reply {
                Reply::Line { key, replay, .. } => Some((*key, *replay)),
                _ => None,
            })
            .collect()
    }

    #[test]
    fn test_reuse() {
        let mut worker = Worker::new();
        let replies = run(&mut worker, &request(1, &["a := 2", "1 + 1", "a + 1"]));
        assert_eq!(texts(&replies)[2], "3");
        assert_eq!(worker.evaluations, 3);
        let first = keys(&replies);

        // Editing a line which changes no state evaluates only this line, the others keep their key
        let replies = run(&mut worker, &request(2, &["a := 2", "1 + 2", "a + 1"]));
        assert_eq!(texts(&replies)[1..], ["3", "3"]);
        assert_eq!(worker.evaluations, 4);
        let second = keys(&replies);
        assert_eq!(first[0], second[0]);
        assert_ne!(first[1], second[1]);
        assert_eq!(first[2], second[2]);

        // Editing a definition evaluates the lines after it again, with new keys
        let replies = run(&mut worker, &request(3, &["a := 5", "1 + 2", "a + 1"]));
        assert_eq!(texts(&replies)[2], "6");
        assert_eq!(worker.evaluations, 7);
        assert!(
            keys(&replies)
                .iter()
                .zip(&second)
                .all(|(new, old)| new != old)
        );

        // Profiling evaluates every line
        let mut profiled = request(4, &["a := 5", "1 + 2", "a + 1"]);
        profiled.profile = true;
        run(&mut worker, &profiled);
        assert_eq!(worker.evaluations, 10);
    }

    #[test]
    fn test_serialize() {
        let mut worker = Worker::new();
        // Graphs with non-finite constants (`undefined`, `oo`), compared by their JSON since NaN != NaN
        let lines = [
            "y = a*sin(x)",
            "x^2 + y^2 < 1",
            "integrate(sqrt(x/r-1),r,r_1,x)",
            "piecewise(x < 0, oo, x)",
        ];
        let mut all = String::new();
        for reply in run(&mut worker, &request(1, &lines)) {
            let json = serde_json::to_string(&reply).unwrap();
            let read = serde_json::from_str::<Reply>(&json).unwrap();
            assert_eq!(serde_json::to_string(&read).unwrap(), json);
            all += &json;
        }
        assert!(all.contains(r#"{"Const":"NaN"}"#) && all.contains(r#"{"Const":"inf"}"#));
    }
}
