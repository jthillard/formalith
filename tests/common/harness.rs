//! Running checks on many cases, sorting failures into wrong answers, panics and timeouts.
use std::{
    fmt::Write,
    sync::Arc,
    time::{Duration, Instant},
};

use super::{
    guard::{Outcome, spawn_guarded},
    numeric::Check,
    rng::{Rng, seed},
};

/// The conclusion of a check on one case.
#[derive(Debug)]
pub enum Verdict {
    /// The result satisfies its definition.
    Pass,
    /// The result is wrong.
    Wrong(String),
    /// Nothing could be checked (unevaluated result, invalid points...).
    Skip(String),
}

impl From<Check> for Verdict {
    fn from(check: Check) -> Self {
        match check {
            Check::Equal => Self::Pass,
            Check::Differ(why) => Self::Wrong(why),
            Check::Inconclusive(why) => Self::Skip(why),
        }
    }
}

/// Default timeout of a case.
pub const TIMEOUT: Duration = Duration::from_secs(60);

/// Number of fuzz cases: `FORMALITH_FUZZ_CASES` if set, else `default`.
pub fn cases(default: usize) -> usize {
    std::env::var("FORMALITH_FUZZ_CASES")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(default)
}

/// Outcomes of a run, by category.
#[derive(Default, Debug)]
pub struct Report {
    /// Cases that passed.
    pub passed: usize,
    /// Skipped cases with the reason.
    pub skipped: Vec<String>,
    /// Wrong answers.
    pub wrong: Vec<String>,
    /// Panics.
    pub panics: Vec<String>,
    /// Timeouts.
    pub timeouts: Vec<String>,
}

impl Report {
    /// Whether some case failed.
    pub fn failed(&self) -> bool {
        !(self.wrong.is_empty() && self.panics.is_empty() && self.timeouts.is_empty())
    }

    /// A summary listing every failure.
    pub fn summary(&self, name: &str, seed: u64) -> String {
        let mut s = format!(
            "{name} (seed {seed}): {} passed, {} skipped, {} wrong, {} panics, {} timeouts\n",
            self.passed,
            self.skipped.len(),
            self.wrong.len(),
            self.panics.len(),
            self.timeouts.len()
        );
        for (title, list) in [
            ("WRONG", &self.wrong),
            ("PANIC", &self.panics),
            ("TIMEOUT", &self.timeouts),
        ] {
            for item in list {
                let _ = writeln!(s, "  {title}: {item}");
            }
        }
        if std::env::var("FORMALITH_SHOW_SKIPPED").is_ok() {
            for item in &self.skipped {
                let _ = writeln!(s, "  SKIP: {item}");
            }
        }
        s
    }
}

/// Stop a run after this many timeouts, since their threads keep running.
const MAX_TIMEOUTS: usize = 4;

/// Check every input with `check` (in a guarded thread each, as many at once as there are cores or as
/// `FORMALITH_WORKERS` says), and return the report.
pub fn run_inputs<F>(inputs: &[String], timeout: Duration, check: F) -> Report
where
    F: Fn(&str) -> Verdict + Send + Sync + 'static,
{
    let check = Arc::new(check);
    let workers = std::env::var("FORMALITH_WORKERS")
        .ok()
        .and_then(|w| w.parse().ok())
        .unwrap_or_else(|| std::thread::available_parallelism().map_or(4, usize::from));
    let mut report = Report::default();
    for (chunk_index, chunk) in inputs.chunks(workers).enumerate() {
        let pending: Vec<_> = chunk
            .iter()
            .map(|input| {
                let (c, i) = (Arc::clone(&check), input.clone());
                spawn_guarded(move || {
                    let start = Instant::now();
                    let verdict = c(&i);
                    if std::env::var("FORMALITH_TIMES").is_ok() {
                        eprintln!("{:>8.3}s  {i}", start.elapsed().as_secs_f64());
                    }
                    verdict
                })
            })
            .collect();
        let deadline = Instant::now() + timeout;
        for (offset, (input, pending)) in chunk.iter().zip(pending).enumerate() {
            let index = chunk_index * workers + offset;
            match pending.wait(deadline) {
                Outcome::Done(Verdict::Pass) => report.passed += 1,
                Outcome::Done(Verdict::Skip(why)) => report.skipped.push(format!("#{index} `{input}`: {why}")),
                Outcome::Done(Verdict::Wrong(why)) => report.wrong.push(format!("#{index} `{input}`: {why}")),
                Outcome::Panic(message) => report.panics.push(format!("#{index} `{input}`: {message}")),
                Outcome::Timeout => report.timeouts.push(format!("#{index} `{input}`: no result after {timeout:?}")),
            }
        }
        // Timed out threads keep running
        if report.timeouts.len() >= MAX_TIMEOUTS {
            break;
        }
    }
    report
}

/// Check curated `inputs`, failing with a report if any case is wrong, panics or times out.
pub fn check_all<F>(name: &str, inputs: &[&str], check: F)
where
    F: Fn(&str) -> Verdict + Send + Sync + 'static,
{
    let inputs: Vec<_> = inputs.iter().map(|&s| s.to_owned()).collect();
    let report = run_inputs(&inputs, TIMEOUT, check);
    assert!(!report.failed(), "{}", report.summary(name, 0));
    // Curated cases must actually be checked
    assert!(report.skipped.is_empty(), "{}skipped: {:#?}", report.summary(name, 0), report.skipped);
}

/// Generate `cases(default)` inputs with `generate` from the run seed, check them, and fail with the report.
pub fn fuzz<G, F>(name: &str, default: usize, generate: G, check: F)
where
    G: Fn(&mut Rng) -> String,
    F: Fn(&str) -> Verdict + Send + Sync + 'static,
{
    let seed = seed();
    let inputs: Vec<_> = (0..cases(default))
        .map(|case| generate(&mut Rng::for_case(seed, case)))
        .collect();
    let report = run_inputs(&inputs, TIMEOUT, check);
    eprintln!("{}", report.summary(name, seed));
    assert!(!report.failed(), "{}", report.summary(name, seed));
}

/// Assert that `check` passes on `input` within `timeout` (for regression tests of bugs).
pub fn assert_pass<F>(input: &str, timeout: Duration, check: F)
where
    F: Fn(&str) -> Verdict + Send + Sync + 'static,
{
    let report = run_inputs(&[input.to_owned()], timeout, check);
    assert!(report.passed == 1, "{}", report.summary(input, 0));
}

/// A fixed generator for checks that sample points, so that a case always uses the same points.
pub fn case_rng(input: &str) -> Rng {
    let hash = input
        .bytes()
        .fold(0xCBF2_9CE4_8422_2325_u64, |h, b| (h ^ u64::from(b)).wrapping_mul(0x100_0000_01B3));
    Rng::new(hash ^ seed())
}
