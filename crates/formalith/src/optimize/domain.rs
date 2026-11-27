//! The domain of a function as it was typed. The parser normalizes each node as it builds it, so `x^3/x` is
//! `x^2` before the optimizer sees it, and the condition `{$x != 0$}` is lost. While [`recording`], the parser
//! passes the raw nodes whose normalization may drop conditions (powers, quotients, calls) to [`record`]; the
//! optimizer then collects the conditions of definition of these terms too.

use std::cell::RefCell;

use crate::{
    field::{
        Set,
        real::{Real, expr::Expr},
    },
    term::Term,
};

thread_local! {
    /// The raw nodes recorded on this thread, `None` when not recording.
    static RECORDED: RefCell<Option<Vec<Expr>>> = const { RefCell::new(None) };
}

/// The sets whose raw nodes are recorded: only [`Real`], where extrema are found.
trait RecordDomain: Set {
    /// Record the term built by `make`, if recording.
    fn record(make: impl FnOnce() -> Term<Self>);

    /// The recorded terms as terms of this set.
    fn recorded(terms: Vec<Expr>) -> Vec<Term<Self>>;
}

impl<T: Set> RecordDomain for T {
    default fn record(_: impl FnOnce() -> Term<Self>) {}

    default fn recorded(_: Vec<Expr>) -> Vec<Term<Self>> {
        vec![]
    }
}

impl RecordDomain for Real {
    fn record(make: impl FnOnce() -> Term<Self>) {
        RECORDED.with_borrow_mut(|recorded| {
            if let Some(recorded) = recorded {
                recorded.push(make());
            }
        });
    }

    fn recorded(terms: Vec<Expr>) -> Vec<Term<Self>> {
        terms
    }
}

/// Record the raw node built by `make` (only called while [`recording`] terms of [`Real`]).
pub fn record<T: Set>(make: impl FnOnce() -> Term<T>) {
    <T as RecordDomain>::record(make);
}

/// Run `f`, returning its result and the raw nodes [`record`]ed meanwhile.
pub fn recording<E: Set, R>(f: impl FnOnce() -> R) -> (R, Vec<Term<E>>) {
    /// Restores the previous recording, also on panic.
    struct Guard(Option<Vec<Expr>>);
    impl Drop for Guard {
        fn drop(&mut self) {
            let previous = self.0.take();
            RECORDED.with_borrow_mut(|recorded| *recorded = previous);
        }
    }
    let guard = Guard(RECORDED.with_borrow_mut(|recorded| recorded.replace(vec![])));
    let res = f();
    let terms = RECORDED.with_borrow_mut(Option::take).unwrap_or_default();
    drop(guard);
    (res, <E as RecordDomain>::recorded(terms))
}
