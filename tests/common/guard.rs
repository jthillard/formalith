//! Run a case in its own thread, catching panics and giving up after a timeout.
use std::{
    panic::{AssertUnwindSafe, catch_unwind},
    sync::mpsc,
    thread,
    time::{Duration, Instant},
};

/// Stack size of guarded threads: the recursive term types need deep stacks.
pub const STACK_SIZE: usize = 256 << 20;

/// How a guarded computation ended.
#[derive(Debug)]
pub enum Outcome<T> {
    /// It returned.
    Done(T),
    /// It panicked, with this message.
    Panic(String),
    /// It didn't finish in time; its thread is leaked.
    Timeout,
}

/// The message of a panic payload.
pub fn panic_message(payload: &(dyn std::any::Any + Send)) -> String {
    payload
        .downcast_ref::<&str>()
        .map(|s| (*s).to_owned())
        .or_else(|| payload.downcast_ref::<String>().cloned())
        .unwrap_or_else(|| "<non-string panic>".to_owned())
}

/// A guarded computation started by [`spawn_guarded`].
pub struct Pending<T>(mpsc::Receiver<Result<T, String>>);

impl<T> Pending<T> {
    /// Wait for the result until `deadline`.
    pub fn wait(self, deadline: Instant) -> Outcome<T> {
        match self.0.recv_timeout(deadline.saturating_duration_since(Instant::now())) {
            Ok(Ok(value)) => Outcome::Done(value),
            Ok(Err(message)) => Outcome::Panic(message),
            Err(_) => Outcome::Timeout,
        }
    }
}

/// Start `f` in a new thread with a big stack, catching panics.
pub fn spawn_guarded<T: Send + 'static>(f: impl FnOnce() -> T + Send + 'static) -> Pending<T> {
    let (sender, receiver) = mpsc::channel();
    thread::Builder::new()
        .stack_size(STACK_SIZE)
        .spawn(move || {
            let result = catch_unwind(AssertUnwindSafe(f)).map_err(|e| panic_message(&*e));
            let _ = sender.send(result);
        })
        .expect("failed to spawn a guarded thread");
    Pending(receiver)
}

/// Run `f` in a new thread with a big stack, catching panics, waiting at most `timeout`.
pub fn run_guarded<T: Send + 'static>(
    timeout: Duration,
    f: impl FnOnce() -> T + Send + 'static,
) -> Outcome<T> {
    let (sender, receiver) = mpsc::channel();
    thread::Builder::new()
        .stack_size(STACK_SIZE)
        .spawn(move || {
            let result = catch_unwind(AssertUnwindSafe(f)).map_err(|e| panic_message(&*e));
            let _ = sender.send(result);
        })
        .expect("failed to spawn a guarded thread");
    match receiver.recv_timeout(timeout) {
        Ok(Ok(value)) => Outcome::Done(value),
        Ok(Err(message)) => Outcome::Panic(message),
        Err(_) => Outcome::Timeout,
    }
}

/// Run `f`, turning a panic into `None`, on the current thread.
pub fn no_panic<T>(f: impl FnOnce() -> T) -> Option<T> {
    catch_unwind(AssertUnwindSafe(f)).ok()
}
