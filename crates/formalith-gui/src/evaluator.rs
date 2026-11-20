//! Evaluation of the lines off the interface thread: in a thread natively, in a Web Worker in the browser.
//!
//! [`Evaluator`] sends one [`Request`] at a time to its [`Backend`] and keeps only the newest one waiting. A
//! backend is replaced after a crash (a panic aborts the wasm instance), skipping the line which crashed, or when
//! it is stuck on an outdated request while a newer one waits.

use std::collections::VecDeque;

use crate::protocol::{CRASHED, Reply, Request};

/// What a backend reports.
#[derive(Debug)]
pub enum Event {
    /// An answer to a request.
    Reply(Reply),
    /// The backend crashed and can't evaluate anything anymore.
    Crashed,
}

/// A worker evaluating requests in order.
pub trait Backend {
    /// Queue `request`.
    fn send(&mut self, request: &Request);
    /// The events since the last call.
    fn poll(&mut self) -> Vec<Event>;
}

/// Creates backends, a new one after a crash.
pub type BackendFactory = Box<dyn Fn() -> Box<dyn Backend>>;

/// Seconds an outdated request may run while a newer one waits.
const PATIENCE: f64 = 1.5;

/// Sends requests to a backend and recovers from its crashes.
pub struct Evaluator {
    factory: BackendFactory,
    backend: Box<dyn Backend>,
    /// The request being evaluated, with the number of lines answered.
    running: Option<(Request, usize)>,
    /// The newest request, waiting for the running one.
    waiting: Option<Request>,
    /// When the running request was sent or last answered.
    last_activity: f64,
    /// Inputs which crashed a backend.
    skip: Vec<String>,
    /// Replies to give to the interface.
    replies: VecDeque<Reply>,
}

impl Evaluator {
    /// An evaluator with backends from `factory`.
    #[must_use]
    pub fn new(factory: BackendFactory) -> Self {
        Self {
            backend: factory(),
            factory,
            running: None,
            waiting: None,
            last_activity: 0.,
            skip: vec![],
            replies: VecDeque::new(),
        }
    }

    /// Evaluate `request` once the running one is done, replacing the one waiting.
    pub fn send(&mut self, request: Request, now: f64) {
        self.waiting = Some(request);
        self.start_waiting(now);
    }

    /// Check if a request is running or waiting.
    #[must_use]
    pub const fn is_busy(&self) -> bool {
        self.running.is_some() || self.waiting.is_some()
    }

    /// The generation of the running request.
    #[must_use]
    pub fn running_generation(&self) -> Option<u64> {
        self.running.as_ref().map(|(request, _)| request.generation)
    }

    /// Send the waiting request if nothing is running.
    fn start_waiting(&mut self, now: f64) {
        if self.running.is_none()
            && let Some(mut request) = self.waiting.take()
        {
            request.skip.clone_from(&self.skip);
            self.backend.send(&request);
            self.running = Some((request, 0));
            self.last_activity = now;
        }
    }

    /// Replace the backend, for example after a crash, and send the running request again.
    fn restart(&mut self, now: f64) {
        self.backend = (self.factory)();
        if let Some((request, _)) = self.running.take() {
            // The newest request first
            if self.waiting.is_none() {
                self.waiting = Some(request);
            }
        }
        self.start_waiting(now);
    }

    /// The replies received since the last call, handling crashes and stuck requests.
    pub fn poll(&mut self, now: f64) -> Vec<Reply> {
        for event in self.backend.poll() {
            match event {
                Event::Reply(reply) => {
                    let Some((request, answered)) = &mut self.running else {
                        continue;
                    };
                    self.last_activity = now;
                    match &reply {
                        Reply::Line { generation, .. } if *generation == request.generation => {
                            *answered += 1
                        }
                        Reply::Done { generation } if *generation == request.generation => {
                            self.running = None;
                        }
                        _ => {}
                    }
                    self.replies.push_back(reply);
                }
                Event::Crashed => {
                    // The first line without an answer crashed the backend
                    if let Some((request, answered)) = &self.running
                        && let Some(line) = request.lines.get(*answered)
                    {
                        self.skip.push(line.text.clone());
                        let reply = Reply::Line {
                            generation: request.generation,
                            id: line.id,
                            result: crate::protocol::LineResult::error(CRASHED),
                        };
                        self.replies.push_back(reply);
                    }
                    self.restart(now);
                    // The next events come from the crashed backend
                    break;
                }
            }
        }
        if self.running.is_some() && self.waiting.is_some() && now - self.last_activity > PATIENCE {
            // An outdated request takes too long: drop it for the newer one
            self.running = None;
            self.restart(now);
        }
        self.start_waiting(now);
        self.replies.drain(..).collect()
    }
}

#[cfg(not(target_arch = "wasm32"))]
pub use native::NativeBackend;

#[cfg(not(target_arch = "wasm32"))]
mod native {
    use std::{
        sync::mpsc::{self, Receiver, Sender, TryRecvError},
        thread,
    };

    use super::{Backend, Event};
    use crate::protocol::{Reply, Request, Worker};

    /// A backend evaluating requests in a thread. A replaced backend's thread stops at its next reply.
    pub struct NativeBackend {
        requests: Sender<Request>,
        replies: Receiver<Reply>,
    }

    impl NativeBackend {
        /// Start a thread, calling `notify` after each reply, like to repaint the interface.
        #[must_use]
        pub fn new(notify: impl Fn() + Send + 'static) -> Self {
            let (requests, receiver) = mpsc::channel::<Request>();
            let (sender, replies) = mpsc::channel();
            thread::Builder::new()
                .name("formalith-worker".to_owned())
                .spawn(move || {
                    let mut worker = Worker::new();
                    while let Ok(mut request) = receiver.recv() {
                        // Only the newest request matters
                        while let Ok(newer) = receiver.try_recv() {
                            request = newer;
                        }
                        let mut connected = true;
                        worker.evaluate(&request, |reply| {
                            connected = sender.send(reply).is_ok();
                            notify();
                            connected
                        });
                        if !connected {
                            return;
                        }
                    }
                })
                .expect("Failed to start the evaluation thread");
            Self { requests, replies }
        }
    }

    impl Backend for NativeBackend {
        fn send(&mut self, request: &Request) {
            // A closed channel is reported as a crash by `poll`
            let _ = self.requests.send(request.clone());
        }

        fn poll(&mut self) -> Vec<Event> {
            let mut events = vec![];
            loop {
                match self.replies.try_recv() {
                    Ok(reply) => events.push(Event::Reply(reply)),
                    Err(TryRecvError::Empty) => break,
                    Err(TryRecvError::Disconnected) => {
                        events.push(Event::Crashed);
                        break;
                    }
                }
            }
            events
        }
    }
}

#[cfg(target_arch = "wasm32")]
pub use web::WebBackend;

#[cfg(target_arch = "wasm32")]
mod web {
    use std::{cell::RefCell, rc::Rc};

    use wasm_bindgen::{JsCast, closure::Closure};
    use web_sys::{ErrorEvent, MessageEvent, Worker, WorkerOptions, WorkerType};

    use super::{Backend, Event};
    use crate::protocol::{Reply, Request};

    /// A backend evaluating requests in a Web Worker running `worker.js`, terminated when replaced.
    pub struct WebBackend {
        worker: Worker,
        events: Rc<RefCell<Vec<Event>>>,
        _on_message: Closure<dyn FnMut(MessageEvent)>,
        _on_error: Closure<dyn FnMut(ErrorEvent)>,
    }

    impl WebBackend {
        /// Start a worker, calling `notify` after each reply, like to repaint the interface.
        ///
        /// # Panics
        /// Panics if the worker can't be created.
        #[must_use]
        pub fn new(notify: impl Fn() + 'static) -> Self {
            let options = WorkerOptions::new();
            options.set_type(WorkerType::Module);
            let worker = Worker::new_with_options("./worker.js", &options)
                .expect("Failed to start the worker");
            let events = Rc::new(RefCell::new(vec![]));
            let notify = Rc::new(notify);
            let on_message = {
                let events = Rc::clone(&events);
                let notify = Rc::clone(&notify);
                Closure::<dyn FnMut(MessageEvent)>::new(move |message: MessageEvent| {
                    let Some(json) = message.data().as_string() else {
                        return;
                    };
                    let event =
                        serde_json::from_str::<Reply>(&json).map_or(Event::Crashed, Event::Reply);
                    events.borrow_mut().push(event);
                    notify();
                })
            };
            let on_error = {
                let events = Rc::clone(&events);
                Closure::<dyn FnMut(ErrorEvent)>::new(move |error: ErrorEvent| {
                    error.prevent_default();
                    events.borrow_mut().push(Event::Crashed);
                    notify();
                })
            };
            worker.set_onmessage(Some(on_message.as_ref().unchecked_ref()));
            worker.set_onerror(Some(on_error.as_ref().unchecked_ref()));
            Self {
                worker,
                events,
                _on_message: on_message,
                _on_error: on_error,
            }
        }
    }

    impl Backend for WebBackend {
        fn send(&mut self, request: &Request) {
            let json = serde_json::to_string(request).expect("Requests are serializable");
            if self.worker.post_message(&json.into()).is_err() {
                self.events.borrow_mut().push(Event::Crashed);
            }
        }

        fn poll(&mut self) -> Vec<Event> {
            std::mem::take(&mut *self.events.borrow_mut())
        }
    }

    impl Drop for WebBackend {
        fn drop(&mut self) {
            self.worker.set_onmessage(None);
            self.worker.set_onerror(None);
            self.worker.terminate();
        }
    }
}

#[cfg(test)]
mod tests {
    use std::{cell::RefCell, rc::Rc};

    use super::*;
    use crate::protocol::{LineResult, RequestLine};

    /// A backend answering synchronously, crashing on lines `crash`.
    struct Fake {
        events: Vec<Event>,
        log: Rc<RefCell<Vec<Request>>>,
    }

    impl Backend for Fake {
        fn send(&mut self, request: &Request) {
            self.log.borrow_mut().push(request.clone());
            for line in &request.lines {
                if line.text == "crash" && !request.skip.contains(&line.text) {
                    self.events.push(Event::Crashed);
                    return;
                }
                self.events.push(Event::Reply(Reply::Line {
                    generation: request.generation,
                    id: line.id,
                    result: LineResult::error(line.text.clone()),
                }));
            }
            self.events.push(Event::Reply(Reply::Done {
                generation: request.generation,
            }));
        }

        fn poll(&mut self) -> Vec<Event> {
            std::mem::take(&mut self.events)
        }
    }

    #[test]
    fn test_crash() {
        let log = Rc::new(RefCell::new(vec![]));
        let factory_log = Rc::clone(&log);
        let mut evaluator = Evaluator::new(Box::new(move || {
            Box::new(Fake {
                events: vec![],
                log: Rc::clone(&factory_log),
            })
        }));
        let lines = ["1", "crash", "2"]
            .iter()
            .zip(0..)
            .map(|(text, id)| RequestLine {
                id,
                text: (*text).to_owned(),
            })
            .collect();
        evaluator.send(
            Request {
                generation: 1,
                set: "R".to_owned(),
                lines,
                skip: vec![],
                profile: false,
            },
            0.,
        );
        let replies = evaluator.poll(0.);
        // The line which crashed gets an error, the request is sent again without it
        assert!(matches!(&replies[1], Reply::Line { id: 1, result, .. } if result.text == CRASHED));
        assert_eq!(log.borrow().len(), 2);
        assert_eq!(log.borrow()[1].skip, ["crash"]);
        let replies = evaluator.poll(0.);
        assert_eq!(replies.len(), 4);
        assert!(!evaluator.is_busy());
    }
}
