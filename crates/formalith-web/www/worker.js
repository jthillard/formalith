// Evaluates lines off the main thread. Unsupported operations panic, which aborts the wasm instance: the main
// thread is then told to replace this worker.
import init, { run, set_typst } from './pkg/formalith_web.js';

const ready = init().then(() => {
  set_typst(true);
  postMessage({ ready: true });
});

// Runs `line` in the session, answering its kind, text, text in Formalith syntax, whether to replay it and the current set.
onmessage = async ({ data: { id, line } }) => {
  await ready;
  try {
    const answer = run(line);
    postMessage({ id, kind: answer.kind, text: answer.text, plain: answer.plain, replay: answer.replay, set: answer.set });
    answer.free();
  } catch (err) {
    postMessage({ id, panic: String(err) });
  }
};
