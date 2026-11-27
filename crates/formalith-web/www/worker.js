// Evaluates lines off the main thread. Unsupported operations panic, which aborts the wasm instance: the main
// thread is then told to replace this worker.
import init, { complete, run, set_typst } from './pkg/formalith_web.js';

const ready = init().then(() => {
  set_typst(true);
  postMessage({ ready: true });
});

// Runs `line` in the session, answering its kind, text, text in Formalith syntax, the line as Typst, whether to replay it and the current set.
// Or answers the completions of the word ending at `pos` in `line`, when asked with `complete`.
onmessage = async ({ data: { id, line, complete: pos } }) => {
  await ready;
  if (pos !== undefined) {
    const completion = complete(line, pos);
    postMessage({ id, completion: { start: completion.start, candidates: completion.candidates } });
    completion.free();
    return;
  }
  try {
    const answer = run(line);
    postMessage({ id, kind: answer.kind, text: answer.text, plain: answer.plain, input: answer.input, replay: answer.replay, set: answer.set });
    answer.free();
  } catch (err) {
    postMessage({ id, panic: String(err) });
  }
};
