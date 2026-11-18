// Evaluates expressions off the main thread. Unsupported operations panic, which aborts the wasm instance: the
// main thread is then told to replace this worker.
import init, { evaluate, set_names, sets_help } from './pkg/formalith_web.js';

const ready = init().then(() => postMessage({ ready: true, sets: set_names(), help: sets_help() }));

onmessage = async ({ data: { id, input, set, typst } }) => {
  await ready;
  try {
    postMessage({ id, ok: evaluate(input, set, typst) });
  } catch (err) {
    if (typeof err === 'string') {
      postMessage({ id, err });
    } else {
      postMessage({ id, panic: String(err) });
    }
  }
};
