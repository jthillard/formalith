// Evaluates expressions off the main thread. Unsupported operations panic, which aborts the wasm instance: the
// main thread is then told to replace this worker.
import init, { evaluate, set_name, sets_help } from './pkg/formalith_web.js';

const ready = init().then(() => postMessage({ ready: true, help: sets_help() }));

// Evaluates `input` in `set`, or checks the set name `setName` and answers its canonical name.
onmessage = async ({ data: { id, input, set, typst, setName } }) => {
  await ready;
  try {
    postMessage({ id, ok: setName === undefined ? evaluate(input, set, typst) : set_name(setName) });
  } catch (err) {
    if (typeof err === 'string') {
      postMessage({ id, err });
    } else {
      postMessage({ id, panic: String(err) });
    }
  }
};
