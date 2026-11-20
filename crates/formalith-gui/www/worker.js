// Evaluates lines off the main thread. Unsupported operations panic, which aborts the wasm instance: the main
// thread is then told the worker crashed, and replaces it.
import init, { worker_evaluate } from './pkg/formalith_gui.js';

const ready = init();

// Evaluates a JSON request, posting a JSON reply per line, or `crashed` after a panic.
onmessage = async ({ data }) => {
  await ready;
  try {
    worker_evaluate(data, (reply) => postMessage(reply));
  } catch (err) {
    console.error(err);
    postMessage('crashed');
  }
};
