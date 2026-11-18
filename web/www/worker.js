// Evaluates expressions off the main thread. Unsupported operations panic, which aborts the wasm instance: the
// main thread is then told to replace this worker.
import init, {
  clear_definitions,
  definitions,
  evaluate,
  is_definition,
  set_name,
  sets_help,
} from './pkg/formalith_web.js';

const ready = init().then(() => postMessage({ ready: true, help: sets_help() }));

// Evaluates `input` in `set` (telling if it is a definition), checks the set name `setName` and answers its
// canonical name, lists definitions if `defs` is set, or removes the definition `clear` (all of them if empty).
onmessage = async ({ data: { id, input, set, typst, setName, defs, clear } }) => {
  await ready;
  try {
    if (setName !== undefined) {
      postMessage({ id, ok: set_name(setName) });
    } else if (defs) {
      postMessage({ id, ok: definitions() });
    } else if (clear !== undefined) {
      clear_definitions(clear);
      postMessage({ id, ok: '' });
    } else {
      postMessage({ id, ok: evaluate(input, set, typst), definition: is_definition(input) });
    }
  } catch (err) {
    if (typeof err === 'string') {
      postMessage({ id, err });
    } else {
      postMessage({ id, panic: String(err) });
    }
  }
};
