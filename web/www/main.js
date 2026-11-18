// Terminal-like interface to the Formalith wasm build. Mirrors `src/bin/cli.rs`: expressions are evaluated in the
// current set, `:set <name>` changes it, `:typst` toggles between rendered math and plain text output. Definitions
// like `f(x) := x^2` live in the worker: they are replayed in a new worker after a panic.

const log = document.getElementById('log');
const form = document.getElementById('prompt');
const input = document.getElementById('input');
const label = document.getElementById('prompt-label');
const busy = document.getElementById('busy');

const HISTORY_KEY = 'formalith-history';
const HISTORY_SIZE = 500;
// Text color used by Typst, replaced by `currentColor` in the SVG so results follow the page theme.
const TYPST_FILL = '#010203';

let set = 'R';
let setsHelp = '';
let typst = true;

let history = [];
try {
  history = JSON.parse(localStorage.getItem(HISTORY_KEY)) ?? [];
} catch {}
let historyIndex = history.length;
let draft = '';

function saveHistory() {
  try {
    localStorage.setItem(HISTORY_KEY, JSON.stringify(history.slice(-HISTORY_SIZE)));
  } catch {}
}

function print(text, className = 'info') {
  const line = document.createElement('p');
  line.className = className;
  line.textContent = text;
  log.append(line);
  return line;
}

function echo(text) {
  const line = document.createElement('p');
  line.className = 'line';
  const prompt = document.createElement('span');
  prompt.className = 'prompt';
  prompt.textContent = `${set}>`;
  line.append(prompt, text);
  log.append(line);
}

function scrollToPrompt() {
  form.scrollIntoView({ block: 'end' });
}

// Typst rendering

let typstReady = false;
function initTypst() {
  if (typstReady || !globalThis.$typst) {
    return typstReady;
  }
  $typst.setCompilerInitOptions({
    getModule: () =>
      'https://cdn.jsdelivr.net/npm/@myriaddreamin/typst-ts-web-compiler@v0.7.0-rc1/pkg/typst_ts_web_compiler_bg.wasm',
  });
  $typst.setRendererInitOptions({
    getModule: () =>
      'https://cdn.jsdelivr.net/npm/@myriaddreamin/typst-ts-renderer@v0.7.0-rc1/pkg/typst_ts_renderer_bg.wasm',
  });
  typstReady = true;
  return true;
}

// Renders are chained so the compiler is never used concurrently.
let renderQueue = Promise.resolve();
function renderMath(source) {
  // Typst points are rendered as CSS pixels, the math font is scaled up to match the monospace text
  const fontSize = parseFloat(getComputedStyle(document.body).fontSize) * 1.25;
  const mainContent =
    `#set page(width: auto, height: auto, margin: (x: 0pt, y: 0.3em));\n` +
    `#set text(size: ${fontSize}pt, fill: rgb("${TYPST_FILL}"));\n` +
    `$ ${source} $`;
  const svg = renderQueue.then(() => $typst.svg({ mainContent }));
  renderQueue = svg.catch(() => {});
  return svg.then(svg => {
    if (typeof svg !== 'string' || !svg.includes('<svg')) {
      throw new Error('typst rendering failed');
    }
    return svg.replaceAll(TYPST_FILL, 'currentColor');
  });
}

function printResult(text, rendered) {
  const result = print(text, 'result');
  result.title = 'Click to copy';
  result.addEventListener('click', () => {
    navigator.clipboard?.writeText(text).then(() => {
      result.classList.add('copied');
      setTimeout(() => result.classList.remove('copied'), 1000);
    });
  });
  if (rendered && initTypst()) {
    renderMath(text).then(
      svg => {
        result.innerHTML = svg;
        scrollToPrompt();
      },
      err => console.error(err),
    );
  }
}

// Evaluation worker

let worker;
let pending = null;
let nextId = 0;
// Definitions and removals in order, with the set definitions were made in, replayed in a new worker
let definitionLog = [];

function startWorker() {
  worker = new Worker('worker.js', { type: 'module' });
  worker.onmessage = ({ data }) => {
    if (data.ready) {
      setsHelp = data.help;
      return;
    }
    if (!pending || data.id !== pending.id) {
      return;
    }
    const { set: evalSet, typst: rendered, setName, input: evalInput, defs, clear } = pending;
    finish();
    if (defs && data.ok !== undefined) {
      print(data.ok || 'no definitions');
    } else if (clear !== undefined && data.ok !== undefined) {
      definitionLog = clear ? [...definitionLog, { clear }] : [];
    } else if (setName !== undefined) {
      if (data.ok !== undefined) {
        set = data.ok;
        label.textContent = `${set}>`;
      } else {
        print(`error: ${data.err ?? 'invalid set'}`, 'error');
      }
    } else if (data.ok !== undefined) {
      if (data.definition) {
        definitionLog.push({ input: evalInput, set: evalSet });
      }
      printResult(data.ok, rendered);
    } else if (data.err !== undefined) {
      print(`error: ${data.err}`, 'error');
    } else {
      // The wasm instance aborted on a panic and can't be reused
      print(`error: this operation is not supported in ${evalSet}`, 'error');
      restartWorker();
    }
    scrollToPrompt();
  };
  worker.onerror = event => {
    event.preventDefault();
    console.error(event);
    if (pending) {
      finish();
      print(`error: ${event.message || 'failed to load the evaluator'}`, 'error');
    }
    restartWorker();
  };
}

function restartWorker() {
  worker.terminate();
  startWorker();
  // Answers to these messages don't match a pending request and are ignored
  for (const { input, set: evalSet, clear } of definitionLog) {
    worker.postMessage(clear === undefined ? { id: -1, input, set: evalSet, typst: false } : { id: -1, clear });
  }
}

function finish() {
  pending = null;
  busy.hidden = true;
}

function evaluate(expression) {
  pending = { id: nextId++, set, typst, input: expression };
  busy.hidden = false;
  worker.postMessage({ id: pending.id, input: expression, set, typst });
}

// Lists definitions if `defs` is set, or removes the definition `clear` (all of them if empty)
function definitionCommand(command) {
  pending = { id: nextId++, ...command };
  busy.hidden = false;
  worker.postMessage({ id: pending.id, ...command });
}

// Sets are parameterized (like `Z/7` or `R[x]`), names are checked by the worker
function changeSet(name) {
  pending = { id: nextId++, setName: name };
  busy.hidden = false;
  worker.postMessage({ id: pending.id, setName: name });
}

// Commands

function help() {
  print(
    [
      'Enter an expression to evaluate it, like `expand((x+1)^3)` or `factor(x^2-1)`.',
      'Define variables and functions with `a := x^2` or `f(x, y) := x*y`.',
      'Solve linear systems with `x + y = 3, x - y = 1`.',
      'commands:',
      '  :defs         list definitions',
      '  :clear [name] remove a definition, or all of them',
      '  :set          show the current set',
      '  :set <name>   evaluate in another set',
      `  :typst        toggle rendered math output (currently ${typst ? 'on' : 'off'})`,
      '  clear         clear the screen (also Ctrl+L)',
      '  help          show this help',
      'Ctrl+C interrupts a running computation.',
      setsHelp,
    ].join('\n'),
  );
}

function run(line) {
  echo(line);
  if (line === ':typst') {
    typst = !typst;
    print(`typst output ${typst ? 'enabled' : 'disabled'}`);
  } else if (line === 'help' || line === ':help') {
    help();
  } else if (line.startsWith(':set')) {
    const name = line.slice(4).trim();
    if (!name) {
      print(`current set: ${set}\n${setsHelp}`);
    } else {
      changeSet(name);
    }
  } else if (line === ':defs') {
    definitionCommand({ defs: true });
  } else if (line.startsWith(':clear')) {
    definitionCommand({ clear: line.slice(6).trim() });
  } else {
    evaluate(line);
  }
}

form.addEventListener('submit', event => {
  event.preventDefault();
  if (pending) {
    return;
  }
  const line = input.value.trim();
  input.value = '';
  draft = '';
  if (line === 'clear') {
    log.replaceChildren();
  } else if (line) {
    if (history.at(-1) !== line) {
      history.push(line);
      saveHistory();
    }
    run(line);
  }
  historyIndex = history.length;
  scrollToPrompt();
});

input.addEventListener('keydown', event => {
  if (event.key === 'ArrowUp' || event.key === 'ArrowDown') {
    event.preventDefault();
    if (historyIndex === history.length) {
      draft = input.value;
    }
    historyIndex = Math.max(
      0,
      Math.min(history.length, historyIndex + (event.key === 'ArrowUp' ? -1 : 1)),
    );
    input.value = historyIndex === history.length ? draft : history[historyIndex];
    input.setSelectionRange(input.value.length, input.value.length);
  } else if (event.ctrlKey && event.key === 'l') {
    event.preventDefault();
    log.replaceChildren();
  } else if (event.ctrlKey && event.key === 'c' && input.selectionStart === input.selectionEnd) {
    event.preventDefault();
    if (pending) {
      finish();
      print('interrupted', 'error');
      restartWorker();
    } else {
      echo(`${input.value}^C`);
      input.value = '';
    }
    scrollToPrompt();
  }
});

// Focus the prompt when clicking the terminal, unless text is being selected
document.getElementById('terminal').addEventListener('click', () => {
  if (getSelection().isCollapsed) {
    input.focus();
  }
});

startWorker();
print('Formalith — type `help` for the list of commands.');
