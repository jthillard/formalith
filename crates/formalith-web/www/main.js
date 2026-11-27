// Terminal-like interface to the Formalith wasm build. Lines are run by the session in the worker, like in the
// command line interface (`formalith-cli`): `:set <name>` changes the set, `:typst` toggles between rendered math
// and plain text output. Lines changing the session, like definitions `f(x) := x^2`, are replayed in a new worker
// after a panic. The transcript and these lines are kept in the local storage, so a reload shows the transcript
// again and restores the session; `clear` (or Ctrl+L) clears the transcript. With Typst output, an input line is
// typeset once evaluated, as it was typed (the session prints it without evaluating it). Tab completes builtins,
// definitions, commands and sets, listing the candidates when there are several.

const log = document.getElementById('log');
const form = document.getElementById('prompt');
const input = document.getElementById('input');
const label = document.getElementById('prompt-label');
const busy = document.getElementById('busy');

const HISTORY_KEY = 'formalith-history';
const HISTORY_SIZE = 500;
const TRANSCRIPT_KEY = 'formalith-transcript';
const TRANSCRIPT_SIZE = 1000;
const REPLAY_KEY = 'formalith-replay';
// Text color used by Typst, replaced by `currentColor` in the SVG so results follow the page theme.
const TYPST_FILL = '#010203';

let set = 'R';

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

function load(key) {
  try {
    return JSON.parse(localStorage.getItem(key)) ?? [];
  } catch {
    return [];
  }
}

function store(key, value) {
  try {
    localStorage.setItem(key, JSON.stringify(value));
  } catch {}
}

// Entries of the transcript shown: `{ kind: 'line', set, text, interrupted, typst }` (`typst` the typeset input), `{ kind: 'result', text, plain,
// rendered }`, `{ kind: 'info' | 'error', text }`
let transcript = load(TRANSCRIPT_KEY);
// Whether the stored transcript is being shown again, so it isn't recorded twice
let restoring = false;

function record(entry) {
  if (restoring) {
    return;
  }
  transcript.push(entry);
  if (transcript.length > TRANSCRIPT_SIZE) {
    transcript = transcript.slice(-TRANSCRIPT_SIZE);
  }
  store(TRANSCRIPT_KEY, transcript);
}

function clearLog() {
  log.replaceChildren();
  transcript = [];
  store(TRANSCRIPT_KEY, transcript);
}

// Shows a line of output without recording it
function show(text, className) {
  const line = document.createElement('p');
  line.className = className;
  line.textContent = text;
  log.append(line);
  return line;
}

function print(text, className = 'info') {
  record({ kind: className, text });
  return show(text, className);
}

// Copies `text` when `element` is clicked, unless text is being selected
function copyOnClick(element, text) {
  element.classList.add('copyable');
  element.title = 'Click to copy';
  element.addEventListener('click', () => {
    if (!getSelection().isCollapsed) {
      return;
    }
    navigator.clipboard?.writeText(text).then(() => {
      element.classList.add('copied');
      setTimeout(() => element.classList.remove('copied'), 1000);
    });
  });
}

// Echoes an input line typed in `lineSet`, copied when clicked unless it is `interrupted` (a line cancelled with
// Ctrl+C), typeset if `typst` is given. Returns the element and its transcript entry, so the line can be typeset once
// evaluated.
function echo(text, interrupted = false, lineSet = set, typst = undefined) {
  const entry = { kind: 'line', set: lineSet, text, interrupted };
  record(entry);
  const line = document.createElement('p');
  line.className = 'line';
  const prompt = document.createElement('span');
  prompt.className = 'prompt';
  prompt.textContent = `${lineSet}>`;
  line.append(prompt, interrupted ? `${text}^C` : text);
  if (!interrupted && text) {
    copyOnClick(line, text);
  }
  log.append(line);
  if (typst) {
    entry.typst = typst;
    renderInput(line, typst);
  }
  return { element: line, entry };
}

function scrollToPrompt() {
  form.scrollIntoView({ block: 'end' });
}

// Theme: the one chosen with the button (also read by the inline script of the page, so it applies before the page
// is drawn), otherwise the system one. Typst results use `currentColor`, so they follow it.

const THEME_KEY = 'formalith-theme';
const themeButton = document.getElementById('theme');
const systemDark = matchMedia('(prefers-color-scheme: dark)');

function currentTheme() {
  return document.documentElement.dataset.theme ?? (systemDark.matches ? 'dark' : 'light');
}

function showThemeButton() {
  const dark = currentTheme() === 'dark';
  themeButton.textContent = dark ? '☀' : '☾';
  themeButton.title = dark ? 'Switch to the light theme' : 'Switch to the dark theme';
}

themeButton.addEventListener('click', () => {
  const theme = currentTheme() === 'dark' ? 'light' : 'dark';
  document.documentElement.dataset.theme = theme;
  try {
    localStorage.setItem(THEME_KEY, theme);
  } catch {}
  showThemeButton();
});
systemDark.addEventListener('change', showThemeButton);
showThemeButton();

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

function typstDocument(source) {
  // Typst points are rendered as CSS pixels, the math font is scaled up to match the monospace text
  const fontSize = parseFloat(getComputedStyle(document.body).fontSize) * 1.25;
  return (
    `#set page(width: auto, height: auto, margin: (x: 0pt, y: 0.3em));\n` +
    `#set text(size: ${fontSize}pt, fill: rgb("${TYPST_FILL}"));\n` +
    `$ ${source} $`
  );
}

// Renders a first formula once the evaluator is ready, so the compiler, the renderer and the fonts are downloaded
// before the first result instead of after it.
let typstPrefetched = false;
function prefetchTypst() {
  if (typstPrefetched || !initTypst()) {
    return;
  }
  typstPrefetched = true;
  const mainContent = typstDocument('x');
  renderQueue = renderQueue.then(() => $typst.svg({ mainContent })).catch(err => console.error(err));
}

function renderMath(source) {
  const mainContent = typstDocument(source);
  const svg = renderQueue.then(() => $typst.svg({ mainContent }));
  renderQueue = svg.catch(() => {});
  return svg.then(svg => {
    if (typeof svg !== 'string' || !svg.includes('<svg')) {
      throw new Error('typst rendering failed');
    }
    return svg.replaceAll(TYPST_FILL, 'currentColor');
  });
}

// Shows a result, typeset if `rendered` (`text` is then Typst source), copied in Formalith syntax (`plain`) when
// clicked
function printResult(text, plain, rendered) {
  record({ kind: 'result', text, plain, rendered });
  const result = show(text, 'result');
  copyOnClick(result, plain);
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

// Replaces the text of the input line `element` by `typst` typeset, keeping the raw text if rendering fails
function renderInput(element, typst) {
  if (!initTypst()) {
    return;
  }
  renderMath(typst).then(
    svg => {
      const math = document.createElement('span');
      math.className = 'math';
      math.innerHTML = svg;
      element.lastChild.replaceWith(math);
      scrollToPrompt();
    },
    err => console.error(err),
  );
}

// Evaluation worker

let worker;
let pending = null;
// The completion asked to the worker, `{ id, line, pos }`, until it answers
let completing = null;
let nextId = 0;
// Lines which changed the session, replayed in a new worker (also after a reload)
let replayLog = load(REPLAY_KEY);

function startWorker() {
  worker = new Worker('worker.js', { type: 'module' });
  worker.onmessage = ({ data }) => {
    if (data.ready) {
      prefetchTypst();
      runQueued();
      return;
    }
    if (data.completion) {
      if (completing && data.id === completing.id) {
        applyCompletion(data.completion);
      }
      return;
    }
    if (data.id === -1 && data.set) {
      // A replayed line, which may have changed the set
      set = data.set;
      label.textContent = `${set}>`;
    }
    if (!pending || data.id !== pending.id) {
      return;
    }
    const { line, element, entry } = pending;
    finish();
    if (data.panic !== undefined) {
      // The wasm instance aborted on a panic and can't be reused
      print(`error: this operation is not supported in ${set}`, 'error');
      restartWorker();
    } else {
      if (data.replay) {
        replayLog.push(line);
        store(REPLAY_KEY, replayLog);
      }
      set = data.set;
      label.textContent = `${set}>`;
      if (data.input) {
        // Typeset before the result, renders being queued
        entry.typst = data.input;
        store(TRANSCRIPT_KEY, transcript);
        renderInput(element, data.input);
      }
      if (data.kind === 'result' || data.kind === 'typst') {
        printResult(data.text, data.plain, data.kind === 'typst');
      } else if (data.kind === 'message') {
        print(data.text);
        if (line === 'help' || line === ':help') {
          print(
            '  clear         clear the screen (also Ctrl+L)\nTab completes names, Ctrl+C interrupts a running computation.',
          );
        }
      } else if (data.kind === 'error') {
        print(`error: ${data.text}`, 'error');
      }
    }
    scrollToPrompt();
    runQueued();
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

// Runs the lines which changed the session again in a new worker
function replay() {
  // Answers to these messages don't match a pending request, only their set is used
  for (const line of replayLog) {
    worker.postMessage({ id: -1, line });
  }
}

function restartWorker() {
  completing = null;
  worker.terminate();
  startWorker();
  replay();
}

// Asks the worker for the completions of the word before the cursor, unless it is evaluating
function requestCompletion() {
  if (pending || completing || input.selectionStart !== input.selectionEnd) {
    return;
  }
  completing = { id: nextId++, line: input.value, pos: input.selectionStart };
  worker.postMessage({ id: completing.id, line: completing.line, complete: completing.pos });
}

// Replaces the word before the cursor by the longest common prefix of the candidates, listing them when it adds
// nothing, unless the input changed meanwhile
function applyCompletion({ start, candidates }) {
  const { line, pos } = completing;
  completing = null;
  if (input.value !== line || input.selectionStart !== pos || input.selectionEnd !== pos || !candidates.length) {
    return;
  }
  let prefix = candidates[0];
  for (const candidate of candidates) {
    while (!candidate.toLowerCase().startsWith(prefix.toLowerCase())) {
      prefix = prefix.slice(0, -1);
    }
  }
  if (prefix.length > pos - start || candidates.length === 1) {
    input.value = line.slice(0, start) + prefix + line.slice(pos);
    const cursor = start + prefix.length;
    input.setSelectionRange(cursor, cursor);
  } else {
    show(candidates.join('  '), 'info');
    scrollToPrompt();
  }
}

function finish() {
  pending = null;
  busy.hidden = true;
}

// Sends `line` to the worker, remembered in `pending` with its echoed element until it answers
function run(line) {
  const { element, entry } = echo(line);
  pending = { id: nextId++, line, element, entry };
  busy.hidden = false;
  worker.postMessage({ id: pending.id, line });
}

// Lines of the `run` query parameter (separated by newlines), like the examples of the documentation, run once
// the worker is ready, one after the other
const queued = (new URLSearchParams(location.search).get('run') ?? '')
  .split('\n')
  .map(line => line.trim())
  .filter(Boolean);
if (queued.length) {
  window.history.replaceState(null, '', location.pathname);
}

function runQueued() {
  if (!pending && queued.length) {
    run(queued.shift());
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
    clearLog();
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
  if (event.key === 'Tab' && !event.shiftKey && !event.ctrlKey && !event.altKey && !event.metaKey) {
    event.preventDefault();
    requestCompletion();
  } else if (event.key === 'ArrowUp' || event.key === 'ArrowDown') {
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
    clearLog();
  } else if (event.ctrlKey && event.key === 'c' && input.selectionStart === input.selectionEnd) {
    event.preventDefault();
    if (pending) {
      finish();
      print('interrupted', 'error');
      restartWorker();
    } else {
      echo(input.value, true);
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
replay();

// The transcript of the previous visits
restoring = true;
for (const entry of transcript) {
  if (entry.kind === 'line') {
    echo(entry.text, entry.interrupted, entry.set, entry.typst);
  } else if (entry.kind === 'result') {
    printResult(entry.text, entry.plain, entry.rendered);
  } else {
    print(entry.text, entry.kind);
  }
}
restoring = false;
if (!transcript.length) {
  show('Formalith — type `help` for the list of commands.', 'info');
}
scrollToPrompt();
