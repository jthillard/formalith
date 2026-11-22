// Documentation pages, written by `cargo run -p formalith-session --example builtin_docs`: filters the builtins
// and renders the results of examples (`data-typst`) as math with typst.ts, like the REPL
// (crates/formalith-web/www/main.js). Without it, results stay as text.

// Text color used by Typst, replaced by `currentColor` in the SVG so results follow the page theme.
const TYPST_FILL = '#010203';

// Filter

const filter = document.getElementById('filter');
const empty = document.getElementById('empty');

function applyFilter() {
  const words = filter.value.toLowerCase().split(/\s+/).filter(Boolean);
  let shown = 0;
  for (const category of document.querySelectorAll('.category')) {
    let categoryShown = 0;
    for (const builtin of category.querySelectorAll('.builtin')) {
      const name = builtin.id.toLowerCase();
      const visible = words.every(word => name.includes(word) || builtin.dataset.search.includes(word));
      builtin.hidden = !visible;
      categoryShown += visible;
    }
    category.hidden = categoryShown === 0;
    shown += categoryShown;
  }
  document.getElementById('usage').hidden = words.length > 0;
  empty.hidden = shown > 0;
  for (const link of document.querySelectorAll('aside ul ul a')) {
    const target = document.getElementById(link.getAttribute('href').slice(1));
    link.parentElement.hidden = target?.hidden ?? false;
  }
}

filter.addEventListener('input', applyFilter);

// Typst rendering

function initTypst() {
  if (!globalThis.$typst) {
    return false;
  }
  $typst.setCompilerInitOptions({
    getModule: () =>
      'https://cdn.jsdelivr.net/npm/@myriaddreamin/typst-ts-web-compiler@v0.7.0-rc1/pkg/typst_ts_web_compiler_bg.wasm',
  });
  $typst.setRendererInitOptions({
    getModule: () =>
      'https://cdn.jsdelivr.net/npm/@myriaddreamin/typst-ts-renderer@v0.7.0-rc1/pkg/typst_ts_renderer_bg.wasm',
  });
  return true;
}

function typstDocument(source, fontSize) {
  return (
    `#set page(width: auto, height: auto, margin: (x: 0pt, y: 0.2em));\n` +
    `#set text(size: ${fontSize}pt, fill: rgb("${TYPST_FILL}"));\n` +
    `$ ${source} $`
  );
}

// Renders every result in order, one at a time since the compiler can't be used concurrently.
async function renderResults() {
  if (!initTypst()) {
    return;
  }
  const fontSize = parseFloat(getComputedStyle(document.body).fontSize) * 1.2;
  for (const result of document.querySelectorAll('.result[data-typst]')) {
    try {
      const svg = await $typst.svg({ mainContent: typstDocument(result.dataset.typst, fontSize) });
      if (typeof svg === 'string' && svg.includes('<svg')) {
        result.innerHTML = svg.replaceAll(TYPST_FILL, 'currentColor');
        result.classList.add('rendered');
        result.title = result.dataset.typst;
      }
    } catch (err) {
      console.error(err);
    }
  }
}

// The typst.ts bundle is a module loaded before this one, which may still be initializing
if (globalThis.$typst) {
  renderResults();
} else {
  addEventListener('load', renderResults, { once: true });
}
