//! Writes the documentation pages of the website: the builtins, sets and commands, from
//! `formalith::context::docs` and the session.
//!
//! `cargo run -p formalith-session --example builtin_docs -- <out dir>` (`./dev docs`) writes `index.html` with
//! the stylesheet and the script of `docs/site/`.

use std::{fmt::Write as _, fs, path::PathBuf};

use formalith_session::{
    COMMANDS,
    formalith::{
        context::docs::{BuiltinDoc, Category, Example},
        dynamic::sets,
    },
};

/// `text` with the HTML special characters escaped.
fn escape(text: &str) -> String {
    let mut escaped = String::with_capacity(text.len());
    for c in text.chars() {
        match c {
            '&' => escaped.push_str("&amp;"),
            '<' => escaped.push_str("&lt;"),
            '>' => escaped.push_str("&gt;"),
            '"' => escaped.push_str("&quot;"),
            '\'' => escaped.push_str("&#39;"),
            c => escaped.push(c),
        }
    }
    escaped
}

/// `text` encoded as a URL query component.
fn encode_component(text: &str) -> String {
    let mut encoded = String::new();
    for byte in text.bytes() {
        if byte.is_ascii_alphanumeric() || b"-_.~".contains(&byte) {
            encoded.push(byte as char);
        } else {
            write!(encoded, "%{byte:02X}").unwrap();
        }
    }
    encoded
}

/// `text` with the parts between backquotes as code, escaped.
fn inline_code(text: &str) -> String {
    text.split('`')
        .enumerate()
        .map(|(i, part)| {
            if i % 2 == 1 {
                format!("<code>{}</code>", escape(part))
            } else {
                escape(part)
            }
        })
        .collect()
}

fn example(html: &mut String, example: &Example) {
    let lines = if example.set == "R" {
        example.input.to_owned()
    } else {
        format!(":set {}\n{}", example.set, example.input)
    };
    let set = if example.set == "R" {
        String::new()
    } else {
        format!(r#"<span class="set">in {}</span>"#, escape(example.set))
    };
    write!(
        html,
        r#"<li><a class="input" href="../repl/?run={}" title="Run in the REPL"><code>{}</code></a>{set}<span class="arrow">→</span><span class="result" data-typst="{result}">{result}</span></li>"#,
        encode_component(&lines),
        escape(example.input),
        result = escape(example.result),
    )
    .unwrap();
}

fn builtin(html: &mut String, doc: &BuiltinDoc) {
    let name = doc.name();
    write!(
        html,
        r##"<section class="builtin" id="{id}" data-search="{search}"><h3><a href="#{id}"><code>{signature}</code></a></h3><p>{summary}</p>"##,
        id = escape(name),
        search = escape(&format!("{name} {} {}", doc.summary, doc.details).to_lowercase()),
        signature = escape(doc.signature),
        summary = escape(doc.summary),
    )
    .unwrap();
    if !doc.details.is_empty() {
        write!(html, r#"<p class="details">{}</p>"#, escape(doc.details)).unwrap();
    }
    html.push_str(r#"<ul class="examples">"#);
    for item in doc.examples {
        example(html, item);
    }
    html.push_str("</ul></section>");
}

fn page() -> String {
    let mut nav = String::new();
    let mut content = String::new();
    for category in Category::ALL {
        let id = category.title().to_lowercase().replace(' ', "-");
        write!(nav, r##"<li><a href="#{id}">{}</a><ul>"##, category.title()).unwrap();
        write!(
            content,
            r#"<div class="category" id="{id}"><h2>{}</h2>"#,
            category.title()
        )
        .unwrap();
        for doc in category.builtins() {
            write!(
                nav,
                r##"<li><a href="#{name}"><code>{name}</code></a></li>"##,
                name = escape(doc.name())
            )
            .unwrap();
            builtin(&mut content, doc);
        }
        nav.push_str("</ul></li>");
        content.push_str("</div>");
    }

    let mut usage = String::from(r#"<table><tbody>"#);
    for (name, description) in sets() {
        write!(
            usage,
            "<tr><td><code>{}</code></td><td>{}</td></tr>",
            escape(&name),
            inline_code(description)
        )
        .unwrap();
    }
    usage.push_str(r#"</tbody></table><h3>Commands</h3><table><tbody>"#);
    for (command, description) in COMMANDS {
        write!(
            usage,
            "<tr><td><code>{}</code></td><td>{}</td></tr>",
            escape(command),
            escape(description)
        )
        .unwrap();
    }
    usage.push_str("</tbody></table>");

    format!(
        r##"<!doctype html>
<html lang="en">
<head>
  <meta charset="utf-8">
  <meta name="viewport" content="width=device-width, initial-scale=1">
  <title>Formalith documentation</title>
  <meta name="description" content="The builtin functions of the Formalith computer algebra system, with examples">
  <link rel="stylesheet" href="style.css">
  <!-- Typst compiler and renderer, used to render results as math -->
  <script type="module"
    src="https://cdn.jsdelivr.net/npm/@myriaddreamin/typst.ts@v0.7.0-rc1/dist/esm/contrib/all-in-one-lite.bundle.js"></script>
  <script type="module" src="docs.js"></script>
</head>
<body>
  <header>
    <a class="title" href="./">Formalith</a>
    <nav><a href="../repl/">REPL</a><a href="../gui/">Graphing calculator</a></nav>
  </header>
  <div class="layout">
    <aside>
      <input id="filter" type="search" placeholder="Filter builtins" aria-label="Filter builtins" spellcheck="false">
      <ul><li><a href="#usage">Usage</a></li>{nav}</ul>
    </aside>
    <main>
      <div id="usage">
        <h1>Formalith</h1>
        <p>Formalith is a computer algebra system. Enter an expression in the <a href="../repl/">REPL</a> to
        evaluate it, like <code>expand((x+1)^3)</code>, define variables and functions with <code>a := x^2</code>
        or <code>f(x, y) := x*y</code>, and solve systems with <code>x + y = 3, x - y = 1</code>. Products are
        written with <code>*</code>, or without it after a number (<code>2x</code>). Click an example to run
        it.</p>
        <h3>Sets</h3>
        <p>Expressions are evaluated in a set, <code>R</code> by default, chosen with <code>:set &lt;name&gt;</code>.</p>
        {usage}
      </div>
      {content}
      <p id="empty" hidden>No builtin matches.</p>
    </main>
  </div>
</body>
</html>
"##
    )
}

fn main() -> std::io::Result<()> {
    let out: PathBuf = std::env::args_os()
        .nth(1)
        .map_or_else(|| "target/docs-site".into(), PathBuf::from);
    fs::create_dir_all(&out)?;
    fs::write(out.join("index.html"), page())?;
    fs::write(
        out.join("style.css"),
        include_str!("../../../docs/site/style.css"),
    )?;
    fs::write(
        out.join("docs.js"),
        include_str!("../../../docs/site/docs.js"),
    )?;
    println!("documentation written to {}", out.display());
    Ok(())
}
