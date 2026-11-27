//! Printing trait and options to render expressions.

use std::fmt::{Debug, Display};

use owo_colors::{
    Color, OwoColorize,
    colors::{BrightBlack, Yellow},
};

use crate::{
    context::{Context, Symbol},
    field::Set,
    term::Term,
};

/// Rendering options are stored here. It can be created from some presets or completly custom.
#[derive(Clone, Copy, Debug)]
pub struct PrintOptions {
    /// Set color rendering. Enabled by default if stdout support colors.
    pub colors: bool,
    /// Set rendering to typst format. Disabled by default.
    pub typst: bool,
    /// Fancier printing using ASCII art.
    pub pretty_print: bool,
    /// The maximum width of the lines of pretty printing, wider results being cut into stacked chunks
    /// ([`PrettyPrinter::wrap`]), like the width of a terminal. Unlimited by default.
    pub width: Option<usize>,
}

impl Default for PrintOptions {
    fn default() -> Self {
        Self {
            colors: supports_color::on_cached(supports_color::Stream::Stdout).is_some(),
            typst: false,
            pretty_print: true,
            width: None,
        }
    }
}

impl PrintOptions {
    /// Print
    fn stdout() -> Self {
        Self {
            colors: supports_color::on_cached(supports_color::Stream::Stdout).is_some(),
            typst: false,
            pretty_print: false,
            width: None,
        }
    }
    /// Single line, without colors.
    #[must_use]
    pub const fn plain() -> Self {
        Self {
            colors: false,
            typst: false,
            pretty_print: false,
            width: None,
        }
    }
    /// Single-line typst math source, without colors.
    #[must_use]
    pub const fn typst() -> Self {
        Self {
            colors: false,
            typst: true,
            pretty_print: false,
            width: None,
        }
    }
    /// The same options with lines of pretty printing at most `width` wide (unlimited for `None`).
    #[must_use]
    pub const fn with_width(self, width: Option<usize>) -> Self {
        Self { width, ..self }
    }
    /// Check if colors should be written.
    const fn use_colors(self) -> bool {
        self.colors && !self.typst
    }
}

/// Structs containing printing options used to format output.
#[derive(Debug)]
pub struct Printer<'a, T> {
    content: &'a T,
    options: PrintOptions,
}

impl<'a, T> Printer<'a, T> {
    /// Create a new Printer
    pub const fn new(content: &'a T, options: PrintOptions) -> Self {
        Self { content, options }
    }
}

impl<T: PrettyPrint> Display for Printer<'_, T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        PrettyPrint::fmt(self.content, &self.options, f)
    }
}

/// Elements and expressions which can be printed using options.
pub trait Print {
    /// Create a new printer for self with specific options.
    fn with_options(&self, options: PrintOptions) -> Printer<'_, Self>
    where
        Self: Sized,
    {
        Printer::new(self, options)
    }
    /// Create a new printer for self with default options for printing on the stdout.
    fn stdout(&self) -> Printer<'_, Self>
    where
        Self: Sized,
    {
        self.with_options(PrintOptions::stdout())
    }
    /// Create a new printer for self rendering typst math source.
    fn typst(&self) -> Printer<'_, Self>
    where
        Self: Sized,
    {
        self.with_options(PrintOptions::typst())
    }
    /// Format `self` using given options.
    ///
    /// # Errors
    /// Returns an error if the formatter fails.
    fn print(&self, options: &PrintOptions, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result;

    /// Apply delimiter color depending on options.
    ///
    /// # Errors
    /// Returns an error if the formatter fails.
    fn delimiter(
        text: &str,
        options: &PrintOptions,
        f: &mut std::fmt::Formatter<'_>,
    ) -> std::fmt::Result
    where
        Self: Sized,
    {
        Self::fg::<BrightBlack>(text, options, f)
    }

    /// Add paren to the expr if needed.
    ///
    /// # Errors
    /// Returns an error if the formatter fails.
    fn group<T: Set>(
        elem: &Term<T>,
        options: &PrintOptions,
        f: &mut std::fmt::Formatter<'_>,
    ) -> std::fmt::Result
    where
        Self: Sized,
    {
        let need_paren = match elem {
            // Typst reads `-2^x` as `-(2^x)`
            Term::Value(value) => {
                !value.set.is_atomic(&value.value)
                    || (options.typst && value.typst().to_string().starts_with('-'))
            }
            Term::Symbol(_) | Term::Fun(_) => false,
            Term::Add(_) | Term::Pow(_) | Term::Mul(_) => true,
        };
        if need_paren {
            Self::group_delim("(", options, f)?;
        }
        elem.print_operand(*options, f)?;
        if need_paren {
            Self::group_delim(")", options, f)?;
        }
        Ok(())
    }

    /// Apply group delimiter color depending on options.
    ///
    /// # Errors
    /// Returns an error if the formatter fails.
    fn group_delim(
        text: &str,
        options: &PrintOptions,
        f: &mut std::fmt::Formatter<'_>,
    ) -> std::fmt::Result
    where
        Self: Sized,
    {
        if options.use_colors() {
            write!(f, "{}", text.white().dimmed())?;
        } else {
            write!(f, "{text}")?;
        }
        Ok(())
    }

    /// Apply operator color depending on options.
    ///
    /// # Errors
    /// Returns an error if the formatter fails.
    fn operator(
        text: &str,
        options: &PrintOptions,
        f: &mut std::fmt::Formatter<'_>,
    ) -> std::fmt::Result
    where
        Self: Sized,
    {
        Self::fg::<Yellow>(text, options, f)
    }

    /// Write a multiplication sign: `*` normally, a space (implicit product) in typst.
    ///
    /// # Errors
    /// Returns an error if the formatter fails.
    fn mul_sign(options: &PrintOptions, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result
    where
        Self: Sized,
    {
        if options.typst {
            f.write_str(" ")
        } else {
            Self::operator("*", options, f)
        }
    }

    /// Apply a compile-time color depending on options.
    ///
    /// # Errors
    /// Returns an error if the formatter fails.
    fn fg<C: Color>(
        text: &str,
        options: &PrintOptions,
        f: &mut std::fmt::Formatter<'_>,
    ) -> std::fmt::Result
    where
        Self: Sized,
    {
        if options.use_colors() {
            write!(f, "{}", text.fg::<C>())?;
        } else {
            write!(f, "{text}")?;
        }
        Ok(())
    }
}
/// Elements and expressions which can be pretty printed using options.
pub trait PrettyPrint: Print {
    /// Format `self` using given options, selecting or not pretty printing.
    ///
    /// # Errors
    /// Returns an error if the formatter fails.
    fn fmt(&self, options: &PrintOptions, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if options.pretty_print && !options.typst {
            write!(f, "{}", self.pretty_print(options).wrapped(options.width))
        } else {
            self.print(options, f)
        }
    }
    /// Format `self` using given options, with pretty printing.
    #[must_use]
    fn pretty_print(&self, options: &PrintOptions) -> PrettyPrinter;
}

/// Utility struct implementing various ascii art printing methods.
#[derive(Debug, Clone)]
pub struct PrettyPrinter {
    /// Vector of multiple lines, allowing to easily add content at the top, left, etc...
    pub lines: Vec<String>,
    width: usize,
    /// Give the height of the base of the expression.
    pub baseline: usize,
    /// The columns where the printer may be cut when it is too wide, see [`PrettyPrinter::wrap`].
    breaks: Vec<Break>,
}

/// Where a line which is too wide is preferably cut, from the best place to the worst one.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum BreakKind {
    /// After a separator between items, like the `, ` between the equations of a solution.
    Separator,
    /// Before a relation, like `=` or `<`.
    Relation,
    /// Before the `+` or `-` of a sum.
    Sum,
    /// Before the `⋅` of a product.
    Product,
}

/// A column where a pretty printer may be cut, the next chunk starting there.
#[derive(Debug, Clone, Copy)]
struct Break {
    column: usize,
    kind: BreakKind,
    /// The number of parentheses or other constructs around it, cutting at the outermost level first.
    depth: u8,
}

impl From<String> for PrettyPrinter {
    fn from(value: String) -> Self {
        Self {
            width: value.chars().count(),
            lines: vec![value],
            baseline: 0,
            breaks: vec![],
        }
    }
}

const fn get_drawings_chars(sym: char) -> Option<(char, char, char)> {
    match sym {
        '(' => Some(('⎛', '⎜', '⎝')),
        ')' => Some(('⎞', '⎟', '⎠')),
        '[' => Some(('⎡', '⎢', '⎣')),
        ']' => Some(('⎤', '⎥', '⎦')),
        '|' => Some(('│', '│', '│')),
        '⌊' => Some(('⎢', '⎢', '⎣')),
        '⌋' => Some(('⎥', '⎥', '⎦')),
        '⌈' => Some(('⎡', '⎢', '⎢')),
        '⌉' => Some(('⎤', '⎥', '⎥')),
        _ => None,
    }
}

/// Greek letters, by the names that pretty printing writes as letters.
#[rustfmt::skip]
const GREEK: [(&str, &str); 34] = [
    ("alpha", "α"), ("beta", "β"), ("gamma", "γ"), ("delta", "δ"), ("epsilon", "ε"),
    ("zeta", "ζ"), ("eta", "η"), ("theta", "θ"), ("iota", "ι"), ("kappa", "κ"),
    ("lambda", "λ"), ("mu", "μ"), ("nu", "ν"), ("xi", "ξ"), ("omicron", "ο"), ("rho", "ρ"),
    ("sigma", "σ"), ("tau", "τ"), ("upsilon", "υ"), ("phi", "φ"), ("chi", "χ"), ("psi", "ψ"),
    ("omega", "ω"), ("Gamma", "Γ"), ("Delta", "Δ"), ("Theta", "Θ"), ("Lambda", "Λ"),
    ("Xi", "Ξ"), ("Pi", "Π"), ("Sigma", "Σ"), ("Phi", "Φ"), ("Psi", "Ψ"), ("Omega", "Ω"),
    ("Upsilon", "Υ"),
];

/// The name of a symbol or function as pretty printed: a Greek letter for its name, like `α` for `alpha`, also before
/// a subscript (`α_1` for `alpha_1`).
#[must_use]
pub fn pretty_name(name: &str) -> std::borrow::Cow<'_, str> {
    let (letter, rest) = name.find('_').map_or((name, ""), |i| name.split_at(i));
    GREEK
        .iter()
        .find(|(greek, _)| *greek == letter)
        .map_or(std::borrow::Cow::Borrowed(name), |(_, glyph)| {
            std::borrow::Cow::Owned(format!("{glyph}{rest}"))
        })
}

/// Whether `name` is written as is in Typst math: a single character or the name of a Typst symbol.
fn is_typst_identifier(name: &str) -> bool {
    name.chars().count() == 1
        || matches!(name, "pi" | "oo")
        || GREEK.iter().any(|(greek, _)| *greek == name)
}

/// The name of a symbol in Typst math, where a multi-letter identifier is a variable: quoted as text unless it is a
/// single letter or a Greek letter, like `"abc"`, also in a subscript (`x_("ab")`, `t_12`).
#[must_use]
pub fn typst_name(name: &str) -> std::borrow::Cow<'_, str> {
    let (base, subscript) = name
        .split_once('_')
        .map_or((name, None), |(base, rest)| (base, Some(rest)));
    let base_ok = is_typst_identifier(base);
    let subscript_ok = subscript.is_none_or(|rest| {
        is_typst_identifier(rest) || (!rest.is_empty() && rest.chars().all(|c| c.is_ascii_digit()))
    });
    if base_ok && subscript_ok {
        return std::borrow::Cow::Borrowed(name);
    }
    let mut res = if base_ok {
        base.to_owned()
    } else {
        format!("\"{base}\"")
    };
    if let Some(rest) = subscript {
        if subscript_ok {
            res.push('_');
            res.push_str(rest);
        } else {
            res.push_str("_(");
            res.push_str(&typst_name(rest));
            res.push(')');
        }
    }
    std::borrow::Cow::Owned(res)
}

/// The name of the function `ident` (printed `name`) in Typst math, written before its arguments in parentheses:
/// a Typst function or operator like `arctan`, `binom` or `root` (which takes the index first), the name itself for a
/// single letter, `op("name")` otherwise.
pub(crate) fn typst_function_name(ident: Symbol, name: &str) -> std::borrow::Cow<'_, str> {
    std::borrow::Cow::Borrowed(match ident {
        Context::CONJ => "overline",
        Context::RE => "Re",
        Context::IM => "Im",
        Context::ROOT => "root",
        Context::BINOMIAL => "binom",
        Context::GAMMA => "Gamma",
        Context::LAMBERTW => "W",
        Context::BETA => "Beta",
        Context::ZETA => "zeta",
        Context::ASIN => "arcsin",
        Context::ACOS => "arccos",
        Context::ATAN => "arctan",
        Context::TRACE => "tr",
        Context::KERNEL => "ker",
        Context::ABS
        | Context::ARG
        | Context::DET
        | Context::SQRT
        | Context::FLOOR
        | Context::CEIL
        | Context::MIN
        | Context::MAX
        | Context::GCD
        | Context::LCM
        | Context::EXP
        | Context::LN
        | Context::SIN
        | Context::COS
        | Context::TAN
        | Context::SINH
        | Context::COSH
        | Context::TANH => name,
        _ if name.chars().count() == 1 => name,
        _ => return std::borrow::Cow::Owned(format!("op(\"{name}\")")),
    })
}

impl PrettyPrinter {
    /// Create a new blank pretty printer.
    #[must_use]
    pub const fn empty() -> Self {
        Self {
            lines: vec![],
            width: 0,
            baseline: 0,
            breaks: vec![],
        }
    }
    /// Check if the pretty printer is blank.
    #[must_use]
    pub const fn is_empty(&self) -> bool {
        self.width == 0
    }

    /// Center horizontally and vertically the printer to be exactly of size (`height`*`width`)
    /// Return the final height of the printer (Can be bigger than the expected height, because of baseline alignement)
    ///
    /// # Panics
    /// Panics if height or width is smaller than printer's size.
    pub fn center(&mut self, height: usize, width: usize, baseline: usize) -> usize {
        assert!(
            !(height < self.height() || width < self.width()),
            "Can't center self on a smaller size !"
        );
        assert!(
            baseline <= height,
            "Can't have a baseline greater than the height !"
        );
        // Center vertically, aligning baseline.
        let base_offset = baseline - self.baseline;
        for _ in 0..base_offset {
            self.lines.insert(0, " ".repeat(self.width()));
        }

        if height > self.height() {
            let end_offset = height - self.height();
            for _ in 0..end_offset {
                self.lines.push(" ".repeat(self.width()));
            }
        }

        // Center horizontally
        let diff = width - self.width();
        let offset = diff / 2;
        let end_offset = diff - offset;
        for line in &mut self.lines {
            line.insert_str(0, &" ".repeat(offset));
            line.push_str(&" ".repeat(end_offset));
        }

        self.width = width;
        self.breaks.clear();
        self.height()
    }

    /// Concat two pretty printer, aligning their baseline and adding sym between them. `space` can be used to specify if spaces are needed around `sym`.
    ///
    /// self + other
    pub fn concat(&mut self, sym: &str, space: bool, other: &Self) {
        self.concat_with(sym, space, other, None);
    }

    /// Concat two pretty printers like [`PrettyPrinter::concat`], allowing to cut the result at `sym` when it is
    /// too wide: after it for a [`BreakKind::Separator`], before it otherwise.
    pub fn concat_breaking(&mut self, sym: &str, space: bool, other: &Self, kind: BreakKind) {
        self.concat_with(sym, space, other, Some(kind));
    }

    fn concat_with(&mut self, sym: &str, spaced: bool, other: &Self, kind: Option<BreakKind>) {
        if self.is_empty() {
            *self = other.clone();
            return;
        }

        // Baselines should be aligned
        let other_offset = if self.baseline < other.baseline {
            for _ in 0..other.baseline - self.baseline {
                self.lines.insert(0, " ".repeat(self.width));
            }
            self.baseline = other.baseline;
            0
        } else {
            self.baseline - other.baseline
        };
        if self.height() < other.height() + other_offset {
            // Add blank lines
            for _ in 0..other.height() + other_offset - self.height() {
                self.lines.push(" ".repeat(self.width()));
            }
        }

        // Add space and the symbol
        let (sym, space) = if spaced {
            (format!(" {sym} "), " ".repeat(sym.chars().count() + 2))
        } else {
            (sym.to_string(), " ".repeat(sym.chars().count()))
        };
        for i in 0..self.height() {
            if i == self.baseline {
                self.lines[i] += &sym;
            } else {
                self.lines[i] += &space;
            }
        }

        // Concat the other printer
        for i in 0..self.height() {
            if i >= other_offset && i - other_offset < other.height() {
                self.lines[i] += &other.lines[i - other_offset];
            } else {
                self.lines[i] += &" ".repeat(other.width());
            }
        }

        // Update printer infos
        let offset = self.width + space.len();
        if let Some(kind) = kind {
            let column = if kind == BreakKind::Separator {
                offset
            } else {
                self.width + usize::from(spaced)
            };
            self.breaks.push(Break {
                column,
                kind,
                depth: 0,
            });
        }
        self.breaks.extend(other.breaks.iter().map(|other| Break {
            column: other.column + offset,
            ..*other
        }));
        self.width += other.width + space.len();
    }

    /// Concat two pretty printer vertically, centering them.
    ///
    /// self
    /// -----
    /// other
    pub fn vertical_concat(&mut self, sym: &str, other: &Self) {
        if self.is_empty() {
            *self = other.clone();
            return;
        }

        // Center the smallest
        let diff = self.width().abs_diff(other.width());
        let offset = diff / 2;
        let offset_end = diff - offset;
        let (other_offset, other_offset_end) = if self.width() < other.width() {
            for i in &mut self.lines {
                i.insert_str(0, &" ".repeat(offset));
            }
            for i in &mut self.lines {
                *i += &" ".repeat(offset_end);
            }
            self.width += diff;
            (0, 0)
        } else {
            (offset, offset_end)
        };

        // Add the symbol
        self.breaks.clear();
        self.baseline = self.height();
        self.lines.push(sym.repeat(self.width()));

        // Concat the other printer
        for line in &other.lines {
            let mut line = line.clone();
            line.insert_str(0, &" ".repeat(other_offset));
            line += &" ".repeat(other_offset_end);
            self.lines.push(line);
        }
    }
    /// Put `other` below `self`, aligned on the left. The baseline stays the one of `self`.
    ///
    /// self
    /// other
    pub fn stack(&mut self, other: &Self) {
        if self.is_empty() {
            *self = other.clone();
            return;
        }
        let width = self.width().max(other.width());
        self.breaks.clear();
        for line in &mut self.lines {
            *line += &" ".repeat(width - self.width);
        }
        for line in &other.lines {
            self.lines
                .push(line.clone() + &" ".repeat(width - other.width));
        }
        self.width = width;
    }
    /// Put other as an exponant of self.
    ///
    /// ```no_test
    ///     other
    /// self
    /// ```
    pub fn pow(&mut self, other: &Self) {
        // Add space to concat other
        self.baseline += other.height();
        for _ in 0..other.height() {
            self.lines.insert(0, " ".repeat(self.width()));
        }
        for i in 0..self.height() {
            if i < other.height() {
                self.lines[i].push_str(&other.lines[i]);
            } else {
                self.lines[i].push_str(&" ".repeat(other.width()));
            }
        }
        self.width += other.width;
    }
    /// Put self under a radical sign, with an optional `index` (`None` for a square root).
    ///
    /// ```no_test
    ///       ___
    ///      ╱ a                 _____
    ///    n╱  ─      n _____   ∛x + 1
    ///   ╲╱   b       √x + 1
    /// ```
    pub fn root(&mut self, index: Option<&Self>) {
        let height = self.height();
        let sign = match index.map(|index| index.lines.as_slice()) {
            _ if height > 1 => None,
            Some([index]) if index == "3" => Some('∛'),
            Some([index]) if index == "4" => Some('∜'),
            _ => Some('√'),
        };
        let index = index.filter(|_| !matches!(sign, Some('∛' | '∜')));
        // A diagonal sign is one column wider than the radicand's height, plus a space before the radicand
        let sign_width = if height == 1 { 1 } else { height + 2 };
        let mut lines = Vec::with_capacity(height + 1);
        // The overline starts at the top of the sign, covering the space before the radicand
        let overline_start = if height == 1 { 1 } else { height + 1 };
        lines.push(
            " ".repeat(overline_start) + &"_".repeat(self.width() + sign_width - overline_start),
        );
        for (i, line) in self.lines.iter().enumerate() {
            #[allow(clippy::option_if_let_else)]
            let prefix = if let Some(sign) = sign {
                sign.to_string()
            } else if i == height - 1 {
                "╲╱".to_string() + &" ".repeat(height)
            } else {
                " ".repeat(height - i) + "╱" + &" ".repeat(i + 1)
            };
            lines.push(prefix + line);
        }
        self.lines = lines;
        self.width += sign_width;
        self.baseline += 1;
        self.shift_breaks(sign_width);
        self.nest();

        let Some(index) = index else {
            return;
        };
        // The index ends on the line above the bottom of the sign, where the free space at the
        // left of the sign is the smallest, it only grows on the lines above.
        let (bottom, free) = if height == 1 { (0, 0) } else { (height - 1, 2) };
        let extra = index.width().saturating_sub(free);
        for line in &mut self.lines {
            line.insert_str(0, &" ".repeat(extra));
        }
        self.width += extra;
        self.shift_breaks(extra);
        let missing = (index.height() - 1).saturating_sub(bottom);
        for _ in 0..missing {
            self.lines.insert(0, " ".repeat(self.width));
        }
        self.baseline += missing;
        let bottom = bottom + missing;
        let end = free + extra;
        for (i, index_line) in index.lines.iter().enumerate() {
            let line = &mut self.lines[bottom + 1 + i - index.height()];
            let mut chars: Vec<char> = line.chars().collect();
            chars.splice(end - index.width()..end, index_line.chars());
            *line = chars.into_iter().collect();
        }
    }
    /// Put self (the integrand followed by `dx`) after an integral sign, with optional
    /// `(lower, upper)` bounds below and above the sign.
    ///
    /// ```no_test
    /// 1
    /// ⌠
    /// ⎮ f(x) dx
    /// ⌡
    /// 0
    /// ```
    pub fn integral(&mut self, bounds: Option<(&Self, &Self)>) {
        let height = self.height();
        let mut sign_lines = Vec::with_capacity(height + 2);
        sign_lines.push("⌠".to_string());
        sign_lines.extend(std::iter::repeat_n("⎮".to_string(), height));
        sign_lines.push("⌡".to_string());
        let sign = Self {
            lines: sign_lines,
            width: 1,
            baseline: 0,
            breaks: vec![],
        };
        let (mut column, upper_height) = match bounds {
            Some((lower, upper)) => {
                let mut column = upper.clone();
                column.stack(&sign);
                column.stack(lower);
                (column, upper.height())
            }
            None => (sign, 0),
        };
        // The body starts on the line below `⌠`
        self.nest();
        column.baseline = upper_height + 1 + self.baseline;
        column.concat(" ", false, self);
        *self = column;
    }
    /// Put self after a big operator `sign`, like `∑` or `lim`, with its `lower` part and an optional `upper` one.
    ///
    /// ```text
    ///   n
    ///   ∑  f(k)    lim  f(x)
    /// k=1         x → 0
    /// ```
    pub fn big_operator(&mut self, sign: &str, lower: &Self, upper: Option<&Self>) {
        let mut column = upper.cloned().unwrap_or_else(Self::empty);
        column.over(&Self::from(sign.to_string()));
        column.over(lower);
        column.baseline = upper.map_or(0, Self::height);
        self.nest();
        column.concat(" ", false, self);
        *self = column;
    }
    /// Put `lower` below `self`, both centered horizontally, keeping the baseline of `self`, like the parts of a
    /// binomial coefficient.
    pub fn over(&mut self, lower: &Self) {
        if self.is_empty() {
            *self = lower.clone();
            return;
        }
        let width = self.width().max(lower.width());
        let center = |part: &Self| {
            let mut part = part.clone();
            let (height, baseline) = (part.height(), part.baseline);
            part.center(height, width, baseline);
            part
        };
        let baseline = self.baseline;
        *self = center(self);
        self.stack(&center(lower));
        self.baseline = baseline;
    }
    /// Lay out the cases of a piecewise function, one per line, like `{$cases(v_1 & "if" c_1, d & "otherwise")$}`:
    /// each value followed by `if` and its condition, or by `otherwise` without one, values aligned on the left,
    /// after a brace.
    ///
    /// ```text
    /// ⎧ -x  if x < 0
    /// ⎨ x²  if x < 1
    /// ⎩ 1   otherwise
    /// ```
    #[must_use]
    pub fn cases(rows: Vec<(Self, Option<Self>)>) -> Self {
        let width = rows
            .iter()
            .map(|(value, _)| value.width())
            .max()
            .unwrap_or(0);
        let mut res = Self::empty();
        for (mut value, condition) in rows {
            let padding = width - value.width();
            for line in &mut value.lines {
                line.push_str(&" ".repeat(padding));
            }
            value.width = width;
            match condition {
                Some(condition) => {
                    value.concat("  if ", false, &condition);
                }
                None => value.concat("  otherwise", false, &Self::empty()),
            }
            res.stack(&value);
        }
        res.baseline = res.height().saturating_sub(1) / 2;
        let height = res.height();
        for (i, line) in res.lines.iter_mut().enumerate() {
            let brace = match (height, i) {
                (1, _) => '{',
                (_, 0) => '⎧',
                (_, i) if i == height - 1 => '⎩',
                (_, i) if i == (height - 1) / 2 => '⎨',
                _ => '⎪',
            };
            line.insert_str(0, &format!("{brace} "));
        }
        res.width += 2;
        res.breaks.clear();
        res
    }
    /// Add `sym` at the left of self, converting it to unicode drawings chars.
    pub fn left(&mut self, sym: char) {
        let or = (sym, sym, sym);
        let height = self.height();
        let drawings = if height == 1 {
            // If height is 1, use directly sym, not a drawing variant
            or
        } else {
            get_drawings_chars(sym).unwrap_or(or)
        };
        for (i, line) in self.lines.iter_mut().enumerate() {
            line.insert(
                0,
                if i == 0 {
                    drawings.0
                } else if i == height - 1 {
                    drawings.2
                } else {
                    drawings.1
                },
            );
        }
        self.width += 1;
        self.shift_breaks(1);
    }
    /// Add `sym` at the right of self, converting it to unicode drawings chars.
    pub fn right(&mut self, sym: char) {
        let or = (sym, sym, sym);
        let height = self.height();
        let drawings = if height == 1 {
            // If height is 1, use directly sym, not a drawing variant
            or
        } else {
            get_drawings_chars(sym).unwrap_or(or)
        };
        for (i, line) in self.lines.iter_mut().enumerate() {
            line.push(if i == 0 {
                drawings.0
            } else if i == height - 1 {
                drawings.2
            } else {
                drawings.1
            });
        }
        self.width += 1;
    }
    /// Wrap self between `start` and `end` symbol.
    pub fn group(&mut self, start: char, end: char) {
        self.left(start);
        self.right(end);
        self.nest();
    }
    /// Move the breaks of self `columns` to the right, after adding columns at its left.
    fn shift_breaks(&mut self, columns: usize) {
        for cut in &mut self.breaks {
            cut.column += columns;
        }
    }
    /// Make the breaks of self one level deeper, to be cut after the ones outside of it.
    fn nest(&mut self) {
        for cut in &mut self.breaks {
            cut.depth = cut.depth.saturating_add(1);
        }
    }
    /// Self wrapped at `width` (see [`PrettyPrinter::wrap`]), or unchanged for `None`.
    #[must_use]
    pub fn wrapped(self, width: Option<usize>) -> Self {
        match width {
            Some(width) if self.width > width => self.wrap(width),
            _ => self,
        }
    }
    /// Cut self into chunks at most `width` wide, stacked: at its breaks (outermost ones first, the best kind
    /// first, preferably in the right half of the line so that chunks aren't too short, and only when the next
    /// chunk can end at a break too), or at `width` when there is none. Each chunk is the slice of every line, without its blank rows and columns at the edges, so a chunk
    /// of a single line takes a single line; chunks taller than a line are separated by an empty line.
    #[must_use]
    pub fn wrap(&self, width: usize) -> Self {
        let width = width.max(1);
        if self.width <= width {
            return self.clone();
        }
        let rows: Vec<Vec<char>> = self
            .lines
            .iter()
            .map(|line| line.chars().collect())
            .collect();
        let blank_column = |column: usize| {
            rows.iter()
                .all(|row| row.get(column).is_none_or(|c| *c == ' '))
        };
        // Cutting at `column` is useless when the next chunk must be cut at a width anyway
        let useful = |column: usize| {
            self.width - column <= width
                || self
                    .breaks
                    .iter()
                    .any(|cut| cut.column > column && cut.column <= column + width)
        };
        let mut chunks = vec![];
        let mut start = 0;
        while self.width - start > width {
            let end = start + width;
            let best = |from: usize| {
                self.breaks
                    .iter()
                    .filter(|cut| cut.column > from.max(start) && cut.column <= end)
                    .filter(|cut| useful(cut.column))
                    .min_by_key(|cut| (cut.depth, cut.kind, std::cmp::Reverse(cut.column)))
            };
            let cut = best(start + width / 2)
                .or_else(|| best(start))
                .map_or(end, |cut| cut.column);
            chunks.push((start, cut));
            start = cut;
        }
        chunks.push((start, self.width));
        let mut res = Self::empty();
        let mut previous_height = 0;
        for (mut start, mut end) in chunks {
            while start < end && blank_column(start) {
                start += 1;
            }
            while end > start && blank_column(end - 1) {
                end -= 1;
            }
            if start == end {
                continue;
            }
            let mut lines: Vec<String> = rows
                .iter()
                .map(|row| {
                    (start..end)
                        .map(|column| row.get(column).copied().unwrap_or(' '))
                        .collect()
                })
                .collect();
            let blank = |line: &String| line.chars().all(|c| c == ' ');
            let top = lines.iter().take_while(|line| blank(line)).count();
            lines.drain(..top);
            while lines.last().is_some_and(blank) {
                lines.pop();
            }
            let chunk = Self {
                baseline: self.baseline.saturating_sub(top).min(lines.len() - 1),
                lines,
                width: end - start,
                breaks: vec![],
            };
            if !res.is_empty() && previous_height.max(chunk.height()) > 1 {
                res.stack(&Self::from(String::new()));
            }
            previous_height = chunk.height();
            res.stack(&chunk);
        }
        res
    }
    /// Wrap self between paren.
    pub fn paren(&mut self) {
        self.group('(', ')');
    }
    /// Return the width of the pretty printer.
    #[must_use]
    pub const fn width(&self) -> usize {
        self.width
    }
    /// Return the height of the pretty printer.
    #[must_use]
    pub const fn height(&self) -> usize {
        self.lines.len()
    }
}

impl Display for PrettyPrinter {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for (i, line) in self.lines.iter().enumerate() {
            write!(f, "{line}")?;
            if i != self.height() - 1 {
                writeln!(f)?;
            }
        }
        Ok(())
    }
}
