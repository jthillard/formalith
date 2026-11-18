//! Printing trait and options to render expressions.

use std::fmt::{Debug, Display};

use owo_colors::{
    Color, OwoColorize,
    colors::{BrightBlack, Yellow},
};

use crate::{field::Set, term::Term};

/// Rendering options are stored here. It can be created from some presets or completly custom.
#[derive(Debug)]
pub struct PrintOptions {
    /// Set color rendering. Enabled by default if stdout support colors.
    pub colors: bool,
    /// Set rendering to typst format. Disabled by default.
    pub typst: bool,
    /// Fancier printing using ASCII art.
    pub pretty_print: bool,
}

impl Default for PrintOptions {
    fn default() -> Self {
        Self {
            colors: supports_color::on_cached(supports_color::Stream::Stdout).is_some(),
            typst: false,
            pretty_print: true,
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
        }
    }
    /// Single-line typst math source, without colors.
    #[must_use]
    pub const fn typst() -> Self {
        Self {
            colors: false,
            typst: true,
            pretty_print: false,
        }
    }
    /// Check if colors should be written.
    const fn use_colors(&self) -> bool {
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
    /// Create e new printer for self with specific options.
    fn with_options(&self, options: PrintOptions) -> Printer<'_, Self>
    where
        Self: Sized,
    {
        Printer::new(self, options)
    }
    /// Create e new printer for self with default options for printing on the stdout.
    fn stdout(&self) -> Printer<'_, Self>
    where
        Self: Sized,
    {
        self.with_options(PrintOptions::stdout())
    }
    /// Create e new printer for self rendering typst math source.
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
        elem.print(options, f)?;
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
            write!(f, "{}", self.pretty_print(options))
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
}

impl From<String> for PrettyPrinter {
    fn from(value: String) -> Self {
        Self {
            width: value.chars().count(),
            lines: vec![value],
            baseline: 0,
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
        _ => None,
    }
}

impl PrettyPrinter {
    /// Create a new blank pretty printer.
    #[must_use]
    pub const fn empty() -> Self {
        Self {
            lines: vec![],
            width: 0,
            baseline: 0,
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
        self.height()
    }

    /// Concat two pretty printer, aligning their baseline and adding sym between them. `space` can be used to specify if spaces are needed around `sym`.
    ///
    /// self + other
    pub fn concat(&mut self, sym: &str, space: bool, other: &Self) {
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
        let (sym, space) = if space {
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
        self.baseline = self.height();
        self.lines.push(sym.repeat(self.width()));

        // Concat the other printer
        for i in 0..other.height() {
            let mut line = other.lines[i].clone();
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
        for line in &mut self.lines {
            *line += &" ".repeat(width - self.width);
        }
        for line in &other.lines {
            self.lines.push(line.clone() + &" ".repeat(width - other.width));
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
            None => Some('√'),
            Some([index]) if index == "3" => Some('∛'),
            Some([index]) if index == "4" => Some('∜'),
            Some(_) => Some('√'),
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
        column.baseline = upper_height + 1 + self.baseline;
        column.concat(" ", false, self);
        *self = column;
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
        for i in 0..height {
            self.lines[i].insert(
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
    }
    /// Add `sym` at the left of self, converting it to unicode drawings chars.
    pub fn right(&mut self, sym: char) {
        let or = (sym, sym, sym);
        let height = self.height();
        let drawings = if height == 1 {
            // If height is 1, use directly sym, not a drawing variant
            or
        } else {
            get_drawings_chars(sym).unwrap_or(or)
        };
        for i in 0..height {
            self.lines[i].push(if i == 0 {
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
