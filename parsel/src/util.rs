//! Helper functions, types and macros that didn't fit anywhere else.

use core::cmp::max_by_key;
use core::ops::Range;
use core::fmt::{self, Debug, Display, Formatter, Write};
use proc_macro2::{TokenStream, TokenTree, Spacing, Delimiter};
use syn::parse::{ParseStream, discouraged::Speculative};
use quote::ToTokens;
use crate::{Error, Result, Span, Spanned, LineColumn};

/// Similar to `syn::parse_quote!`, but instead of panicking, it returns an
/// `Err` if the inferred type fails to parse from the specified token stream.
///
/// ```rust
/// use core::iter::FromIterator;
/// use parsel::{try_parse_quote, Result};
/// use parsel::ast::{Lit, Many};
///
/// fn try_parse_literals(bit: bool, number: u64) -> Result<Many<Lit>> {
///     let ast: Many<Lit> = try_parse_quote!(#bit "some text" #number);
///     Ok(ast)
/// }
///
/// let actual: Many<Lit> = try_parse_literals(true, 76192)?;
/// let expected: Many<Lit> = Many::from_iter([
///     Lit::from(true),
///     Lit::from("some text"),
///     Lit::from(76192_u64),
/// ]);
///
/// assert_eq!(actual, expected);
/// #
/// # Result::<()>::Ok(())
/// ```
#[macro_export]
macro_rules! try_parse_quote {
    ($($tt:tt)*) => {
        ::parsel::parse2(::parsel::quote::quote!($($tt)*))?
    }
}

/// Similar to `syn::parse_quote_spanned!`, but instead of panicking, it returns
/// an `Err` if the inferred type fails to parse from the specified token stream.
///
/// ```rust
/// use parsel::{parse_str, try_parse_quote_spanned, Result};
/// use parsel::ast::{word, Word, Punctuated};
/// use parsel::ast::token::Comma;
///
/// fn try_parse_words(interp: &str, spanner: &str) -> Result<Punctuated<Word, Comma>> {
///     let interp: Word = parse_str(interp)?;
///     let spanner: Word = parse_str(spanner)?;
///
///     // Interpolated tokens must preserve their own span, whereas
///     // tokens originating from the macro will have the specified span.
///     let ast = try_parse_quote_spanned!{ spanner.span() =>
///         lorem, #interp, ipsum
///     };
///
///     Ok(ast)
/// }
///
/// let interp = "quodsit";
/// let spanner = "this_is_a_long_identifier";
///
/// let actual = try_parse_words(interp, spanner)?;
/// let expected_strings = ["lorem", interp, "ipsum"];
/// let expected: Punctuated<Word, Comma> = expected_strings
///     .iter()
///     .copied()
///     .map(word)
///     .collect();
///
/// let actual_ends: Vec<_> = actual
///     .iter()
///     .map(|w| w.span().end().column)
///     .collect();
/// let expected_ends = vec![spanner.len(), interp.len(), spanner.len()];
///
/// assert_eq!(actual, expected);
/// assert_eq!(actual_ends, expected_ends);
/// #
/// # Result::<()>::Ok(())
/// ```
#[macro_export]
macro_rules! try_parse_quote_spanned {
    ($span:expr => $($tt:tt)*) => {
        ::parsel::parse2(::parsel::quote::quote_spanned!($span => $($tt)*))?
    }
}

/// Extension trait for formatting the span of AST nodes in a human-readable manner,
/// and for (re-)computing byte offsets into the source based on the line/column
/// location, since this information is not exposed by the public API of `Span`.
pub trait SpannedExt: Spanned {
    fn format_span(&self) -> SpanDisplay;

    fn byte_range(&self, source: &str) -> Range<usize>;

    fn char_range(&self, source: &str) -> Range<usize>;
}

impl<T> SpannedExt for T
where
    T: ?Sized + Spanned
{
    fn format_span(&self) -> SpanDisplay {
        SpanDisplay::new(self.span())
    }

    /// TODO(H2CO3): a faster, less naive implementation would be great.
    /// We should use the byte offset of `start` to compute that of `end`,
    /// sparing the double scan of the source up until the start location.
    ///
    /// ```rust
    /// # use parsel::{Error, Result};
    /// # use parsel::util::SpannedExt;
    /// # use parsel::ast::{Lit, Many};
    /// #
    /// let source = r#"
    ///    -3.667
    ///   1248  "string ű literal"
    ///       "wíőzs"
    /// "#;
    /// let tokens: Many<Lit> = source.parse()?;
    ///
    /// assert_eq!(tokens.len(), 4);
    /// assert_eq!(tokens[0].byte_range(source),  4..10);
    /// assert_eq!(tokens[1].byte_range(source), 13..17);
    /// assert_eq!(tokens[2].byte_range(source), 19..38);
    /// assert_eq!(tokens[3].byte_range(source), 45..54);
    /// #
    /// # Result::<()>::Ok(())
    /// ```
    fn byte_range(&self, source: &str) -> Range<usize> {
        let span = self.span();
        let start = byte_offset(source, span.start());
        let end = byte_offset(source, span.end());

        start..end
    }

    /// TODO(H2CO3): a faster, less naive implementation would be great.
    /// We should use the char offset of `start` to compute that of `end`,
    /// sparing the double scan of the source up until the start location.
    ///
    /// ```rust
    /// # use parsel::{Error, Result};
    /// # use parsel::util::SpannedExt;
    /// # use parsel::ast::{Lit, Many};
    /// #
    /// let source = r#"
    ///    -3.667
    ///   1248  "string ű literal"
    ///       "wíőzs"
    /// "#;
    /// let tokens: Many<Lit> = source.parse()?;
    ///
    /// assert_eq!(tokens.len(), 4);
    /// assert_eq!(tokens[0].char_range(source),  4..10);
    /// assert_eq!(tokens[1].char_range(source), 13..17);
    /// assert_eq!(tokens[2].char_range(source), 19..37);
    /// assert_eq!(tokens[3].char_range(source), 44..51);
    /// #
    /// # Result::<()>::Ok(())
    /// ```
    fn char_range(&self, source: &str) -> Range<usize> {
        let span = self.span();
        let start = char_offset(source, span.start());
        let end = char_offset(source, span.end());

        start..end
    }
}

/// Compute byte offset from line and column because
/// we can't directly get the byte range of a `Span`.
fn byte_offset(source: &str, loc: LineColumn) -> usize {
    // split including newlines so that they are also counted
    let mut lines = source.split_inclusive('\n');

    // byte offset of all lines except the current one
    let line_offset: usize = lines
        .by_ref()
        .take(loc.line.saturating_sub(1))
        .map(str::len)
        .sum();

    // byte offset within the current line
    let char_offset: usize = lines.next().map_or(0, |line| {
        line.char_indices()
            .nth(loc.column)
            .map_or(line.len(), |(index, _)| index)
    });

    line_offset + char_offset
}

/// Compute char offset from line and column because
/// we can't directly get the byte range of a `Span`.
fn char_offset(source: &str, loc: LineColumn) -> usize {
    // split including newlines so that they are also counted
    let mut lines = source.split_inclusive('\n');

    // `char` offset of all lines except the current one
    let line_offset: usize = lines
        .by_ref()
        .take(loc.line.saturating_sub(1))
        .flat_map(str::chars)
        .count();

    // `char` offset within the current line
    let char_offset = loc.column;

    line_offset + char_offset
}

/// Helper type that formats a `Span` in a human-readable way.
///
/// ```rust
/// # use parsel::{Error, Parse, TokenStream};
/// # use parsel::ast::{Token, Word, Separated};
/// # use parsel::util::SpannedExt;
/// #
/// #[derive(Clone, Debug, Parse)]
/// struct HttpHeader {
///     key: Separated<Word, Token![-]>,
///     colon: Token![:],
///     value: TokenStream,
/// }
///
/// let header: HttpHeader = parsel::parse_str(r#"
///     // this comment exists only so that there is a line before the actual tokens
///     Content-Type: application/json
///     /* another comment, just to confuse the lexer */
/// "#)?;
///
/// let key_span = header.key.format_span().to_string();
/// assert_eq!(key_span, "3:5..3:16");
///
/// let colon_span = header.colon.format_span().to_string();
/// assert_eq!(colon_span, "3:17..3:17");
///
/// let value_span = header.value.format_span().to_string();
/// assert_eq!(value_span, "3:19..3:34");
/// #
/// # Ok::<(), Error>(())
/// ```
#[derive(Clone, Copy, Debug)]
pub struct SpanDisplay {
    span: Span,
}

impl SpanDisplay {
    pub const fn new(span: Span) -> Self {
        SpanDisplay { span }
    }
}

impl From<Span> for SpanDisplay {
    fn from(span: Span) -> Self {
        SpanDisplay::new(span)
    }
}

impl Display for SpanDisplay {
    fn fmt(&self, formatter: &mut Formatter<'_>) -> fmt::Result {
        write!(
            formatter,
            "{start_line}:{start_col}..{end_line}:{end_col}",
            start_line = self.span.start().line,
            start_col = self.span.start().column + 1, // 0-indexed
            end_line = self.span.end().line,
            end_col = self.span.end().column, // + 1 - 1: 0-indexed but inclusive
        )
    }
}

/// Not public API -- runtime helper for `parsel_derive::Parse`.
///
/// Preserves span and message of original error (because they
/// are more specific), but also adds our own, wider context.
#[doc(hidden)]
pub fn chain_error<T: Display>(
    cause: Error,
    enum_: &str,
    ctor: &str,
    field: T,
) -> Error {
    let message = if enum_.is_empty() {
        format!(
            "error parsing {ctor}::{field}, caused by:\n{cause}",
            ctor = ctor,
            field = field,
            cause = cause,
        )
    } else {
        format!(
            "error parsing {enum_}::{ctor}::{field}, caused by:\n{cause}",
            enum_ = enum_,
            ctor = ctor,
            field = field,
            cause = cause,
        )
    };
    Error::new(cause.span(), message)
}

/// Not public API -- runtime helper for `parsel_derive::Parse`.
///
/// Speculatively parse a sub-production of an alternation (`enum`).
/// Only advances the input if the parse succeeds.
///
/// If parsing fails, and this production got farther in the input
/// than all previous ones, then it updates the error location and
/// message so that it points to this sub-production. This heuristic
/// is based on the observation that the intended production in an
/// alternation that failed to parse was most likely the one that
/// produced the longest successful partial parse.
#[doc(hidden)]
pub fn try_parse_variant<T, F>(
    input: ParseStream<'_>,
    error_acc: Option<Error>,
    parser: F,
) -> Result<T>
where
    F: FnOnce(ParseStream<'_>) -> Result<T>,
{
    let fork = input.fork();

    match parser(&fork) {
        Ok(value) => {
            input.advance_to(&fork);
            Ok(value)
        }
        Err(error) => {
            let farthest = match error_acc {
                Some(acc) => max_by_key(acc, error, |e| e.span().end()),
                None => error,
            };
            Err(farthest)
        }
    }
}

/// Helper type for correctly and reasonably "pretty"-printing any `TokenStream` in
/// a grammar- and language-agnostic way. This mostly means dealing with parentheses,
/// so that nested structures don't end up on one single long line.
///
/// Of course, it is not possible to perform pretty-printing in a completely generic
/// manner, but the primary purpose of this mechanism is not that -- it's merely trying
/// to be a useful debugging tool, of which the results are less unnecessarily verbose,
/// and therefore easier to read, than the output of `#[derive(Debug)]`.
///
/// ```rust
/// use parsel::util::TokenStreamFormatter;
/// use parsel::quote::quote;
///
/// let ts = quote!{
///     [
///         [
///             7.43 * {
///                 zzz (
///                     3333 + "52" - 'a / [
///                         foo bar || &baz;
///                     ]
///                 ) != 5;
///                 ww;
///                 6 <<= 78 >>= 951,
///                 $ foo $bar #![attribute]
///             },
///             x, y
///         ]
///     ]
/// };
///
/// let mut string = String::new();
/// let mut fmt = TokenStreamFormatter::new(&mut string);
/// fmt.write(ts)?;
///
/// assert_eq!(string, str::trim(r#"
/// [
///     [
///         7.43 * {
///             zzz (
///                 3333 + "52" - 'a / [
///                     foo bar || & baz ;
///                 ]
///             )
///             != 5 ;
///             ww ;
///             6 <<= 78 >>= 951 ,
///             $ foo $ bar # ! [
///                 attribute
///             ]
///         }
///         ,
///         x ,
///         y
///     ]
/// ]
/// "#));
/// #
/// # Ok::<(), core::fmt::Error>(())
/// ```
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct TokenStreamFormatter<S, W> {
    indent_level: usize,
    indent_string: S,
    writer: W,
}

impl<S, W> TokenStreamFormatter<S, W>
where
    S: AsRef<str>,
{
    /// Constructor for indenting with arbitrary whitespace.
    ///
    /// This returns an error when non-whitespace characters are present in the indentation.
    ///
    /// ```rust
    /// # use std::io::Cursor;
    /// # use parsel::util::TokenStreamFormatter;
    /// #
    /// let ok = TokenStreamFormatter::with_indent("  \t", Cursor::new(&[] as &[u8]));
    /// assert!(ok.is_ok());
    ///
    /// let err = TokenStreamFormatter::with_indent("  not ws ", Cursor::new(&[] as &[u8]));
    /// assert!(err.is_err());
    /// ```
    pub fn with_indent(indent_string: S, writer: W) -> Result<Self> {
        if indent_string.as_ref().trim().is_empty() {
            Ok(TokenStreamFormatter {
                indent_level: 0,
                indent_string,
                writer,
            })
        } else {
            Err(Error::new(Span::call_site(), "indentation contains non-whitespace characters"))
        }
    }
}

impl<S, W> TokenStreamFormatter<S, W>
where
    S: AsRef<str>,
    W: Write,
{
    pub fn write(&mut self, stream: TokenStream) -> fmt::Result {
        self.write_indent()?;
        let mut spacing = Spacing::Joint;
        let mut iter = stream.into_iter().peekable();

        while let Some(tt) = iter.next() {
            if spacing == Spacing::Joint {
                spacing = Spacing::Alone;
            } else {
                self.writer.write_char(' ')?;
            }

            match tt {
                TokenTree::Literal(lit) => write!(self.writer, "{}", lit)?,
                TokenTree::Ident(ident) => write!(self.writer, "{}", ident)?,
                TokenTree::Punct(punct) => {
                    write!(self.writer, "{}", punct)?;
                    spacing = punct.spacing();

                    if matches!(
                        (punct.as_char(), spacing, iter.peek()),
                        (',' | ';', Spacing::Alone, Some(_))
                    ) {
                        writeln!(self.writer)?;
                        self.write_indent()?;
                        spacing = Spacing::Joint;
                    }
                }
                TokenTree::Group(group) => {
                    let (open, close) = match group.delimiter() {
                        Delimiter::None => {
                            self.write(group.stream())?;
                            continue;
                        }
                        Delimiter::Parenthesis => ('(', ')'),
                        Delimiter::Bracket => ('[', ']'),
                        Delimiter::Brace => ('{', '}'),
                    };

                    self.writer.write_char(open)?;
                    self.indent_level += 1;
                    writeln!(self.writer)?;

                    self.write(group.stream())?;

                    self.indent_level -= 1;
                    writeln!(self.writer)?;
                    self.write_indent()?;
                    self.writer.write_char(close)?;

                    if iter.peek().is_some() {
                        writeln!(self.writer)?;
                        self.write_indent()?;
                        spacing = Spacing::Joint;
                    }
                }
            }
        }

        Ok(())
    }

    pub fn write_node<T>(&mut self, node: &T) -> fmt::Result
    where
        T: ?Sized + ToTokens,
    {
        self.write(node.to_token_stream())
    }

    fn write_indent(&mut self) -> fmt::Result {
        for _ in 0..self.indent_level {
            self.writer.write_str(self.indent_string.as_ref())?;
        }

        Ok(())
    }
}

impl<W> TokenStreamFormatter<&'static str, W> {
    pub const fn new(writer: W) -> Self {
        TokenStreamFormatter {
            indent_level: 0,
            indent_string: "    ",
            writer,
        }
    }
}

/// Helper for implementing `Display` in terms of `ToTokens`.
pub fn pretty_print_tokens<T, W>(node: &T, writer: W) -> fmt::Result
where
    T: ?Sized + ToTokens,
    W: Write,
{
    let mut formatter = TokenStreamFormatter::new(writer);
    formatter.write_node(node)
}
