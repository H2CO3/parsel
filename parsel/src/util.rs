//! Helper functions, types and macros that didn't fit anywhere else.

use std::fmt::{self, Debug, Display, Formatter};
use crate::{Error, Span, Spanned};

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
///     Lit::from(76192_u128),
/// ]);
///
/// assert_eq!(actual, expected);
/// #
/// # Result::<()>::Ok(())
/// ```
#[macro_export]
macro_rules! try_parse_quote {
    ($($tt:tt)*) => {
        match ::parsel::parse2(::parsel::quote::quote!($($tt)*)) {
            ::parsel::Result::Ok(ast) => ast,
            ::parsel::Result::Err(error) => {
                return ::core::result::Result::Err(
                    ::core::convert::From::from(error)
                )
            }
        }
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
        match ::parsel::parse2(::parsel::quote::quote_spanned!($span => $($tt)*)) {
            ::parsel::Result::Ok(ast) => ast,
            ::parsel::Result::Err(error) => {
                return ::core::result::Result::Err(
                    ::core::convert::From::from(error)
                )
            }
        }
    }
}

/// Extension trait for formatting the span of AST nodes in a human-readable manner.
pub trait FormatSpan: Spanned {
    fn format_span(&self) -> SpanDisplay;
}

impl<T> FormatSpan for T
where
    T: ?Sized + Spanned
{
    fn format_span(&self) -> SpanDisplay {
        SpanDisplay::new(self.span())
    }
}

/// Helper type that formats a `Span` in a human-readable way.
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

