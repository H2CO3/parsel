//! This module provides helper types for common grammar idioms/needs, such as:
//!
//! * Repetition
//! * Parenthesization, delimiting
//! * Separation of consecutive items

use core::cmp::{max_by_key, PartialOrd, Ord, Ordering};
use core::iter::{FromIterator, FusedIterator};
use core::convert::TryFrom;
use core::str::FromStr;
use core::num::NonZeroUsize;
use core::slice::SliceIndex;
use core::hash::{Hash, Hasher};
use core::ops::{Deref, DerefMut, Index, IndexMut};
use core::fmt::{self, Debug, Display, Formatter};
use std::borrow::{Cow, Borrow, BorrowMut};
use proc_macro2::{TokenStream, TokenTree, Span, Literal};
use ordered_float::NotNan;
use syn::spanned::Spanned;
use syn::ext::IdentExt;
use syn::parse::{Error, Result, Parse, ParseStream};
use syn::parse::discouraged::Speculative;
use syn::punctuated::{Pair, IntoIter, Iter, IterMut, IntoPairs, Pairs, PairsMut};
use quote::{ToTokens, TokenStreamExt};
use crate::util::pretty_print_tokens;

pub use proc_macro2::Ident;
pub use syn::Token;
pub use syn::token;

/// Creates an `Ident` spanned to the call site. Useful for testing.
pub fn ident(name: &str) -> Ident {
    Ident::new(name, Span::call_site())
}

/// Creates a [`Word`](type.Word.html) spanned to the call site. Useful for testing.
pub fn word(name: &str) -> Word {
    Word::new(name, Span::call_site())
}

/// A trait for parameterizing [`CustomIdent`](struct.CustomIdent.html) over a set of keywords.
pub trait KeywordList {
    /// The exhaustive list of keywords that should not be allowed as an identifier.
    const KEYWORDS: &'static [&'static str];
}

/// An identifier which allows customizing the keywords of the language,
/// i.e., which words should be accepted and rejected when parsing.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct CustomIdent<K> {
    ident: Ident,
    marker: K,
}

impl<K> CustomIdent<K> {
    pub fn span(&self) -> Span {
        self.ident.span()
    }

    pub fn set_span(&mut self, span: Span) {
        self.ident.set_span(span);
    }

    pub fn token(&self) -> Ident {
        self.ident.clone()
    }
}

impl<K, T> PartialEq<T> for CustomIdent<K>
where
    T: AsRef<str>
{
    fn eq(&self, other: &T) -> bool {
        self.ident == other
    }
}

impl<K> TryFrom<Ident> for CustomIdent<K>
where
    K: Default + KeywordList
{
    type Error = Error;

    fn try_from(ident: Ident) -> Result<Self> {
        if K::KEYWORDS.iter().any(|kw| ident == kw) {
            Err(Error::new(ident.span(), "expected identifier, found keyword"))
        } else {
            Ok(CustomIdent {
                ident,
                marker: K::default(),
            })
        }
    }
}

impl<K> From<CustomIdent<K>> for Ident {
    fn from(ident: CustomIdent<K>) -> Self {
        ident.ident
    }
}

impl<K> Debug for CustomIdent<K> {
    fn fmt(&self, formatter: &mut Formatter<'_>) -> fmt::Result {
        Debug::fmt(&self.ident, formatter)
    }
}

impl<K> Display for CustomIdent<K> {
    fn fmt(&self, formatter: &mut Formatter<'_>) -> fmt::Result {
        Display::fmt(&self.ident, formatter)
    }
}

impl<K> FromStr for CustomIdent<K>
where
    K: Default + KeywordList
{
    type Err = Error;

    fn from_str(string: &str) -> Result<Self> {
        syn::parse_str(string)
    }
}

impl<K> Parse for CustomIdent<K>
where
    K: Default + KeywordList
{
    fn parse(input: ParseStream<'_>) -> Result<Self> {
        input.call(Ident::parse_any).and_then(CustomIdent::try_from)
    }
}

impl<K> ToTokens for CustomIdent<K> {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        self.ident.to_tokens(tokens);
    }
}

/// Marker type for [`CustomIdent`](struct.CustomIdent.html) that allows parsing
/// any word as a valid identifier (i.e. it doesn't mark any of them as a keyword).
#[derive(Clone, Copy, Default, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct AllowAll;

impl KeywordList for AllowAll {
    const KEYWORDS: &'static [&'static str] = &[];
}

/// Convenience type alias for an identifier that successfully parses
/// from any single word, including Rust keywords. (This is in contrast
/// with the default behavior of `Ident`.)
///
/// ```rust
/// # use parsel::parse_quote;
/// # use parsel::ast::Word;
/// let non_kw: Word = parse_quote!(not_a_keyword);
/// assert_eq!(non_kw, "not_a_keyword");
///
/// let underscore: Word = parse_quote!(_);
/// assert_eq!(underscore, "_");
///
/// let keyword_fn: Word = parse_quote!(fn);
/// assert_eq!(keyword_fn, "fn");
///
/// let keyword_pub: Word = parse_quote!(pub);
/// assert_eq!(keyword_pub, "pub");
/// ```
pub type Word = CustomIdent<AllowAll>;

impl Word {
    /// This is only defined on `Word` and not on `CustomIdent` in general,
    /// because this practice prevents users from accidentally creating an
    /// invalid identifier (one that is a keyword, as defined by the user).
    pub fn new(string: &str, span: Span) -> Self {
        Word {
            ident: Ident::new(string, span),
            marker: AllowAll,
        }
    }
}

/// Declares a module containing custom keywords as defined by `custom_keyword!`, and a
/// `Keywords` marker type for [`CustomIdent`](ast/struct.CustomIdent.html) implementing
/// [`KeywordList`](ast/trait.KeywordList.html).
///
/// ```rust
/// # use parsel::{define_keywords, Error, Result, TokenTree};
/// # use parsel::quote::quote;
/// # use parsel::ast::{ident, CustomIdent, KeywordList};
/// #
/// define_keywords!{
///     mod kw {
///         Foo => foo;
///         Bar => bar;
///         Quux => quux;
///     }
/// }
///
/// // Idiom for using `CustomIdent`
/// type MyIdent = CustomIdent<kw::Keywords>;
///
/// // Valid keywords in this language
/// let id_self: MyIdent = "self".parse()?;
/// assert_eq!(id_self, "self");
///
/// let id_async: MyIdent = "async".parse()?;
/// assert_eq!(id_async, "async");
///
/// let id_baz: MyIdent = "baz".parse()?;
/// assert_eq!(id_baz, "baz");
///
/// let id_multi_part: MyIdent = "multi_part".parse()?;
/// assert_eq!(id_multi_part, "multi_part");
///
/// let _: kw::Bar = "bar".parse()?;
///
/// // Invalid keywords
/// let invalid: Result<MyIdent> = "quux".parse();
/// assert_eq!(
///     invalid.unwrap_err().to_string(),
///     "expected identifier, found keyword",
/// );
///
/// let invalid_quux: Result<kw::Quux> = "somethingelse".parse();
/// assert_eq!(
///     invalid_quux.unwrap_err().to_string(),
///     "expected keyword `quux`",
/// );
///
/// let kw_bar = kw::Bar::default();
/// let kw_quux = kw::Quux::default();
/// let some_stream = quote![#kw_quux #kw_bar #kw_quux];
/// let actual_tokens: Vec<_> = some_stream.clone().into_iter().collect();
/// let expected_tokens = ["quux", "bar", "quux"].map(|x| TokenTree::from(ident(x)));
///
/// assert_eq!(some_stream.to_string(), "quux bar quux");
/// assert!(matches!(actual_tokens, expected_tokens));
///
/// // Ensure that the generated `Keywords` struct implements `KeywordList`
/// // and is default-constructible, trivially-copiable
/// fn assert_keyword_list<K>(_: K)
/// where
///     K: Copy + Default + KeywordList
/// {}
///
/// assert_keyword_list(kw::Keywords);
/// #
/// # Ok::<(), Error>(())
/// ```
#[macro_export]
macro_rules! define_keywords {
    ($vis:vis mod $modname:ident { $($name:ident => $kw:ident;)* }) => {
        $vis mod $modname {
            $(
                #[derive(Clone, Copy)]
                pub struct $name {
                    span: ::parsel::Span,
                }

                impl $name {
                    pub fn new(span: ::parsel::Span) -> Self {
                        $name { span }
                    }

                    pub fn as_str(&self) -> &'static str {
                        ::core::stringify!($kw)
                    }

                    pub fn span(&self) -> ::parsel::Span {
                        self.span
                    }

                    pub fn set_span(&mut self, span: ::parsel::Span) {
                        self.span = span;
                    }

                    pub fn token(&self) -> ::parsel::ast::Ident {
                        ::parsel::ast::Ident::new(::core::stringify!($kw), self.span)
                    }
                }

                impl ::core::default::Default for $name {
                    fn default() -> Self {
                        Self::new(::parsel::Span::call_site())
                    }
                }

                impl ::core::convert::From<$name> for ::parsel::proc_macro2::TokenTree {
                    fn from(kw: $name) -> Self {
                        ::parsel::proc_macro2::TokenTree::Ident(kw.token())
                    }
                }

                // These traits are implemented manually because `Span: !PartialEq + !Hash`
                impl ::core::cmp::PartialEq for $name {
                    fn eq(&self, _other: &Self) -> bool {
                        true
                    }
                }

                impl<T> ::core::cmp::PartialEq<T> for $name
                where
                    T: ::core::convert::AsRef<::core::primitive::str>
                {
                    fn eq(&self, other: &T) -> bool {
                        self.as_str() == ::core::convert::AsRef::as_ref(other)
                    }
                }

                impl ::core::cmp::Eq for $name {}

                impl ::core::cmp::PartialOrd for $name {
                    fn partial_cmp(&self, other: &Self) -> ::core::option::Option<::core::cmp::Ordering> {
                        ::core::option::Option::Some(::core::cmp::Ord::cmp(self, other))
                    }
                }

                impl ::core::cmp::Ord for $name {
                    fn cmp(&self, other: &Self) -> ::core::cmp::Ordering {
                        ::core::cmp::Ordering::Equal
                    }
                }

                impl ::core::hash::Hash for $name {
                    fn hash<H>(&self, _state: &mut H) {}
                }

                impl ::core::fmt::Debug for $name {
                    fn fmt(&self, formatter: &mut ::core::fmt::Formatter<'_>) -> ::core::fmt::Result {
                        ::core::fmt::Display::fmt(::core::stringify!($kw), formatter)
                    }
                }

                impl ::core::fmt::Display for $name {
                    fn fmt(&self, formatter: &mut ::core::fmt::Formatter<'_>) -> ::core::fmt::Result {
                        formatter.pad(::core::stringify!($kw))
                    }
                }

                impl ::core::str::FromStr for $name {
                    type Err = ::parsel::Error;

                    fn from_str(string: &::core::primitive::str) -> ::parsel::Result<Self> {
                        ::parsel::parse_str(string)
                    }
                }

                impl ::parsel::Parse for $name {
                    fn parse(input: ::parsel::syn::parse::ParseStream<'_>) -> ::parsel::Result<Self> {
                        let ident: ::parsel::ast::Ident = input.call(::parsel::syn::ext::IdentExt::parse_any)?;
                        let span = ident.span();

                        if ident == ::core::stringify!($kw) {
                            ::parsel::Result::Ok($name { span })
                        } else {
                            let message = ::core::concat!("expected keyword `", ::core::stringify!($kw), "`");

                            ::parsel::Result::Err(
                                ::parsel::Error::new(span, message)
                            )
                        }
                    }
                }

                impl ::parsel::ToTokens for $name {
                    fn to_tokens(&self, tokens: &mut ::parsel::TokenStream) {
                        ::parsel::quote::TokenStreamExt::append(tokens, self.token());
                    }
                }
            )*

            #[derive(Clone, Copy, Default, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
            pub struct Keywords;

            impl ::parsel::ast::KeywordList for Keywords {
                const KEYWORDS: &'static [&'static ::core::primitive::str] = &[
                    $(::core::stringify!($kw),)*
                ];
            }
        }
    }
}

/// Always parses succesfully, consuming no tokens. Emits nothing when printed.
///
/// This type exists because
/// [`syn::parse::Nothing`](https://docs.rs/syn/latest/syn/parse/struct.Nothing.html)
/// doesn't implement [`ToTokens`](https://docs.rs/quote/latest/quote/trait.ToTokens.html).
#[derive(Clone, Copy, Default, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct Empty;

impl Empty {
    pub const fn new() -> Self {
        Empty
    }
}

impl FromStr for Empty {
    type Err = Error;

    fn from_str(string: &str) -> Result<Self> {
        syn::parse_str(string)
    }
}

impl Display for Empty {
    fn fmt(&self, _formatter: &mut Formatter<'_>) -> fmt::Result {
        Ok(())
    }
}

impl Parse for Empty {
    fn parse(_input: ParseStream<'_>) -> Result<Self> {
        Ok(Empty)
    }
}

impl ToTokens for Empty {
    fn to_tokens(&self, _tokens: &mut TokenStream) {}
}

/// Verifies that parsing reached the end of the input (i.e., the end of
/// the parse stream at the current level of nesting). Useful for ensuring
/// that an input or a group is fully parsed by preceding types.
///
/// Consumes no tokens when parsed, produces no tokens when printed.
///
/// ```rust
/// # use parsel::{Result, Parse};
/// # use parsel::ast::{LitBool, LitInt, Eof, Punctuated};
/// # use parsel::ast::token::Comma;
/// #
/// // an empty string / token stream should trivially parse as `Eof`
/// let _: Eof = "".parse()?;
/// // so should an all-whitespace one
/// let _: Eof = "\r\n   ".parse()?;
///
/// #[derive(PartialEq, Eq, Debug, Parse)]
/// struct BoolAtEnd {
///     value: LitBool,
///     eof: Eof,
/// }
///
/// #[derive(PartialEq, Eq, Debug, Parse)]
/// enum BoolAtEndOrInt {
///     Bool(BoolAtEnd),
///     Int(LitInt),
/// }
///
/// let actual: Punctuated<BoolAtEndOrInt, Comma> = "2, 46, 802, false".parse()?;
/// let actual: Vec<_> = actual.into_iter().collect();
/// let expected = [
///     BoolAtEndOrInt::Int(LitInt::from(2)),
///     BoolAtEndOrInt::Int(LitInt::from(46)),
///     BoolAtEndOrInt::Int(LitInt::from(802)),
///     BoolAtEndOrInt::Bool(BoolAtEnd {
///         value: LitBool::from(false),
///         eof: Eof,
///     }),
/// ];
/// assert_eq!(actual, expected);
///
/// let bad: Result<Punctuated<BoolAtEndOrInt, Comma>> = "2, 46, false, 802".parse();
/// let message = bad.as_ref().unwrap_err().to_string();
/// assert!(
///     message.contains("expected end of input"),
///     "actual error: {}", message
/// );
/// #
/// # Result::<()>::Ok(())
/// ```
#[derive(Clone, Copy, Default, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct Eof;

impl Eof {
    pub const fn new() -> Self {
        Eof
    }
}

impl FromStr for Eof {
    type Err = Error;

    fn from_str(string: &str) -> Result<Self> {
        syn::parse_str(string)
    }
}

impl Display for Eof {
    fn fmt(&self, _formatter: &mut Formatter<'_>) -> fmt::Result {
        Ok(())
    }
}

impl Parse for Eof {
    fn parse(input: ParseStream<'_>) -> Result<Self> {
        if input.is_empty() {
            Ok(Eof)
        } else {
            Err(input.error("expected end of input or group, found garbage"))
        }
    }
}

impl ToTokens for Eof {
    fn to_tokens(&self, _tokens: &mut TokenStream) {}
}

/// Verifies that parsing did not yet reach the end of the input (i.e., the end
/// of the parse stream at the current level of nesting). Useful for conditionally
/// parsing an optional production with no other obvious prefix token.
///
/// Consumes no tokens when parsed, produces no tokens when printed.
///
/// ```rust
/// # use parsel::{Result, Span, Parse};
/// # use parsel::ast::{Lit, NotEof, Maybe, Brace};
/// # use parsel::ast::token::Semi;
/// #
/// #[derive(PartialEq, Eq, Debug, Parse)]
/// struct SimpleBlockBody {
///     statement: Lit,
///     semicolon: Semi,
///     expression: Maybe<NotEof, Lit>,
/// }
/// type SimpleBlock = Brace<SimpleBlockBody>;
///
/// let actual_short: SimpleBlock = "{ 54194; }".parse()?;
/// let expected_short: SimpleBlock = Brace::new(
///     SimpleBlockBody {
///         statement: Lit::from(54194_u128),
///         semicolon: Semi::default(),
///         expression: Maybe::default(),
///     },
///     Span::call_site(),
/// );
/// assert_eq!(actual_short, expected_short);
///
/// let actual_long: SimpleBlock = "{ 54194; true }".parse()?;
/// let expected_long: SimpleBlock = Brace::new(
///     SimpleBlockBody {
///         statement: Lit::from(54194_u128),
///         semicolon: Semi::default(),
///         expression: Maybe::from(Lit::from(true)),
///     },
///     Span::call_site(),
/// );
/// assert_eq!(actual_long, expected_long);
///
/// // an empty string / token stream should trivially fail to parse as `Eof`
/// let bad: Result<NotEof> = "".parse();
/// assert!(bad.is_err());
///
/// // an empty string / token stream should trivially fail to parse as `Eof`
/// let bad_ws_only: Result<NotEof> = " \t\n".parse();
/// assert!(bad_ws_only.is_err());
/// #
/// # Result::<()>::Ok(())
/// ```
#[derive(Clone, Copy, Default, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct NotEof;

impl NotEof {
    pub const fn new() -> Self {
        NotEof
    }
}

impl FromStr for NotEof {
    type Err = Error;

    fn from_str(string: &str) -> Result<Self> {
        syn::parse_str(string)
    }
}

impl Display for NotEof {
    fn fmt(&self, _formatter: &mut Formatter<'_>) -> fmt::Result {
        Ok(())
    }
}

impl Parse for NotEof {
    fn parse(input: ParseStream<'_>) -> Result<Self> {
        if input.is_empty() {
            Err(input.error("unexpected end of input"))
        } else {
            Ok(NotEof)
        }
    }
}

impl ToTokens for NotEof {
    fn to_tokens(&self, _tokens: &mut TokenStream) {}
}

/// Parses an optional expression introduced by some lookahead tokens.
///
/// ```rust
/// # use parsel::{parse_quote, Parse, ToTokens};
/// # use parsel::ast::{token, ident, Ident, Empty, Maybe, Paren, Brace};
/// #[derive(PartialEq, Eq, Debug, Parse, ToTokens)]
/// enum Ty {
///     Named(Ident),
///     Ref(
///         token::And,
///         #[parsel(recursive)]
///         Box<Self>,
///     ),
///     Opt(
///         token::Question,
///         #[parsel(recursive)]
///         Box<Self>,
///     ),
/// }
///
/// #[derive(PartialEq, Eq, Debug, Parse, ToTokens)]
/// struct TyAnnot {
///     colon: token::Colon,
///     ty: Ty,
/// }
///
/// #[derive(PartialEq, Eq, Debug, Parse, ToTokens)]
/// struct Function {
///     kw_fn: token::Fn,
///     name: Ident,
///     argument: Paren<Maybe<Ident, TyAnnot>>,
///     return_ty: Maybe<token::RArrow, Ty>,
///     body: Brace<Empty>,
/// }
///
/// let unit_to_unit_function: Function = parse_quote!{
///     fn foo() {}
/// };
/// assert_eq!(
///     unit_to_unit_function,
///     Function {
///         kw_fn: Default::default(),
///         name: ident("foo"),
///         argument: Paren::default(),
///         return_ty: Maybe::default(),
///         body: Brace::default(),
///     }
/// );
///
/// let unit_to_opt_function: Function = parse_quote!{
///     fn another_name() -> ?Rofl {}
/// };
/// assert_eq!(
///     unit_to_opt_function,
///     Function {
///         kw_fn: Default::default(),
///         name: ident("another_name"),
///         argument: Paren::default(),
///         return_ty: Maybe::from((
///             token::RArrow::default(),
///             Ty::Opt(
///                 token::Question::default(),
///                 Box::new(Ty::Named(ident("Rofl"))),
///             )
///         )),
///         body: Brace::default(),
///     }
/// );
///
/// let opt_to_ref_function: Function = parse_quote!{
///     fn fn_3(the_arg: ?&DoubleTrouble) -> &Indirect {}
/// };
/// assert_eq!(
///     opt_to_ref_function,
///     Function {
///         kw_fn: Default::default(),
///         name: ident("fn_3"),
///         argument: Paren::from(Maybe::from((
///             ident("the_arg"),
///             TyAnnot {
///                 colon: Default::default(),
///                 ty: Ty::Opt(
///                     token::Question::default(),
///                     Box::new(Ty::Ref(
///                         token::And::default(),
///                         Box::new(Ty::Named(ident("DoubleTrouble"))),
///                     )),
///                 )
///             }
///         ))),
///         return_ty: Maybe::from((
///             token::RArrow::default(),
///             Ty::Ref(
///                 token::And::default(),
///                 Box::new(Ty::Named(ident("Indirect"))),
///             )
///         )),
///         body: Brace::default(),
///     }
/// );
/// ```
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct Maybe<P, T = Empty> {
    inner: Option<(P, T)>,
}

impl<P, T> Maybe<P, T> {
    pub const fn new() -> Self {
        Maybe { inner: None }
    }

    pub fn as_prefix(&self) -> Option<&P> {
        self.inner.as_ref().map(|(prefix, _)| prefix)
    }

    pub fn as_prefix_mut(&mut self) -> Option<&mut P> {
        self.inner.as_mut().map(|(prefix, _)| prefix)
    }

    pub fn into_prefix(self) -> Option<P> {
        self.inner.map(|(prefix, _)| prefix)
    }

    pub fn as_ref(&self) -> Option<&T> {
        self.inner.as_ref().map(|(_, inner)| inner)
    }

    pub fn as_mut(&mut self) -> Option<&mut T> {
        self.inner.as_mut().map(|(_, inner)| inner)
    }

    pub fn into_inner(self) -> Option<T> {
        self.inner.map(|(_, inner)| inner)
    }

    pub fn as_parts(&self) -> Option<&(P, T)> {
        self.inner.as_ref()
    }

    pub fn as_parts_mut(&mut self) -> Option<&mut (P, T)> {
        self.inner.as_mut()
    }

    pub fn into_parts(self) -> Option<(P, T)> {
        self.inner
    }

    pub fn into_prefix_iter(self) -> core::option::IntoIter<P> {
        self.into_prefix().into_iter()
    }

    pub fn prefix_iter(&self) -> core::option::IntoIter<&P> {
        self.as_prefix().into_iter()
    }

    pub fn prefix_iter_mut(&mut self) -> core::option::IntoIter<&mut P> {
        self.as_prefix_mut().into_iter()
    }

    pub fn iter(&self) -> core::option::IntoIter<&T> {
        self.as_ref().into_iter()
    }

    pub fn iter_mut(&mut self) -> core::option::IntoIter<&mut T> {
        self.as_mut().into_iter()
    }

    pub fn into_parts_iter(self) -> core::option::IntoIter<(P, T)> {
        self.inner.into_iter()
    }

    pub fn parts_iter(&self) -> core::option::Iter<'_, (P, T)> {
        self.inner.iter()
    }

    pub fn parts_iter_mut(&mut self) -> core::option::IterMut<'_, (P, T)> {
        self.inner.iter_mut()
    }
}

impl<P, T> Default for Maybe<P, T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<P, T> From<Option<(P, T)>> for Maybe<P, T> {
    fn from(inner: Option<(P, T)>) -> Self {
        Maybe { inner }
    }
}

impl<P: Default, T> From<Option<T>> for Maybe<P, T> {
    fn from(inner: Option<T>) -> Self {
        Maybe {
            inner: inner.map(|t| (P::default(), t))
        }
    }
}

impl<P, T> From<(P, T)> for Maybe<P, T> {
    fn from(parts: (P, T)) -> Self {
        Maybe { inner: parts.into() }
    }
}

impl<P: Default, T> From<T> for Maybe<P, T> {
    fn from(tail: T) -> Self {
        let head = P::default();
        let inner = (head, tail);

        Maybe::from(inner)
    }
}

impl<P, T> IntoIterator for Maybe<P, T> {
    type Item = T;
    type IntoIter = core::option::IntoIter<T>;

    fn into_iter(self) -> Self::IntoIter {
        self.into_inner().into_iter()
    }
}

impl<'a, P, T> IntoIterator for &'a Maybe<P, T> {
    type Item = &'a T;
    type IntoIter = core::option::IntoIter<&'a T>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<'a, P, T> IntoIterator for &'a mut Maybe<P, T> {
    type Item = &'a mut T;
    type IntoIter = core::option::IntoIter<&'a mut T>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter_mut()
    }
}

impl<P, T> Deref for Maybe<P, T> {
    type Target = Option<(P, T)>;

    fn deref(&self) -> &Self::Target {
        &self.inner
    }
}

impl<P, T> DerefMut for Maybe<P, T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.inner
    }
}

impl<P, T> Debug for Maybe<P, T>
where
    P: Debug,
    T: Debug,
{
    fn fmt(&self, formatter: &mut Formatter<'_>) -> fmt::Result {
        self.inner.fmt(formatter)
    }
}

impl<P, T> Display for Maybe<P, T>
where
    P: ToTokens,
    T: ToTokens,
{
    fn fmt(&self, formatter: &mut Formatter<'_>) -> fmt::Result {
        pretty_print_tokens(self, formatter)
    }
}

impl<P, T> FromStr for Maybe<P, T>
where
    P: Parse,
    T: Parse,
{
    type Err = Error;

    fn from_str(string: &str) -> Result<Self> {
        syn::parse_str(string)
    }
}

impl<P, T> Parse for Maybe<P, T>
where
    P: Parse,
    T: Parse,
{
    fn parse(input: ParseStream<'_>) -> Result<Self> {
        // Unfortunately, it's not possible to use `Peek` at the type level,
        // because `ParseBuffer::peek()` as well as `Lookahead1::peek()`
        // expect a function, of which the type cannot be named. So, we hack
        // this limitation around by attempting a full parse of the prefix.
        let fork = input.fork();

        if let Ok(prefix) = fork.parse::<P>() {
            input.advance_to(&fork);

            let inner: T = input.parse()?;

            Ok(Maybe {
                inner: Some((prefix, inner)),
            })
        } else {
            Ok(Self::default())
        }
    }
}

impl<P, T> ToTokens for Maybe<P, T>
where
    P: ToTokens,
    T: ToTokens,
{
    fn to_tokens(&self, tokens: &mut TokenStream) {
        if let Some((head, tail)) = &self.inner {
            head.to_tokens(&mut *tokens);
            tail.to_tokens(&mut *tokens);
        }
    }
}

/// Parses a subexpression inside parentheses.
///
/// ```rust
/// # use parsel::parse_quote;
/// # use parsel::ast::{LitInt, Paren};
/// let answer: Paren<LitInt> = parse_quote!{ (42) };
///
/// assert_eq!(answer.into_inner(), LitInt::from(42));
/// ```
/// ```rust,should_panic
/// # use parsel::parse_quote;
/// # use parsel::ast::{LitInt, Paren};
/// let answer: Paren<LitInt> = parse_quote!{ 42 };
/// ```
/// ```rust
/// # use parsel::{quote, parse_quote, ToTokens};
/// # use parsel::ast::{LitInt, Paren};
/// let answer: Paren<LitInt> = LitInt::from(43).into();
///
/// assert_eq!(
///     answer.to_token_stream().to_string(),
///     quote::quote!{(43)}.to_string(),
/// );
/// ```
#[derive(Clone, Copy, Default, PartialEq, Eq, Hash, Debug)]
pub struct Paren<T> {
    parens: token::Paren,
    inner: T,
}

impl<T> Paren<T> {
    pub const fn new(inner: T, span: Span) -> Self {
        let parens = token::Paren { span };
        Paren { parens, inner }
    }

    pub fn into_inner(self) -> T {
        self.inner
    }

    pub fn as_parens(&self) -> &token::Paren {
        &self.parens
    }

    pub fn into_parens(self) -> token::Paren {
        self.parens
    }

    pub fn as_parts(&self) -> (&token::Paren, &T) {
        let Paren { parens, inner } = self;
        (parens, inner)
    }

    pub fn into_parts(self) -> (token::Paren, T) {
        let Paren { parens, inner } = self;
        (parens, inner)
    }
}

impl<T: Spanned> From<T> for Paren<T> {
    fn from(inner: T) -> Self {
        let parens = token::Paren(inner.span());
        Paren { parens, inner }
    }
}

impl<T> From<(token::Paren, T)> for Paren<T> {
    fn from((parens, inner): (token::Paren, T)) -> Self {
        Paren { parens, inner }
    }
}

/// Can't be `DerefMut` because of the span
impl<T> Deref for Paren<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &self.inner
    }
}

impl<T> AsRef<T> for Paren<T> {
    fn as_ref(&self) -> &T {
        &self.inner
    }
}

impl<T: ToTokens> Display for Paren<T> {
    fn fmt(&self, formatter: &mut Formatter<'_>) -> fmt::Result {
        pretty_print_tokens(self, formatter)
    }
}

impl<T: Parse> FromStr for Paren<T> {
    type Err = Error;

    fn from_str(string: &str) -> Result<Self> {
        syn::parse_str(string)
    }
}

impl<T: Parse> Parse for Paren<T> {
    fn parse(input: ParseStream<'_>) -> Result<Self> {
        let contents;
        let parens = syn::parenthesized!(contents in input);
        let inner = contents.parse()?;

        Ok(Paren { parens, inner })
    }
}

impl<T: ToTokens> ToTokens for Paren<T> {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        self.parens.surround(tokens, |ts| self.inner.to_tokens(ts));
    }
}

/// Parses a subexpression inside square brackets.
///
/// ```rust
/// # use parsel::parse_quote;
/// # use parsel::ast::{LitBool, Bracket};
/// let array: Bracket<LitBool> = parse_quote!([true]);
///
/// assert_eq!(array.into_inner(), LitBool::from(true));
/// ```
/// ```rust,should_panic
/// # use parsel::parse_quote;
/// # use parsel::ast::{LitBool, Bracket};
/// let array: Bracket<LitBool> = parse_quote!(true);
/// ```
/// ```rust
/// # use parsel::{quote, parse_quote, ToTokens};
/// # use parsel::ast::{ident, LitInt, Ident, Bracket};
/// let expr: Bracket<Ident> = ident("hey_ho").into();
///
/// assert_eq!(
///     expr.to_token_stream().to_string(),
///     quote::quote!([hey_ho]).to_string(),
/// );
/// ```
#[derive(Clone, Copy, Default, PartialEq, Eq, Hash, Debug)]
pub struct Bracket<T> {
    brackets: token::Bracket,
    inner: T,
}

impl<T> Bracket<T> {
    pub const fn new(inner: T, span: Span) -> Self {
        let brackets = token::Bracket { span };
        Bracket { brackets, inner }
    }

    pub fn into_inner(self) -> T {
        self.inner
    }

    pub fn as_brackets(&self) -> &token::Bracket {
        &self.brackets
    }

    pub fn into_brackets(self) -> token::Bracket {
        self.brackets
    }

    pub fn as_parts(&self) -> (&token::Bracket, &T) {
        let Bracket { brackets, inner } = self;
        (brackets, inner)
    }

    pub fn into_parts(self) -> (token::Bracket, T) {
        let Bracket { brackets, inner } = self;
        (brackets, inner)
    }
}

impl<T: Spanned> From<T> for Bracket<T> {
    fn from(inner: T) -> Self {
        let brackets = token::Bracket(inner.span());
        Bracket { brackets, inner }
    }
}

impl<T> From<(token::Bracket, T)> for Bracket<T> {
    fn from((brackets, inner): (token::Bracket, T)) -> Self {
        Bracket { brackets, inner }
    }
}

/// Can't be `DerefMut` because of the span
impl<T> Deref for Bracket<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &self.inner
    }
}

impl<T> AsRef<T> for Bracket<T> {
    fn as_ref(&self) -> &T {
        &self.inner
    }
}

impl<T: ToTokens> Display for Bracket<T> {
    fn fmt(&self, formatter: &mut Formatter<'_>) -> fmt::Result {
        pretty_print_tokens(self, formatter)
    }
}

impl<T: Parse> FromStr for Bracket<T> {
    type Err = Error;

    fn from_str(string: &str) -> Result<Self> {
        syn::parse_str(string)
    }
}

impl<T: Parse> Parse for Bracket<T> {
    fn parse(input: ParseStream<'_>) -> Result<Self> {
        let contents;
        let brackets = syn::bracketed!(contents in input);
        let inner = contents.parse()?;

        Ok(Bracket { brackets, inner })
    }
}

impl<T: ToTokens> ToTokens for Bracket<T> {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        self.brackets.surround(tokens, |ts| self.inner.to_tokens(ts));
    }
}

/// Parses a subexpression inside curly braces.
///
/// ```rust
/// # use parsel::{parse_quote, Parse};
/// # use parsel::ast::{token, Token, Lit, LitStr, Brace};
/// #[derive(PartialEq, Eq, Debug, Parse)]
/// struct KeyValue {
///     key: LitStr,
///     eq: Token![=],
///     value: Lit,
/// }
/// let map: Brace<KeyValue> = parse_quote!({ "age" = 27 });
/// let key_value: KeyValue = parse_quote!("age" = 27);
///
/// assert_eq!(map.into_inner(), key_value);
/// ```
/// ```rust,should_panic
/// # use parsel::parse_quote;
/// # use parsel::ast::{Ident, Brace};
/// let set: Brace<Ident> = parse_quote!(my_ident);
/// ```
/// ```rust
/// # use parsel::{quote, parse_quote, ToTokens};
/// # use parsel::ast::{LitBool, Brace};
/// let block: Brace<LitBool> = LitBool::from(false).into();
///
/// assert_eq!(
///     block.to_token_stream().to_string(),
///     quote::quote!({ false }).to_string(),
/// );
/// ```
#[derive(Clone, Copy, Default, PartialEq, Eq, Hash, Debug)]
pub struct Brace<T> {
    braces: token::Brace,
    inner: T,
}

impl<T> Brace<T> {
    pub const fn new(inner: T, span: Span) -> Self {
        let braces = token::Brace { span };
        Brace { braces, inner }
    }

    pub fn into_inner(self) -> T {
        self.inner
    }

    pub fn as_braces(&self) -> &token::Brace {
        &self.braces
    }

    pub fn into_braces(self) -> token::Brace {
        self.braces
    }

    pub fn as_parts(&self) -> (&token::Brace, &T) {
        let Brace { braces, inner } = self;
        (braces, inner)
    }

    pub fn into_parts(self) -> (token::Brace, T) {
        let Brace { braces, inner } = self;
        (braces, inner)
    }
}

impl<T: Spanned> From<T> for Brace<T> {
    fn from(inner: T) -> Self {
        let braces = token::Brace(inner.span());
        Brace { braces, inner }
    }
}

impl<T> From<(token::Brace, T)> for Brace<T> {
    fn from((braces, inner): (token::Brace, T)) -> Self {
        Brace { braces, inner }
    }
}

/// Can't be `DerefMut` because of the span
impl<T> Deref for Brace<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &self.inner
    }
}

impl<T> AsRef<T> for Brace<T> {
    fn as_ref(&self) -> &T {
        &self.inner
    }
}

impl<T: ToTokens> Display for Brace<T> {
    fn fmt(&self, formatter: &mut Formatter<'_>) -> fmt::Result {
        pretty_print_tokens(self, formatter)
    }
}

impl<T: Parse> FromStr for Brace<T> {
    type Err = Error;

    fn from_str(string: &str) -> Result<Self> {
        syn::parse_str(string)
    }
}

impl<T: Parse> Parse for Brace<T> {
    fn parse(input: ParseStream<'_>) -> Result<Self> {
        let contents;
        let braces = syn::braced!(contents in input);
        let inner = contents.parse()?;

        Ok(Brace { braces, inner })
    }
}

impl<T: ToTokens> ToTokens for Brace<T> {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        self.braces.surround(tokens, |ts| self.inner.to_tokens(ts));
    }
}

/// Parses a given production repeatedly, separated by punctuation.
/// Optional trailing punctuation is allowed, and the entire token
/// stream must consist of interleaved representations of `T` and `P`.
/// (Thus, this is generally only useful within a delimited group.)
///
/// ```rust
/// # use core::convert::TryFrom;
/// # use parsel::parse_quote;
/// # use parsel::ast::{Token, Lit, Punctuated};
/// let items: Punctuated<Lit, Token![,]> = parse_quote!(44, true, "str liter", 5.55,);
/// let items: Vec<Lit> = items.into_iter().collect();
///
/// assert_eq!(items, [
///     Lit::from(44_u128),
///     Lit::from(true),
///     Lit::from("str liter"),
///     Lit::try_from(5.55).unwrap(),
/// ]);
/// ```
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct Punctuated<T, P> {
    inner: syn::punctuated::Punctuated<T, P>,
}

impl<T, P> Punctuated<T, P> {
    pub const fn new() -> Self {
        Punctuated {
            inner: syn::punctuated::Punctuated::new()
        }
    }

    pub fn is_empty(&self) -> bool {
        self.inner.is_empty()
    }

    pub fn len(&self) -> usize {
        self.inner.len()
    }

    pub fn into_inner(self) -> syn::punctuated::Punctuated<T, P> {
        self.inner
    }

    pub fn iter(&self) -> Iter<'_, T> {
        self.inner.iter()
    }

    pub fn iter_mut(&mut self) -> IterMut<'_, T> {
        self.inner.iter_mut()
    }

    pub fn into_pairs(self) -> IntoPairs<T, P> {
        self.inner.into_pairs()
    }

    pub fn pairs(&self) -> Pairs<'_, T, P> {
        self.inner.pairs()
    }

    pub fn pairs_mut(&mut self) -> PairsMut<'_, T, P> {
        self.inner.pairs_mut()
    }
}

impl<T, P> Default for Punctuated<T, P> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T, P> From<syn::punctuated::Punctuated<T, P>> for Punctuated<T, P> {
    fn from(inner: syn::punctuated::Punctuated<T, P>) -> Self {
        Punctuated { inner }
    }
}

impl<T, P> From<Punctuated<T, P>> for syn::punctuated::Punctuated<T, P> {
    fn from(punctuated: Punctuated<T, P>) -> Self {
        punctuated.inner
    }
}

impl<T, P> Deref for Punctuated<T, P> {
    type Target = syn::punctuated::Punctuated<T, P>;

    fn deref(&self) -> &Self::Target {
        &self.inner
    }
}

impl<T, P> DerefMut for Punctuated<T, P> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.inner
    }
}

impl<T, P> AsRef<syn::punctuated::Punctuated<T, P>> for Punctuated<T, P> {
    fn as_ref(&self) -> &syn::punctuated::Punctuated<T, P> {
        &self.inner
    }
}

impl<T, P> AsMut<syn::punctuated::Punctuated<T, P>> for Punctuated<T, P> {
    fn as_mut(&mut self) -> &mut syn::punctuated::Punctuated<T, P> {
        &mut self.inner
    }
}

impl<T, P> Borrow<syn::punctuated::Punctuated<T, P>> for Punctuated<T, P> {
    fn borrow(&self) -> &syn::punctuated::Punctuated<T, P> {
        &self.inner
    }
}

impl<T, P> BorrowMut<syn::punctuated::Punctuated<T, P>> for Punctuated<T, P> {
    fn borrow_mut(&mut self) -> &mut syn::punctuated::Punctuated<T, P> {
        &mut self.inner
    }
}

impl<T, P> FromIterator<T> for Punctuated<T, P>
where
    P: Default,
{
    fn from_iter<I>(iter: I) -> Self
    where
        I: IntoIterator<Item = T>
    {
        Punctuated {
            inner: iter.into_iter().collect()
        }
    }
}

impl<T, P> FromIterator<Pair<T, P>> for Punctuated<T, P> {
    fn from_iter<I>(iter: I) -> Self
    where
        I: IntoIterator<Item = Pair<T, P>>
    {
        Punctuated {
            inner: iter.into_iter().collect()
        }
    }
}

impl<T, P> Extend<T> for Punctuated<T, P>
where
    P: Default,
{
    fn extend<I>(&mut self, iter: I)
    where
        I: IntoIterator<Item = T>
    {
        self.inner.extend(iter);
    }
}

impl<T, P> Extend<Pair<T, P>> for Punctuated<T, P> {
    fn extend<I>(&mut self, iter: I)
    where
        I: IntoIterator<Item = Pair<T, P>>
    {
        self.inner.extend(iter);
    }
}

impl<T, P> IntoIterator for Punctuated<T, P> {
    type Item = T;
    type IntoIter = IntoIter<T>;

    fn into_iter(self) -> Self::IntoIter {
        self.inner.into_iter()
    }
}

impl<'a, T, P> IntoIterator for &'a Punctuated<T, P> {
    type Item = &'a T;
    type IntoIter = Iter<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.inner.iter()
    }
}

impl<'a, T, P> IntoIterator for &'a mut Punctuated<T, P> {
    type Item = &'a mut T;
    type IntoIter = IterMut<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.inner.iter_mut()
    }
}

impl<T, P> Index<usize> for Punctuated<T, P> {
    type Output = T;

    fn index(&self, index: usize) -> &Self::Output {
        self.inner.index(index)
    }
}

impl<T, P> IndexMut<usize> for Punctuated<T, P> {
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        self.inner.index_mut(index)
    }
}

impl<T, P> Debug for Punctuated<T, P>
where
    T: Debug,
    P: Debug,
{
    fn fmt(&self, formatter: &mut Formatter<'_>) -> fmt::Result {
        self.inner.fmt(formatter)
    }
}

impl<T, P> Display for Punctuated<T, P>
where
    T: ToTokens,
    P: ToTokens,
{
    fn fmt(&self, formatter: &mut Formatter<'_>) -> fmt::Result {
        pretty_print_tokens(self, formatter)
    }
}

impl<T, P> FromStr for Punctuated<T, P>
where
    T: Parse,
    P: Parse,
{
    type Err = Error;

    fn from_str(string: &str) -> Result<Self> {
        syn::parse_str(string)
    }
}

impl<T, P> Parse for Punctuated<T, P>
where
    T: Parse,
    P: Parse,
{
    fn parse(input: ParseStream<'_>) -> Result<Self> {
        let inner = syn::punctuated::Punctuated::parse_terminated(input)?;
        Ok(Punctuated { inner })
    }
}

impl<T, P> ToTokens for Punctuated<T, P>
where
    T: ToTokens,
    P: ToTokens,
{
    fn to_tokens(&self, tokens: &mut TokenStream) {
        let Punctuated { inner } = self;
        inner.to_tokens(tokens);
    }
}

/// A convenience type alias for parsing several repeated items with no separator in between.
///
/// ```rust
/// # use core::convert::TryFrom;
/// # use parsel::{parse_quote, Parse, ToTokens};
/// # use parsel::ast::{ident, token};
/// # use parsel::ast::{Lit, LitBool, LitInt, LitFloat, Ident, Many};
/// #[derive(PartialEq, Eq, Debug, Parse, ToTokens)]
/// struct KeyValue {
///     key: Ident,
///     arrow: token::RArrow,
///     value: Lit,
/// }
///
/// let items: Many<KeyValue> = parse_quote!{
///     key_one -> 678
///     no_2    -> 2.718
///     third   -> false
/// };
/// let actual: Vec<KeyValue> = items.into_iter().collect();
/// let expected = vec![
///     KeyValue {
///         key: ident("key_one"),
///         arrow: Default::default(),
///         value: Lit::from(678_u128),
///     },
///     KeyValue {
///         key: ident("no_2"),
///         arrow: Default::default(),
///         value: Lit::try_from(2.718).unwrap(),
///     },
///     KeyValue {
///         key: ident("third"),
///         arrow: Default::default(),
///         value: Lit::from(false),
///     },
/// ];
/// assert_eq!(actual, expected);
/// ```
pub type Many<T> = Punctuated<T, NotEof>;

/// Parses a given production repeatedly, separated by punctuation.
/// Trailing punctuation is **not** allowed, and the production must
/// appear at least once in the input. Parsing stops gracefully once
/// there are no more separators left at the head of the input stream.
///
/// It can't be `Default` because that would mean an empty sequence.
///
/// ```rust
/// use parsel::Result;
/// use parsel::ast::{ident, LitInt, Ident, Separated, Many};
/// use parsel::ast::token::{Add, Colon2, Comma};
///
/// let mut sum: Separated<LitInt, Add> = parsel::parse_quote! {
///     1 + 2 + 4 + 8 + 16 + 32
/// };
/// sum.push_value(LitInt::from(64));
///
/// assert_eq!(sum.to_string(), "1 + 2 + 4 + 8 + 16 + 32 + 64");
///
/// let good_short: Separated<Ident, Colon2> = parsel::parse_quote!(one);
/// let good_short: Vec<_> = good_short.into_iter().collect();
/// let expected_short = vec![ident("one")];
/// assert_eq!(good_short, expected_short);
///
/// let good_long: Separated<Ident, Colon2> = parsel::parse_quote! {
///     root::module::Item
/// };
/// let good_long: Vec<_> = good_long.into_iter().collect();
/// let expected_long: Many<Ident> = parsel::parse_quote!(root module Item);
/// let expected_long: Vec<_> = expected_long.into_iter().collect();
/// assert_eq!(good_long, expected_long);
///
/// let bad_trailing: Result<Separated<Ident, Colon2>> = parsel::parse_str(r"
///     root::module::Item::
/// ");
/// assert!(bad_trailing.is_err());
///
/// let bad_empty: Result<Separated<Ident, Colon2>> = parsel::parse_str("");
/// assert!(bad_empty.is_err());
/// ```
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct Separated<T, P> {
    inner: syn::punctuated::Punctuated<T, P>,
}

impl<T, P> Separated<T, P> {
    pub fn len(&self) -> NonZeroUsize {
        NonZeroUsize::new(self.inner.len()).expect("empty Separated")
    }

    pub fn into_inner(self) -> syn::punctuated::Punctuated<T, P> {
        self.inner
    }

    pub fn first(&self) -> &T {
        self.inner.first().expect("empty Separated")
    }

    pub fn first_mut(&mut self) -> &mut T {
        self.inner.first_mut().expect("empty Separated")
    }

    pub fn last(&self) -> &T {
        self.inner.last().expect("empty Separated")
    }

    pub fn last_mut(&mut self) -> &mut T {
        self.inner.last_mut().expect("empty Separated")
    }

    /// `insert()` is allowed because it doesn't ever make the sequence
    /// empty, nor does it add trailing punctuation, so it doesn't violate
    /// the invariants of the type.
    pub fn insert(&mut self, index: usize, value: T)
    where
        P: Default
    {
        self.inner.insert(index, value);
    }

    /// `push()` is allowed because it doesn't ever make the sequence
    /// empty, nor does it add trailing punctuation, so it doesn't violate
    /// the invariants of the type.
    pub fn push(&mut self, punct: P, value: T) {
        self.inner.push_punct(punct);
        self.inner.push_value(value);
    }

    /// `push_value()` is allowed because it doesn't ever make the sequence
    /// empty, nor does it add trailing punctuation, so it doesn't violate
    /// the invariants of the type.
    pub fn push_value(&mut self, value: T)
    where
        P: Default,
    {
        self.push(P::default(), value);
    }

    pub fn iter(&self) -> Iter<'_, T> {
        self.inner.iter()
    }

    pub fn iter_mut(&mut self) -> IterMut<'_, T> {
        self.inner.iter_mut()
    }

    pub fn into_pairs(self) -> IntoPairs<T, P> {
        self.inner.into_pairs()
    }

    pub fn pairs(&self) -> Pairs<'_, T, P> {
        self.inner.pairs()
    }

    pub fn pairs_mut(&mut self) -> PairsMut<'_, T, P> {
        self.inner.pairs_mut()
    }

    /// Returns the first value and the remaining (punctuation, value) pairs.
    ///
    /// ```rust
    /// # use parsel::ast::{LitInt, Separated};
    /// # use parsel::ast::token::Comma;
    /// let singleton: Separated<LitInt, Comma> = parsel::parse_quote!(137);
    /// let (first, rest) = singleton.into_first_rest();
    /// assert_eq!(first, LitInt::from(137));
    /// assert_eq!(rest, []);
    ///
    /// let triplet: Separated<LitInt, Comma> = parsel::parse_quote!(731, 813, 139);
    /// let (first, rest) = triplet.into_first_rest();
    /// assert_eq!(first, LitInt::from(731));
    /// assert_eq!(rest, [
    ///     (Comma::default(), LitInt::from(813)),
    ///     (Comma::default(), LitInt::from(139)),
    /// ]);
    /// ```
    pub fn into_first_rest(self) -> (T, Vec<(P, T)>) {
        // this subtraction cannot overflow: `self` is never empty
        let mut pairs = Vec::with_capacity(self.len().get() - 1);
        let mut iter = self.into_pairs();
        let pair = iter.next().expect("empty Separated");

        let (first, mut punct) = match pair {
            Pair::Punctuated(value, punct) => (value, punct),
            Pair::End(value) => return (value, pairs),
        };

        for pair in iter {
            match pair {
                Pair::Punctuated(value, next) => {
                    pairs.push((punct, value));
                    punct = next;
                }
                Pair::End(value) => {
                    pairs.push((punct, value));
                    break;
                }
            }
        }

        (first, pairs)
    }

    /// Returns the last value and the preceding (value, punctuation) pairs.
    ///
    /// ```rust
    /// # use parsel::ast::{LitChar, Separated};
    /// # use parsel::ast::token::Semi;
    /// let singleton: Separated<LitChar, Semi> = parsel::parse_quote!('W');
    /// let (last, rest) = singleton.into_last_rest();
    /// assert_eq!(last, LitChar::from('W'));
    /// assert_eq!(rest, []);
    ///
    /// let triplet: Separated<LitChar, Semi> = parsel::parse_quote!('"'; 'é'; '\'');
    /// let (last, rest) = triplet.into_last_rest();
    /// assert_eq!(last, LitChar::from('\''));
    /// assert_eq!(rest, [
    ///     (LitChar::from('"'), Semi::default()),
    ///     (LitChar::from('é'), Semi::default()),
    /// ]);
    /// ```
    pub fn into_last_rest(self) -> (T, Vec<(T, P)>) {
        // this subtraction cannot overflow: `self` is never empty
        let mut pairs = Vec::with_capacity(self.len().get() - 1);

        for pair in self.into_pairs() {
            match pair {
                Pair::Punctuated(value, punct) => {
                    pairs.push((value, punct));
                }
                Pair::End(value) => {
                    return (value, pairs);
                }
            }
        }

        unreachable!("empty Separated or trailing punctuation")
    }
}

impl<T, P> TryFrom<syn::punctuated::Punctuated<T, P>> for Separated<T, P>
where
    T: ToTokens,
    P: ToTokens,
{
    type Error = Error;

    fn try_from(inner: syn::punctuated::Punctuated<T, P>) -> Result<Self> {
        if inner.empty_or_trailing() {
            Err(Error::new_spanned(inner, "empty sequence or trailing punctuation"))
        } else {
            Ok(Separated { inner })
        }
    }
}

impl<T, P> From<Separated<T, P>> for syn::punctuated::Punctuated<T, P> {
    fn from(separated: Separated<T, P>) -> Self {
        separated.inner
    }
}

/// It can't be `DerefMut`, because then users could `.pop()` the last
/// remaining item, resulting in an empty `Separated`. They could push
/// a trailing separator, too, which also violates internal invariants.
impl<T, P> Deref for Separated<T, P> {
    type Target = syn::punctuated::Punctuated<T, P>;

    fn deref(&self) -> &Self::Target {
        &self.inner
    }
}

/// See the documentation of `impl Deref for Separated` for why this
/// can't be `AsMut`.
impl<T, P> AsRef<syn::punctuated::Punctuated<T, P>> for Separated<T, P> {
    fn as_ref(&self) -> &syn::punctuated::Punctuated<T, P> {
        &self.inner
    }
}

/// See the documentation of `impl Deref for Separated` for why this
/// can't be `BorrowMut`.
impl<T, P> Borrow<syn::punctuated::Punctuated<T, P>> for Separated<T, P> {
    fn borrow(&self) -> &syn::punctuated::Punctuated<T, P> {
        &self.inner
    }
}

/// `Extend<Pair<T, P>>` is not provided because it requires either an empty
/// sequence or one with trailing punctuation.
///
/// `FromIterator` impls are missing because the input iterator could be empty.
impl<T, P> Extend<T> for Separated<T, P>
where
    P: Default,
{
    fn extend<I>(&mut self, iter: I)
    where
        I: IntoIterator<Item = T>
    {
        self.inner.extend(iter);
    }
}

/// `Extend<(P, T)>` can be implemented because it never causes the sequence
/// to become empty, nor does it add any trailing punctuation.
impl<T, P> Extend<(P, T)> for Separated<T, P> {
    fn extend<I>(&mut self, iter: I)
    where
        I: IntoIterator<Item = (P, T)>
    {
        for (punct, value) in iter {
            self.push(punct, value);
        }
    }
}

impl<T, P> IntoIterator for Separated<T, P> {
    type Item = T;
    type IntoIter = IntoIter<T>;

    fn into_iter(self) -> Self::IntoIter {
        self.inner.into_iter()
    }
}

impl<'a, T, P> IntoIterator for &'a Separated<T, P> {
    type Item = &'a T;
    type IntoIter = Iter<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.inner.iter()
    }
}

impl<'a, T, P> IntoIterator for &'a mut Separated<T, P> {
    type Item = &'a mut T;
    type IntoIter = IterMut<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.inner.iter_mut()
    }
}

impl<T, P> Index<usize> for Separated<T, P> {
    type Output = T;

    fn index(&self, index: usize) -> &Self::Output {
        self.inner.index(index)
    }
}

impl<T, P> IndexMut<usize> for Separated<T, P> {
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        self.inner.index_mut(index)
    }
}

impl<T, P> Debug for Separated<T, P>
where
    T: Debug,
    P: Debug,
{
    fn fmt(&self, formatter: &mut Formatter<'_>) -> fmt::Result {
        self.inner.fmt(formatter)
    }
}

impl<T, P> Display for Separated<T, P>
where
    T: ToTokens,
    P: ToTokens,
{
    fn fmt(&self, formatter: &mut Formatter<'_>) -> fmt::Result {
        pretty_print_tokens(self, formatter)
    }
}

impl<T, P> FromStr for Separated<T, P>
where
    T: Parse,
    P: Parse,
{
    type Err = Error;

    fn from_str(string: &str) -> Result<Self> {
        syn::parse_str(string)
    }
}

impl<T, P> Parse for Separated<T, P>
where
    T: Parse,
    P: Parse,
{
    fn parse(input: ParseStream<'_>) -> Result<Self> {
        let head: T = input.parse()?;
        let mut inner = syn::punctuated::Punctuated::new();

        inner.push_value(head);

        loop {
            let fork = input.fork();

            if let Ok(punct) = fork.parse::<P>() {
                input.advance_to(&fork);

                let value: T = input.parse()?;
                inner.push_punct(punct);
                inner.push_value(value);
            } else {
                break;
            }
        }

        Ok(Separated { inner })
    }
}

impl<T, P> ToTokens for Separated<T, P>
where
    T: ToTokens,
    P: ToTokens,
{
    fn to_tokens(&self, tokens: &mut TokenStream) {
        let Separated { inner } = self;
        inner.to_tokens(tokens);
    }
}

/// Parses 0 or more consecutive occurrences of the subproduction.
/// Unlike [`Many`](type.Many.html), this does **not** require the
/// input to consist entirely of repeats of the subproduction.
///
/// ```rust
/// # use parsel::{Error, Result, FromStr, Display, Parse, ToTokens};
/// # use parsel::ast::{word, Word, LitInt, Any};
/// #
/// #[derive(PartialEq, Eq, Debug, FromStr, Display, Parse, ToTokens)]
/// struct WordsAndNumbers {
///     words: Any<Word>,
///     numbers: Any<LitInt>,
/// }
///
/// let empty: WordsAndNumbers = "".parse()?;
/// assert_eq!(*empty.words, &[] as &[Word]);
/// assert_eq!(*empty.numbers, &[] as &[LitInt]);
///
/// let one_word: WordsAndNumbers = "one_word".parse()?;
/// assert_eq!(*one_word.words, [word("one_word")]);
/// assert_eq!(*one_word.numbers, &[] as &[LitInt]);
///
/// let many_words: WordsAndNumbers = "one two three".parse()?;
/// assert_eq!(*many_words.words, ["one", "two", "three"].map(word));
/// assert_eq!(*many_words.numbers, &[] as &[LitInt]);
///
/// let one_number: WordsAndNumbers = "777 ".parse()?;
/// assert_eq!(*one_number.words, &[] as &[Word]);
/// assert_eq!(*one_number.numbers, [LitInt::from(777)]);
///
/// let many_numbers: WordsAndNumbers = "88 777  99999".parse()?;
/// assert_eq!(*many_numbers.words, &[] as &[Word]);
/// assert_eq!(*many_numbers.numbers, [88, 777, 99999].map(LitInt::from));
///
/// let mixed: WordsAndNumbers = "hello_world someident 222 333".parse()?;
/// assert_eq!(*mixed.words, ["hello_world", "someident"].map(word));
/// assert_eq!(*mixed.numbers, [222, 333].map(LitInt::from));
///
/// let bad: Result<WordsAndNumbers> = "word 3456 more_words".parse();
/// assert!(bad.is_err());
/// #
/// # Ok::<(), Error>(())
/// ```
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct Any<T> {
    inner: Vec<T>,
}

impl<T> Any<T> {
    pub const fn new() -> Self {
        Any {
            inner: Vec::new(),
        }
    }

    pub fn into_inner(self) -> Vec<T> {
        self.inner
    }

    pub fn len(&self) -> usize {
        self.inner.len()
    }

    pub fn is_empty(&self) -> bool {
        self.inner.is_empty()
    }

    pub fn get<I>(&self, index: I) -> Option<&I::Output>
    where
        I: SliceIndex<[T]>
    {
        self.inner.get(index)
    }

    pub fn get_mut<I>(&mut self, index: I) -> Option<&mut I::Output>
    where
        I: SliceIndex<[T]>
    {
        self.inner.get_mut(index)
    }

    pub fn iter(&self) -> core::slice::Iter<'_, T> {
        self.inner.iter()
    }

    pub fn iter_mut(&mut self) -> core::slice::IterMut<'_, T> {
        self.inner.iter_mut()
    }
}

impl<T> Default for Any<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T> From<Vec<T>> for Any<T> {
    fn from(inner: Vec<T>) -> Self {
        Any { inner }
    }
}

impl<T> From<Any<T>> for Vec<T> {
    fn from(value: Any<T>) -> Self {
        value.inner
    }
}

impl<T> Deref for Any<T> {
    type Target = Vec<T>;

    fn deref(&self) -> &Self::Target {
        &self.inner
    }
}

impl<T> DerefMut for Any<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.inner
    }
}

impl<T> AsRef<[T]> for Any<T> {
    fn as_ref(&self) -> &[T] {
        &self.inner
    }
}

impl<T> AsRef<Vec<T>> for Any<T> {
    fn as_ref(&self) -> &Vec<T> {
        &self.inner
    }
}

impl<T> AsMut<[T]> for Any<T> {
    fn as_mut(&mut self) -> &mut [T] {
        &mut self.inner
    }
}

impl<T> AsMut<Vec<T>> for Any<T> {
    fn as_mut(&mut self) -> &mut Vec<T> {
        &mut self.inner
    }
}

impl<T> Borrow<[T]> for Any<T> {
    fn borrow(&self) -> &[T] {
        &self.inner
    }
}

impl<T> Borrow<Vec<T>> for Any<T> {
    fn borrow(&self) -> &Vec<T> {
        &self.inner
    }
}

impl<T> BorrowMut<[T]> for Any<T> {
    fn borrow_mut(&mut self) -> &mut [T] {
        &mut self.inner
    }
}

impl<T> BorrowMut<Vec<T>> for Any<T> {
    fn borrow_mut(&mut self) -> &mut Vec<T> {
        &mut self.inner
    }
}

impl<T> FromIterator<T> for Any<T> {
    fn from_iter<I>(iter: I) -> Self
    where
        I: IntoIterator<Item = T>
    {
        Any {
            inner: iter.into_iter().collect(),
        }
    }
}

impl<T> Extend<T> for Any<T> {
    fn extend<I>(&mut self, iter: I)
    where
        I: IntoIterator<Item = T>
    {
        self.inner.extend(iter);
    }
}

impl<T> IntoIterator for Any<T> {
    type Item = T;
    type IntoIter = std::vec::IntoIter<T>;

    fn into_iter(self) -> Self::IntoIter {
        self.inner.into_iter()
    }
}

impl<'a, T> IntoIterator for &'a Any<T> {
    type Item = &'a T;
    type IntoIter = core::slice::Iter<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.inner.iter()
    }
}

impl<'a, T> IntoIterator for &'a mut Any<T> {
    type Item = &'a mut T;
    type IntoIter = core::slice::IterMut<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.inner.iter_mut()
    }
}

impl<T, I> Index<I> for Any<T>
where
    I: SliceIndex<[T]>
{
    type Output = <I as SliceIndex<[T]>>::Output;

    fn index(&self, index: I) -> &Self::Output {
        &self.inner[index]
    }
}

impl<T, I> IndexMut<I> for Any<T>
where
    I: SliceIndex<[T]>
{
    fn index_mut(&mut self, index: I) -> &mut Self::Output {
        &mut self.inner[index]
    }
}

impl<T> Debug for Any<T>
where
    T: Debug
{
    fn fmt(&self, formatter: &mut Formatter<'_>) -> fmt::Result {
        Debug::fmt(&self.inner, formatter)
    }
}

impl<T> Display for Any<T>
where
    T: ToTokens
{
    fn fmt(&self, formatter: &mut Formatter<'_>) -> fmt::Result {
        pretty_print_tokens(self, formatter)
    }
}

impl<T> FromStr for Any<T>
where
    T: Parse
{
    type Err = Error;

    fn from_str(string: &str) -> Result<Self> {
        syn::parse_str(string)
    }
}

impl<T> Parse for Any<T>
where
    T: Parse
{
    fn parse(input: ParseStream<'_>) -> Result<Self> {
        let mut inner = Vec::new();

        loop {
            let fork = input.fork();

            if let Ok(item) = fork.parse() {
                inner.push(item);
                input.advance_to(&fork);
            } else {
                break;
            }
        }

        Ok(Any { inner })
    }
}

impl<T> ToTokens for Any<T>
where
    T: ToTokens
{
    fn to_tokens(&self, tokens: &mut TokenStream) {
        tokens.append_all(&self.inner);
    }
}

macro_rules! impl_literal {
    ($($raw:ty => $name:ident;)*) => {$(
        #[derive(Clone, Debug)]
        pub struct $name {
            value: $raw,
            span: Span,
        }

        impl $name {
            pub fn new(value: $raw, span: Span) -> Self {
                $name { value, span }
            }

            pub fn value(&self) -> $raw {
                self.value.clone()
            }

            pub fn into_inner(self) -> $raw {
                self.value
            }

            pub fn span(&self) -> Span {
                self.span
            }

            pub fn set_span(&mut self, span: Span) {
                self.span = span;
            }
        }

        impl Default for $name {
            fn default() -> Self {
                $name {
                    value: <$raw>::default(),
                    span: Span::call_site(),
                }
            }
        }

        impl From<$raw> for $name {
            fn from(value: $raw) -> Self {
                let span = Span::call_site();
                $name { value, span }
            }
        }

        impl From<$name> for $raw {
            fn from(lit: $name) -> $raw {
                lit.value
            }
        }

        impl From<$name> for TokenTree {
            fn from(lit: $name) -> TokenTree {
                lit.token().into()
            }
        }

        impl Borrow<$raw> for $name {
            fn borrow(&self) -> &$raw {
                &self.value
            }
        }

        impl PartialEq<Self> for $name {
            fn eq(&self, other: &Self) -> bool {
                self.value == other.value
            }
        }

        impl PartialEq<$raw> for $name {
            fn eq(&self, value: &$raw) -> bool {
                self.value == *value
            }
        }

        impl Eq for $name {}

        impl PartialOrd<Self> for $name {
            fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
                self.cmp(other).into()
            }
        }

        impl PartialOrd<$raw> for $name {
            fn partial_cmp(&self, other: &$raw) -> Option<Ordering> {
                self.value.cmp(other).into()
            }
        }

        impl Ord for $name {
            fn cmp(&self, other: &Self) -> Ordering {
                self.value.cmp(&other.value)
            }
        }

        impl Hash for $name {
            fn hash<H: Hasher>(&self, state: &mut H) {
                self.value.hash(state);
            }
        }

        impl Display for $name {
            fn fmt(&self, formatter: &mut Formatter<'_>) -> fmt::Result {
                Display::fmt(&self.token(), formatter)
            }
        }

        impl FromStr for $name {
            type Err = Error;

            fn from_str(string: &str) -> Result<Self> {
                syn::parse_str(string)
            }
        }

        impl ToTokens for $name {
            fn to_tokens(&self, tokens: &mut TokenStream) {
                tokens.append(self.token());
            }
        }
    )*}
}

impl_literal!{
    bool        => LitBool;
    u8          => LitByte;
    i128        => LitInt;
    u128        => LitUint;
    NotNan<f64> => LitFloat;
    char        => LitChar;
    String      => LitStr;
    Vec<u8>     => LitByteStr;
}

impl LitBool {
    pub fn token(&self) -> Ident {
        let repr = if self.value { "true" } else { "false" };
        Ident::new(repr, self.span)
    }
}

impl LitByte {
    /// This method is non-trivial, so here is a doc-test for it.
    ///
    /// ```rust
    /// # use parsel::ast::LitByte;
    /// # use parsel::parse_quote;
    /// let byte_a: LitByte = parse_quote!(b'a');
    /// let token_a = byte_a.token();
    /// assert_eq!(token_a.to_string(), r"b'a'");
    ///
    /// let byte_nul: LitByte = parse_quote!(b'\x00');
    /// let token_nul = byte_nul.token();
    /// assert_eq!(token_nul.to_string(), r"b'\x00'");
    ///
    /// let byte_tilde: LitByte = parse_quote!(b'~');
    /// let token_tilde = byte_tilde.token();
    /// assert_eq!(token_tilde.to_string(), r"b'~'");
    ///
    /// let byte_space: LitByte = parse_quote!(b' ');
    /// let token_space = byte_space.token();
    /// assert_eq!(token_space.to_string(), r"b' '");
    ///
    /// let byte_del: LitByte = parse_quote!(b'\x7f');
    /// let token_del = byte_del.token();
    /// assert_eq!(token_del.to_string(), r"b'\x7f'");
    ///
    /// let byte_nonascii_80: LitByte = parse_quote!(b'\x80');
    /// let token_nonascii_80 = byte_nonascii_80.token();
    /// assert_eq!(token_nonascii_80.to_string(), r"b'\x80'");
    ///
    /// let byte_nonascii_ff: LitByte = parse_quote!(b'\xff');
    /// let token_nonascii_ff = byte_nonascii_ff.token();
    /// assert_eq!(token_nonascii_ff.to_string(), r"b'\xff'");
    /// ```
    pub fn token(&self) -> Literal {
        use core::{str, ascii};
        use std::io::{Write, Cursor};

        let mut buf: [u8; 8] = Default::default();
        let mut cursor = Cursor::new(buf.as_mut());
        let escape = ascii::escape_default(self.value);
        write!(cursor, r"b'{}'", escape).expect("cannot escape byte literal");

        // this is not going to overflow
        #[allow(clippy::cast_possible_truncation)]
        let len = cursor.position() as usize;
        let bytes = &buf[..len];
        let repr = str::from_utf8(bytes).expect("invalid UTF-8 in byte literal");
        let mut lit = Literal::from_str(repr).expect("unparseable byte literal");
        lit.set_span(self.span);
        lit
    }
}

impl LitInt {
    pub fn token(&self) -> Literal {
        let mut lit = Literal::i128_unsuffixed(self.value);
        lit.set_span(self.span);
        lit
    }
}

impl LitUint {
    pub fn token(&self) -> Literal {
        let mut lit = Literal::u128_unsuffixed(self.value);
        lit.set_span(self.span);
        lit
    }
}

impl LitFloat {
    pub fn token(&self) -> Literal {
        let mut lit = Literal::f64_unsuffixed(self.value.into_inner());
        lit.set_span(self.span);
        lit
    }
}

impl LitChar {
    pub fn token(&self) -> Literal {
        let mut lit = Literal::character(self.value);
        lit.set_span(self.span);
        lit
    }
}

impl LitStr {
    pub fn token(&self) -> Literal {
        let mut lit = Literal::string(&self.value);
        lit.set_span(self.span);
        lit
    }
}

impl LitByteStr {
    pub fn token(&self) -> Literal {
        let mut lit = Literal::byte_string(&self.value);
        lit.set_span(self.span);
        lit
    }
}

impl Copy for LitBool {}
impl Copy for LitByte {}
impl Copy for LitInt {}
impl Copy for LitUint {}
impl Copy for LitFloat {}
impl Copy for LitChar {}

impl From<syn::LitBool> for LitBool {
    fn from(lit: syn::LitBool) -> Self {
        LitBool::new(lit.value, lit.span)
    }
}

impl From<LitBool> for syn::LitBool {
    fn from(lit: LitBool) -> Self {
        syn::LitBool::new(lit.value, lit.span)
    }
}

impl From<syn::LitByte> for LitByte {
    fn from(lit: syn::LitByte) -> Self {
        LitByte::new(lit.value(), lit.span())
    }
}

impl From<LitByte> for syn::LitByte {
    fn from(lit: LitByte) -> Self {
        syn::LitByte::new(lit.value, lit.span)
    }
}

impl TryFrom<syn::LitInt> for LitInt {
    type Error = Error;

    fn try_from(lit: syn::LitInt) -> Result<Self> {
        let value: i128 = lit.base10_parse()?;
        let span = lit.span();
        Ok(LitInt::new(value, span))
    }
}

impl From<LitInt> for syn::LitInt {
    fn from(lit: LitInt) -> Self {
        lit.token().into()
    }
}

impl TryFrom<syn::LitInt> for LitUint {
    type Error = Error;

    fn try_from(lit: syn::LitInt) -> Result<Self> {
        let value: u128 = lit.base10_parse()?;
        let span = lit.span();
        Ok(LitUint::new(value, span))
    }
}

impl From<LitUint> for syn::LitInt {
    fn from(lit: LitUint) -> Self {
        lit.token().into()
    }
}

impl TryFrom<syn::LitFloat> for LitFloat {
    type Error = Error;

    fn try_from(lit: syn::LitFloat) -> Result<Self> {
        let value: NotNan<f64> = lit.base10_parse()?;
        let span = lit.span();
        Ok(LitFloat::new(value, span))
    }
}

impl From<LitFloat> for syn::LitFloat {
    fn from(lit: LitFloat) -> Self {
        lit.token().into()
    }
}

impl TryFrom<f64> for LitFloat {
    type Error = ordered_float::FloatIsNan;

    fn try_from(x: f64) -> core::result::Result<Self, Self::Error> {
        let value = NotNan::try_from(x)?;
        let span = Span::call_site();

        Ok(LitFloat { value, span })
    }
}

impl From<LitFloat> for f64 {
    fn from(lit: LitFloat) -> f64 {
        lit.value.into_inner()
    }
}

impl From<syn::LitChar> for LitChar {
    fn from(lit: syn::LitChar) -> Self {
        LitChar::new(lit.value(), lit.span())
    }
}

impl From<LitChar> for syn::LitChar {
    fn from(lit: LitChar) -> Self {
        syn::LitChar::new(lit.value, lit.span)
    }
}

impl From<syn::LitStr> for LitStr {
    fn from(lit: syn::LitStr) -> Self {
        LitStr::new(lit.value(), lit.span())
    }
}

impl From<LitStr> for syn::LitStr {
    fn from(lit: LitStr) -> Self {
        syn::LitStr::new(&lit.value, lit.span)
    }
}

impl From<&str> for LitStr {
    fn from(value: &str) -> LitStr {
        LitStr::new(value.to_owned(), Span::call_site())
    }
}

impl From<Box<str>> for LitStr {
    fn from(value: Box<str>) -> LitStr {
        LitStr::new(value.into(), Span::call_site())
    }
}

impl From<Cow<'_, str>> for LitStr {
    fn from(value: Cow<'_, str>) -> LitStr {
        LitStr::new(value.into_owned(), Span::call_site())
    }
}

impl From<LitStr> for Box<str> {
    fn from(lit: LitStr) -> Self {
        lit.value.into_boxed_str()
    }
}

impl From<LitStr> for Cow<'_, str> {
    fn from(lit: LitStr) -> Self {
        lit.value.into()
    }
}

impl AsRef<str> for LitStr {
    fn as_ref(&self) -> &str {
        &self.value
    }
}

impl Deref for LitStr {
    type Target = str;

    fn deref(&self) -> &Self::Target {
        &self.value
    }
}

impl Borrow<str> for LitStr {
    fn borrow(&self) -> &str {
        &self.value
    }
}

impl PartialEq<str> for LitStr {
    fn eq(&self, other: &str) -> bool {
        self.value == other
    }
}

impl PartialOrd<str> for LitStr {
    fn partial_cmp(&self, other: &str) -> Option<Ordering> {
        self.value.as_str().cmp(other).into()
    }
}

impl From<syn::LitByteStr> for LitByteStr {
    fn from(lit: syn::LitByteStr) -> Self {
        LitByteStr::new(lit.value(), lit.span())
    }
}

impl From<LitByteStr> for syn::LitByteStr {
    fn from(lit: LitByteStr) -> Self {
        syn::LitByteStr::new(&lit.value, lit.span())
    }
}

impl From<&[u8]> for LitByteStr {
    fn from(value: &[u8]) -> Self {
        LitByteStr::new(value.to_vec(), Span::call_site())
    }
}

impl From<Box<[u8]>> for LitByteStr {
    fn from(value: Box<[u8]>) -> Self {
        LitByteStr::new(value.into(), Span::call_site())
    }
}

impl From<Cow<'_, [u8]>> for LitByteStr {
    fn from(value: Cow<'_, [u8]>) -> Self {
        LitByteStr::new(value.into_owned(), Span::call_site())
    }
}

impl From<LitByteStr> for Box<[u8]> {
    fn from(lit: LitByteStr) -> Self {
        lit.value.into_boxed_slice()
    }
}

impl From<LitByteStr> for Cow<'_, [u8]> {
    fn from(lit: LitByteStr) -> Self {
        lit.value.into()
    }
}

impl AsRef<[u8]> for LitByteStr {
    fn as_ref(&self) -> &[u8] {
        &self.value
    }
}

impl AsMut<[u8]> for LitByteStr {
    fn as_mut(&mut self) -> &mut [u8] {
        &mut self.value
    }
}

impl Deref for LitByteStr {
    type Target = [u8];

    fn deref(&self) -> &Self::Target {
        &self.value
    }
}

impl DerefMut for LitByteStr {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.value
    }
}

impl Borrow<[u8]> for LitByteStr {
    fn borrow(&self) -> &[u8] {
        &self.value
    }
}

impl BorrowMut<[u8]> for LitByteStr {
    fn borrow_mut(&mut self) -> &mut [u8] {
        &mut self.value
    }
}

impl PartialEq<[u8]> for LitByteStr {
    fn eq(&self, other: &[u8]) -> bool {
        self.value == other
    }
}

impl PartialOrd<[u8]> for LitByteStr {
    fn partial_cmp(&self, other: &[u8]) -> Option<Ordering> {
        self.value.as_slice().cmp(other).into()
    }
}

impl Parse for LitBool {
    fn parse(input: ParseStream<'_>) -> Result<Self> {
        input.parse::<syn::LitBool>().map(LitBool::from)
    }
}

impl Parse for LitByte {
    fn parse(input: ParseStream<'_>) -> Result<Self> {
        input.parse::<syn::LitByte>().map(LitByte::from)
    }
}

impl Parse for LitInt {
    fn parse(input: ParseStream<'_>) -> Result<Self> {
        input.parse::<syn::LitInt>().and_then(LitInt::try_from)
    }
}

impl Parse for LitUint {
    fn parse(input: ParseStream<'_>) -> Result<Self> {
        input.parse::<syn::LitInt>().and_then(LitUint::try_from)
    }
}

impl Parse for LitFloat {
    fn parse(input: ParseStream<'_>) -> Result<Self> {
        input.parse::<syn::LitFloat>().and_then(LitFloat::try_from)
    }
}

impl Parse for LitChar {
    fn parse(input: ParseStream<'_>) -> Result<Self> {
        input.parse::<syn::LitChar>().map(LitChar::from)
    }
}

impl Parse for LitStr {
    fn parse(input: ParseStream<'_>) -> Result<Self> {
        input.parse::<syn::LitStr>().map(LitStr::from)
    }
}

impl Parse for LitByteStr {
    fn parse(input: ParseStream<'_>) -> Result<Self> {
        input.parse::<syn::LitByteStr>().map(LitByteStr::from)
    }
}

/// Represents any literal value.
///
/// The following is a lazy doc-test for ensuring that the `Span` of literals
/// is preserved when converted between `parsel::ast::Lit` and `syn::Lit`.
///
/// ```rust
/// # use core::convert::TryFrom;
/// # use parsel::ast::Lit;
/// # use parsel::ast::Many;
/// # use parsel::ToTokens;
/// // This deliberately uses `parse_str()` instead of `parse_quote!{}`
/// // because the former results in meaningful `Span` values, while
/// // the latter would cause every token to be spanned to the call site.
/// let source = r#"
/// true
///    false  6.283
///   100000023456         b'\xa3'
///       "foo bar baz" - 74819253
///    -99887766554433221100
///     b"This is a byte string! A literal one."
/// "#;
/// let parsel: Many<Lit> = parsel::parse_str(source).unwrap();
/// let syn: Many<syn::Lit> = parsel::parse_str(source).unwrap();
///
/// let parsel_strings: Vec<_> = parsel
///     .iter()
///     .map(Lit::to_string)
///     .collect();
/// let syn_strings: Vec<_> = syn
///     .iter()
///     .map(|lit| -> String {
///         // if we simply used `TokenStream::to_string()` here, then multi-token
///         // negative literals would fail the test since their representation
///         // sometimes includes a space between the sign and the digits.
///         lit.to_token_stream().into_iter().map(|tt| tt.to_string()).collect()
///     })
///     .collect();
///
/// assert_eq!(parsel_strings, syn_strings);
///
/// let parsel_spans: Vec<_> = parsel
///     .iter()
///     .map(Lit::span)
///     .map(|span| (span.start(), span.end()))
///     .collect();
/// let syn_spans: Vec<_> = syn
///     .iter()
///     .map(syn::Lit::span)
///     .map(|span| (span.start(), span.end()))
///     .collect();
///
/// assert_eq!(parsel_spans, syn_spans);
///
/// let parsel_converted_spans: Vec<_> = parsel
///     .into_iter()
///     .map(|lit| syn::Lit::from(lit).span())
///     .map(|span| (span.start(), span.end()))
///     .collect();
/// let syn_converted_spans: Vec<_> = syn
///     .into_iter()
///     .map(|lit| Lit::try_from(lit).unwrap().span())
///     .map(|span| (span.start(), span.end()))
///     .collect();
///
/// assert_eq!(parsel_converted_spans, syn_converted_spans);
/// ```
#[derive(Clone, PartialEq, Eq, Hash)]
pub enum Lit {
    Bool(LitBool),
    Byte(LitByte),
    Int(LitInt),
    Uint(LitUint),
    Float(LitFloat),
    Char(LitChar),
    Str(LitStr),
    ByteStr(LitByteStr),
}

impl Lit {
    pub fn span(&self) -> Span {
        match self {
            Lit::Bool(lit)    => lit.span(),
            Lit::Byte(lit)    => lit.span(),
            Lit::Int(lit)     => lit.span(),
            Lit::Uint(lit)    => lit.span(),
            Lit::Float(lit)   => lit.span(),
            Lit::Char(lit)    => lit.span(),
            Lit::Str(lit)     => lit.span(),
            Lit::ByteStr(lit) => lit.span(),
        }
    }

    pub fn set_span(&mut self, new_span: Span) {
        match self {
            Lit::Bool(lit)    => lit.set_span(new_span),
            Lit::Byte(lit)    => lit.set_span(new_span),
            Lit::Int(lit)     => lit.set_span(new_span),
            Lit::Uint(lit)    => lit.set_span(new_span),
            Lit::Float(lit)   => lit.set_span(new_span),
            Lit::Char(lit)    => lit.set_span(new_span),
            Lit::Str(lit)     => lit.set_span(new_span),
            Lit::ByteStr(lit) => lit.set_span(new_span),
        }
    }
}

impl From<LitBool> for Lit {
    fn from(lit: LitBool) -> Self {
        Lit::Bool(lit)
    }
}

impl From<bool> for Lit {
    fn from(value: bool) -> Self {
        Lit::Bool(value.into())
    }
}

impl From<LitByte> for Lit {
    fn from(lit: LitByte) -> Self {
        Lit::Byte(lit)
    }
}

impl From<u8> for Lit {
    fn from(value: u8) -> Self {
        Lit::Byte(value.into())
    }
}

impl From<LitInt> for Lit {
    fn from(lit: LitInt) -> Self {
        Lit::Int(lit)
    }
}

impl From<i128> for Lit {
    fn from(value: i128) -> Self {
        Lit::Int(value.into())
    }
}

impl From<LitUint> for Lit {
    fn from(lit: LitUint) -> Self {
        Lit::Uint(lit)
    }
}

impl From<u128> for Lit {
    fn from(value: u128) -> Self {
        Lit::Uint(value.into())
    }
}

impl From<LitFloat> for Lit {
    fn from(lit: LitFloat) -> Self {
        Lit::Float(lit)
    }
}

impl From<NotNan<f64>> for Lit {
    fn from(value: NotNan<f64>) -> Self {
        Lit::Float(value.into())
    }
}

impl TryFrom<f64> for Lit {
    type Error = ordered_float::FloatIsNan;

    fn try_from(value: f64) -> core::result::Result<Self, Self::Error> {
        LitFloat::try_from(value).map(Lit::Float)
    }
}

impl From<LitChar> for Lit {
    fn from(lit: LitChar) -> Self {
        Lit::Char(lit)
    }
}

impl From<char> for Lit {
    fn from(value: char) -> Self {
        Lit::Char(value.into())
    }
}

impl From<LitStr> for Lit {
    fn from(lit: LitStr) -> Self {
        Lit::Str(lit)
    }
}

impl From<String> for Lit {
    fn from(value: String) -> Self {
        Lit::Str(value.into())
    }
}

impl From<&str> for Lit {
    fn from(value: &str) -> Self {
        Lit::Str(value.into())
    }
}

impl From<Box<str>> for Lit {
    fn from(value: Box<str>) -> Self {
        Lit::Str(value.into())
    }
}

impl From<Cow<'_, str>> for Lit {
    fn from(value: Cow<'_, str>) -> Self {
        Lit::Str(value.into())
    }
}

impl From<LitByteStr> for Lit {
    fn from(lit: LitByteStr) -> Self {
        Lit::ByteStr(lit)
    }
}

impl From<Vec<u8>> for Lit {
    fn from(value: Vec<u8>) -> Self {
        Lit::ByteStr(value.into())
    }
}

impl From<&[u8]> for Lit {
    fn from(value: &[u8]) -> Self {
        Lit::ByteStr(value.into())
    }
}

impl From<Box<[u8]>> for Lit {
    fn from(value: Box<[u8]>) -> Self {
        Lit::ByteStr(value.into())
    }
}

impl From<Cow<'_, [u8]>> for Lit {
    fn from(value: Cow<'_, [u8]>) -> Self {
        Lit::ByteStr(value.into())
    }
}

impl From<Lit> for syn::Lit {
    fn from(lit: Lit) -> Self {
        match lit {
            Lit::Bool(lit)    => syn::Lit::Bool(lit.into()),
            Lit::Byte(lit)    => syn::Lit::Byte(lit.into()),
            Lit::Int(lit)     => syn::Lit::Int(lit.into()),
            Lit::Uint(lit)    => syn::Lit::Int(lit.into()),
            Lit::Float(lit)   => syn::Lit::Float(lit.into()),
            Lit::Char(lit)    => syn::Lit::Char(lit.into()),
            Lit::Str(lit)     => syn::Lit::Str(lit.into()),
            Lit::ByteStr(lit) => syn::Lit::ByteStr(lit.into()),
        }
    }
}

impl TryFrom<syn::Lit> for Lit {
    type Error = Error;

    fn try_from(lit: syn::Lit) -> Result<Self> {
        match lit {
            syn::Lit::Bool(lit) => Ok(Lit::Bool(lit.into())),
            syn::Lit::Byte(lit) => Ok(Lit::Byte(lit.into())),
            syn::Lit::Int(lit) => {
                if lit.base10_digits().trim().starts_with('-') {
                    LitInt::try_from(lit).map(Lit::Int)
                } else {
                    LitUint::try_from(lit).map(Lit::Uint)
                }
            }
            syn::Lit::Float(lit) => LitFloat::try_from(lit).map(Lit::Float),
            syn::Lit::Char(lit) => Ok(Lit::Char(lit.into())),
            syn::Lit::Str(lit) => Ok(Lit::Str(lit.into())),
            syn::Lit::ByteStr(lit) => Ok(Lit::ByteStr(lit.into())),
            syn::Lit::Verbatim(lit) => {
                Err(Error::new(lit.span(), format!("unparseable literal `{:?}`", lit)))
            }
        }
    }
}

impl Debug for Lit {
    fn fmt(&self, formatter: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Lit::Bool(lit)    => Debug::fmt(lit, formatter),
            Lit::Byte(lit)    => Debug::fmt(lit, formatter),
            Lit::Int(lit)     => Debug::fmt(lit, formatter),
            Lit::Uint(lit)    => Debug::fmt(lit, formatter),
            Lit::Float(lit)   => Debug::fmt(lit, formatter),
            Lit::Char(lit)    => Debug::fmt(lit, formatter),
            Lit::Str(lit)     => Debug::fmt(lit, formatter),
            Lit::ByteStr(lit) => Debug::fmt(lit, formatter),
        }
    }
}

impl Display for Lit {
    fn fmt(&self, formatter: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Lit::Bool(lit)    => Display::fmt(lit, formatter),
            Lit::Byte(lit)    => Display::fmt(lit, formatter),
            Lit::Int(lit)     => Display::fmt(lit, formatter),
            Lit::Uint(lit)    => Display::fmt(lit, formatter),
            Lit::Float(lit)   => Display::fmt(lit, formatter),
            Lit::Char(lit)    => Display::fmt(lit, formatter),
            Lit::Str(lit)     => Display::fmt(lit, formatter),
            Lit::ByteStr(lit) => Display::fmt(lit, formatter),
        }
    }
}

impl FromStr for Lit {
    type Err = Error;

    fn from_str(string: &str) -> Result<Self> {
        syn::parse_str(string)
    }
}

impl Parse for Lit {
    fn parse(input: ParseStream<'_>) -> Result<Self> {
        syn::Lit::parse(input).and_then(Lit::try_from)
    }
}

impl ToTokens for Lit {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        match self {
            Lit::Bool(lit)    => lit.to_tokens(tokens),
            Lit::Byte(lit)    => lit.to_tokens(tokens),
            Lit::Int(lit)     => lit.to_tokens(tokens),
            Lit::Uint(lit)    => lit.to_tokens(tokens),
            Lit::Float(lit)   => lit.to_tokens(tokens),
            Lit::Char(lit)    => lit.to_tokens(tokens),
            Lit::Str(lit)     => lit.to_tokens(tokens),
            Lit::ByteStr(lit) => lit.to_tokens(tokens),
        }
    }
}

/// Helper type for parsing left-associative binary infix operators.
///
/// Prevents infinite left-recursion by parsing a stream of binary infix operators
/// iteratively, then transforming the sequence of nodes into a left-leaning tree.
///
/// * `R` is the type of the right-hand side of the production, i.e.,
///   the sub-production at the next highest precedence level.
/// * `O` is the type of the interleaved binary operator itself.
///
/// That is, a production in EBNF style would look like:
///
/// ```text
/// LeftAssoc = LeftAssoc O R
///           | R
/// ```
///
/// ## Examples
///
/// ```rust
/// # use core::convert::TryFrom;
/// # use parsel::{Parse, ToTokens};
/// # use parsel::ast::{Lit, LitInt, LitUint, LitFloat, Ident, Paren, LeftAssoc};
/// # use parsel::ast::{token, ident};
/// #[derive(PartialEq, Eq, Debug, Parse, ToTokens)]
/// enum AddOp {
///     Add(token::Add),
///     Sub(token::Sub),
/// }
///
/// #[derive(PartialEq, Eq, Debug, Parse, ToTokens)]
/// enum MulOp {
///     Mul(token::Star),
///     Div(token::Div),
/// }
///
/// #[derive(PartialEq, Eq, Debug, Parse, ToTokens)]
/// enum Term {
///     Literal(Lit),
///     Variable(Ident),
///     Group(
///         #[parsel(recursive)]
///         Paren<Box<Expr>>
///     ),
/// }
///
/// type Expr = LeftAssoc<
///     AddOp,
///     LeftAssoc<
///         MulOp,
///         Term
///     >
/// >;
///
/// let actual: Expr = parsel::parse_quote!{
///     10 - 2.99 + p / 42.0 - (q - -24.314) * -13
/// };
/// let expected = LeftAssoc::Binary {
///     lhs: Box::new(LeftAssoc::Binary {
///         lhs: Box::new(LeftAssoc::Binary {
///             lhs: Box::new(LeftAssoc::Rhs(LeftAssoc::Rhs(
///                 Term::Literal(LitUint::from(10).into())
///             ))),
///             op: AddOp::Sub(Default::default()),
///             rhs: LeftAssoc::Rhs(Term::Literal(
///                 LitFloat::try_from(2.99).unwrap().into()
///             )),
///         }),
///         op: AddOp::Add(Default::default()),
///         rhs: LeftAssoc::Binary {
///             lhs: Box::new(LeftAssoc::Rhs(
///                 Term::Variable(ident("p"))
///             )),
///             op: MulOp::Div(Default::default()),
///             rhs: Term::Literal(LitFloat::try_from(42.0).unwrap().into()),
///         },
///     }),
///     op: AddOp::Sub(Default::default()),
///     rhs: LeftAssoc::Binary {
///         lhs: Box::new(LeftAssoc::Rhs(
///             Term::Group(Paren::from(Box::new(
///                 LeftAssoc::Binary {
///                     lhs: Box::new(LeftAssoc::Rhs(LeftAssoc::Rhs(
///                         Term::Variable(ident("q"))
///                     ))),
///                     op: AddOp::Sub(Default::default()),
///                     rhs: LeftAssoc::Rhs(Term::Literal(
///                         LitFloat::try_from(-24.314).unwrap().into()
///                     )),
///                 }
///             )))
///         )),
///         op: MulOp::Mul(Default::default()),
///         rhs: Term::Literal(LitInt::from(-13).into()),
///     }
/// };
///
/// assert_eq!(actual, expected);
/// assert_eq!(actual.to_string(), expected.to_string());
/// assert_eq!(
///     expected.to_string(),
///     str::trim(r#"
/// 10 - 2.99 + p / 42.0 - (
///     q - - 24.314
/// )
/// * - 13
///     "#),
/// );
/// ```
#[derive(Clone, PartialEq, Eq, Hash)]
pub enum LeftAssoc<O, R> {
    /// A left-associative binary infix operator was found.
    Binary {
        /// Left-hand side of the binary operation.
        lhs: Box<Self>,
        /// The infix binary operator.
        op: O,
        /// Right-hand side of the binary operation.
        rhs: R,
    },
    /// No binary operator was found at this level of
    /// precedence, so simply forward to the next level.
    Rhs(R),
}

impl<O, R> From<R> for LeftAssoc<O, R> {
    fn from(rhs: R) -> Self {
        LeftAssoc::Rhs(rhs)
    }
}

impl<O, R> Debug for LeftAssoc<O, R>
where
    O: Debug,
    R: Debug,
{
    fn fmt(&self, formatter: &mut Formatter<'_>) -> fmt::Result {
        match self {
            LeftAssoc::Binary { lhs, op, rhs } => {
                let name = format!("Binary<{:?}>", op);

                formatter.debug_struct(&name)
                    .field("lhs", lhs)
                    .field("rhs", rhs)
                    .finish()
            }
            LeftAssoc::Rhs(rhs) => Debug::fmt(rhs, formatter)
        }
    }
}

impl<O, R> Display for LeftAssoc<O, R>
where
    O: ToTokens,
    R: ToTokens,
{
    fn fmt(&self, formatter: &mut Formatter<'_>) -> fmt::Result {
        pretty_print_tokens(self, formatter)
    }
}

impl<O, R> FromStr for LeftAssoc<O, R>
where
    O: Parse,
    R: Parse,
{
    type Err = Error;

    fn from_str(string: &str) -> Result<Self> {
        syn::parse_str(string)
    }
}

impl<O, R> Parse for LeftAssoc<O, R>
where
    O: Parse,
    R: Parse,
{
    fn parse(input: ParseStream<'_>) -> Result<Self> {
        // Avoid infinite left recursion by parsing iteratively
        let seq: Separated<R, O> = input.parse()?;
        let (first, rest) = seq.into_first_rest();

        let mut expr = LeftAssoc::Rhs(first);

        // Transform linear sequence to left-leaning tree
        for (op, rhs) in rest {
            expr = LeftAssoc::Binary {
                lhs: Box::new(expr),
                op,
                rhs,
            };
        }

        Ok(expr)
    }
}

impl<O, R> ToTokens for LeftAssoc<O, R>
where
    O: ToTokens,
    R: ToTokens,
{
    fn to_tokens(&self, tokens: &mut TokenStream) {
        match self {
            LeftAssoc::Binary { lhs, op, rhs } => {
                lhs.to_tokens(&mut *tokens);
                op.to_tokens(&mut *tokens);
                rhs.to_tokens(&mut *tokens);
            }
            LeftAssoc::Rhs(rhs) => {
                rhs.to_tokens(tokens);
            }
        }
    }
}

/// Helper type for parsing right-associative binary infix operators.
///
/// Reduces deep right-recursion by parsing a stream of binary infix operators
/// iteratively, then transforming the sequence of nodes into a right-leaning tree.
///
/// * `L` is the type of the left-hand side of the production, i.e.,
///   the sub-production at the next highest precedence level.
/// * `O` is the type of the interleaved binary operator itself.
///
/// That is, a production in EBNF style would look like:
///
/// ```text
/// RightAssoc = L O RightAssoc
///            | L
/// ```
///
/// ## Examples
///
/// ```rust
/// # use parsel::{parse_quote, Parse, ToTokens};
/// # use parsel::ast::{ident, LitBool, Ident, Paren, RightAssoc};
/// # use parsel::ast::token::{ And, Or, Tilde };
/// #[derive(PartialEq, Eq, Debug, Parse, ToTokens)]
/// enum Term {
///     Lit(LitBool),
///     Var(Ident),
///     Not(
///         Tilde,
///         #[parsel(recursive)]
///         Box<Term>,
///     ),
///     Group(
///         #[parsel(recursive)]
///         Box<Paren<Expr>>
///     ),
/// }
///
/// type Expr = RightAssoc<
///     Or,
///     RightAssoc<
///         And,
///         Term
///     >
/// >;
///
/// let actual: Expr = parse_quote!((~false | a) & ~(b & c & true));
/// let expected = RightAssoc::<Or, _>::Lhs(RightAssoc::<And, _>::Binary {
///     lhs: Term::Group(Box::new(Paren::from(
///         RightAssoc::<Or, _>::Binary {
///            lhs: RightAssoc::<And, _>::Lhs(Term::Not(
///                Tilde::default(),
///                Box::new(Term::Lit(LitBool::from(false)))
///            )),
///            op: Or::default(),
///            rhs: Box::new(RightAssoc::<Or, _>::Lhs(
///                RightAssoc::<And, _>::Lhs(
///                    Term::Var(ident("a"))
///                )
///            )),
///        }
///     ))),
///     op: And::default(),
///     rhs: Box::new(RightAssoc::<And, _>::Lhs(
///         Term::Not(
///             Tilde::default(),
///             Box::new(Term::Group(Box::new(Paren::from(
///                 RightAssoc::<Or, _>::Lhs(RightAssoc::<And, _>::Binary {
///                     lhs: Term::Var(ident("b")),
///                     op: And::default(),
///                     rhs: Box::new(RightAssoc::<And, _>::Binary {
///                         lhs: Term::Var(ident("c")),
///                         op: And::default(),
///                         rhs: Box::new(RightAssoc::<And, _>::Lhs(
///                             Term::Lit(LitBool::from(true)),
///                         )),
///                     }),
///                 })
///             ))))
///         )
///     )),
/// });
///
/// assert_eq!(actual, expected);
/// assert_eq!(actual.to_string(), expected.to_string());
/// ```
#[derive(Clone, PartialEq, Eq, Hash)]
pub enum RightAssoc<O, L> {
    /// A right-associative binary infix operator was found.
    Binary {
        /// Left-hand side of the binary operation.
        lhs: L,
        /// The infix binary operator.
        op: O,
        /// Right-hand side of the binary operation.
        rhs: Box<Self>,
    },
    /// No binary operator was found at this level of
    /// precedence, so simply forward to the next level.
    Lhs(L),
}

impl<O, L> From<L> for RightAssoc<O, L> {
    fn from(lhs: L) -> Self {
        RightAssoc::Lhs(lhs)
    }
}

impl<O, L> Debug for RightAssoc<O, L>
where
    O: Debug,
    L: Debug,
{
    fn fmt(&self, formatter: &mut Formatter<'_>) -> fmt::Result {
        match self {
            RightAssoc::Binary { lhs, op, rhs } => {
                let name = format!("Binary<{:?}>", op);

                formatter.debug_struct(&name)
                    .field("lhs", lhs)
                    .field("rhs", rhs)
                    .finish()
            }
            RightAssoc::Lhs(lhs) => Debug::fmt(lhs, formatter)
        }
    }
}

impl<O, L> Display for RightAssoc<O, L>
where
    O: ToTokens,
    L: ToTokens,
{
    fn fmt(&self, formatter: &mut Formatter<'_>) -> fmt::Result {
        pretty_print_tokens(self, formatter)
    }
}

impl<O, L> FromStr for RightAssoc<O, L>
where
    O: Parse,
    L: Parse,
{
    type Err = Error;

    fn from_str(string: &str) -> Result<Self> {
        syn::parse_str(string)
    }
}

impl<O, L> Parse for RightAssoc<O, L>
where
    O: Parse,
    L: Parse,
{
    fn parse(input: ParseStream<'_>) -> Result<Self> {
        // Avoid deep right recursion by parsing iteratively
        let seq: Separated<L, O> = input.parse()?;
        let (last, rest) = seq.into_last_rest();

        let mut expr = RightAssoc::Lhs(last);

        // Transform linear sequence to right-leaning tree
        for (lhs, op) in rest.into_iter().rev() {
            expr = RightAssoc::Binary {
                lhs,
                op,
                rhs: Box::new(expr),
            };
        }

        Ok(expr)
    }
}

impl<O, L> ToTokens for RightAssoc<O, L>
where
    O: ToTokens,
    L: ToTokens,
{
    fn to_tokens(&self, tokens: &mut TokenStream) {
        match self {
            RightAssoc::Binary { lhs, op, rhs } => {
                lhs.to_tokens(&mut *tokens);
                op.to_tokens(&mut *tokens);
                rhs.to_tokens(&mut *tokens);
            }
            RightAssoc::Lhs(lhs) => {
                lhs.to_tokens(tokens);
            }
        }
    }
}

/// Generic dichotomous alternation.
///
/// ```rust
/// # use parsel::{Error, Result};
/// # use parsel::ast::{LitInt, Word, Either};
/// #
/// let x: Either<LitInt, Word> = "1234567890".parse()?;
/// assert_eq!(x.as_ref().left().unwrap().value(), 1234567890);
/// assert_eq!(x.as_ref().right(), None);
/// assert_eq!(x.to_string(), "1234567890");
///
/// let y: Either<LitInt, Word> = "i_am_an_ident".parse()?;
/// assert_eq!(y.as_ref().right().unwrap().to_string(), "i_am_an_ident");
/// assert_eq!(y.as_ref().left(), None);
/// assert_eq!(y.to_string(), "i_am_an_ident");
///
/// let bad: Result<Either<LitInt, Word>> = "184.3549".parse();
/// assert!(bad.is_err());
/// #
/// # Ok::<(), Error>(())
/// ```
#[must_use]
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Either<L, R> {
    Left(L),
    Right(R),
}

impl<L, R> Either<L, R> {
    pub fn left(self) -> Option<L> {
        match self {
            Either::Left(left) => Some(left),
            Either::Right(_)   => None,
        }
    }

    pub fn right(self) -> Option<R> {
        match self {
            Either::Left(_)      => None,
            Either::Right(right) => Some(right),
        }
    }

    pub fn is_left(&self) -> bool {
        matches!(self, Either::Left(_))
    }

    pub fn is_right(&self) -> bool {
        matches!(self, Either::Right(_))
    }

    /// ```rust
    /// # use parsel::ast::Either;
    /// #
    /// let left: Either::<String, ()> = Either::Left(String::from("left"));
    /// let right: Either<(), String> = left.flip();
    /// assert_eq!(right, Either::Right(String::from("left")));
    /// ```
    pub fn flip(self) -> Either<R, L> {
        match self {
            Either::Left(left)   => Either::Right(left),
            Either::Right(right) => Either::Left(right),
        }
    }

    pub fn as_ref(&self) -> Either<&L, &R> {
        match *self {
            Either::Left(ref left)   => Either::Left(left),
            Either::Right(ref right) => Either::Right(right),
        }
    }

    pub fn as_mut(&mut self) -> Either<&mut L, &mut R> {
        match *self {
            Either::Left(ref mut left)   => Either::Left(left),
            Either::Right(ref mut right) => Either::Right(right),
        }
    }

    /// ```rust
    /// # use parsel::ast::Either;
    /// #
    /// let left: Either<u32, &str> = Either::Left(752_u32);
    /// let right: Either<u32, &str> = Either::Right("some words");
    ///
    /// let left_mapped: Either<u32, String> = left.map(|x| x + 1, |s| s.to_string());
    /// let right_mapped: Either<u32, usize> = right.map(|x| x + 1, |s| s.len());
    ///
    /// assert_eq!(left_mapped, Either::Left(753_u32));
    /// assert_eq!(right_mapped, Either::Right(10_usize));
    /// ```
    pub fn map<T, U, F, G>(self, f: F, g: G) -> Either<T, U>
    where
        F: FnOnce(L) -> T,
        G: FnOnce(R) -> U,
    {
        match self {
            Either::Left(left)   => Either::Left(f(left)),
            Either::Right(right) => Either::Right(g(right)),
        }
    }

    /// This is not `impl IntoIterator` because that would conflict
    /// with the `Iterator` impl, and it is more ergonomics to have
    /// `Iterator` to be the actual trait impl and `into_iter()` an
    /// inherent associated function.
    #[allow(clippy::should_implement_trait)]
    pub fn into_iter(self) -> Either<L::IntoIter, R::IntoIter>
    where
        L: IntoIterator,
        R: IntoIterator,
    {
        self.map(L::into_iter, R::into_iter)
    }
}

impl<L, R> Either<Option<L>, Option<R>> {
    pub fn transpose(self) -> Option<Either<L, R>> {
        match self {
            Either::Left(left)   => left.map(Either::Left),
            Either::Right(right) => right.map(Either::Right),
        }
    }
}

impl<L, R> Either<Result<L>, Result<R>> {
    pub fn transpose(self) -> Result<Either<L, R>> {
        match self {
            Either::Left(left)   => left.map(Either::Left),
            Either::Right(right) => right.map(Either::Right),
        }
    }
}

impl<T> Either<T, T> {
    pub fn into_inner(self) -> T {
        match self {
            Either::Left(left)   => left,
            Either::Right(right) => right,
        }
    }
}

impl<T> AsRef<T> for Either<T, T> {
    fn as_ref(&self) -> &T {
        match self {
            Either::Left(left)   => left,
            Either::Right(right) => right,
        }
    }
}

impl<T> AsMut<T> for Either<T, T> {
    fn as_mut(&mut self) -> &mut T {
        match self {
            Either::Left(left)   => left,
            Either::Right(right) => right,
        }
    }
}

impl<T> Deref for Either<T, T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        match self {
            Either::Left(left)   => left,
            Either::Right(right) => right,
        }
    }
}

impl<T> DerefMut for Either<T, T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        match self {
            Either::Left(left)   => left,
            Either::Right(right) => right,
        }
    }
}

impl<L, R> Iterator for Either<L, R>
where
    L: Iterator,
    R: Iterator,
{
    type Item = Either<L::Item, R::Item>;

    fn next(&mut self) -> Option<Self::Item> {
        self.as_mut()
            .map(L::next, R::next)
            .transpose()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.as_ref()
            .map(L::size_hint, R::size_hint)
            .into_inner()
    }

    fn count(self) -> usize {
        self.map(L::count, R::count).into_inner()
    }

    fn nth(&mut self, n: usize) -> Option<Self::Item> {
        self.as_mut()
            .map(|left| left.nth(n), |right| right.nth(n))
            .transpose()
    }

    fn last(self) -> Option<Self::Item> {
        self.map(L::last, R::last).transpose()
    }
}

impl<L, R> DoubleEndedIterator for Either<L, R>
where
    L: DoubleEndedIterator,
    R: DoubleEndedIterator,
{
    fn next_back(&mut self) -> Option<Self::Item> {
        self.as_mut()
            .map(L::next_back, R::next_back)
            .transpose()
    }
}

impl<L, R> ExactSizeIterator for Either<L, R>
where
    L: ExactSizeIterator,
    R: ExactSizeIterator,
{
}

impl<L, R> FusedIterator for Either<L, R>
where
    L: FusedIterator,
    R: FusedIterator,
{
}

impl<L, R, T> Extend<T> for Either<L, R>
where
    L: Extend<T>,
    R: Extend<T>,
{
    fn extend<I>(&mut self, iter: I)
    where
        I: IntoIterator<Item = T>
    {
        match self {
            Either::Left(left)   => left.extend(iter),
            Either::Right(right) => right.extend(iter),
        }
    }
}

impl<L, R> FromStr for Either<L, R>
where
    L: Parse,
    R: Parse,
{
    type Err = Error;

    fn from_str(string: &str) -> Result<Self> {
        syn::parse_str(string)
    }
}

impl<L, R> Debug for Either<L, R>
where
    L: Debug,
    R: Debug,
{
    fn fmt(&self, formatter: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Either::Left(left)   => Debug::fmt(left, formatter),
            Either::Right(right) => Debug::fmt(right, formatter),
        }
    }
}

impl<L, R> Display for Either<L, R>
where
    L: Display,
    R: Display,
{
    fn fmt(&self, formatter: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Either::Left(left)   => Display::fmt(left, formatter),
            Either::Right(right) => Display::fmt(right, formatter),
        }
    }
}

impl<L, R> Parse for Either<L, R>
where
    L: Parse,
    R: Parse,
{
    fn parse(input: ParseStream<'_>) -> Result<Self> {
        let left_fork = input.fork();
        let left_error = match left_fork.parse::<L>() {
            Ok(left) => {
                input.advance_to(&left_fork);
                return Ok(Either::Left(left));
            }
            Err(error) => error,
        };

        let right_fork = input.fork();
        let right_error = match right_fork.parse::<R>() {
            Ok(right) => {
                input.advance_to(&right_fork);
                return Ok(Either::Right(right));
            }
            Err(error) => error,
        };

        Err(max_by_key(left_error, right_error, |e| e.span().end()))
    }
}

impl<L, R> ToTokens for Either<L, R>
where
    L: ToTokens,
    R: ToTokens,
{
    fn to_tokens(&self, tokens: &mut TokenStream) {
        match self {
            Either::Left(left)   => left.to_tokens(tokens),
            Either::Right(right) => right.to_tokens(tokens),
        }
    }
}
