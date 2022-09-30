## Parsel, the Zero-Code Parser Generator

[![MSRV](https://img.shields.io/badge/MSRV-1.56.1-green)](https://github.com/H2CO3/Parsel)

Parsel is a library for generating parsers directly from syntax tree node types.

The main entry point is the [`#[derive(Parse)]`](derive.Parse.html) custom derive
proc-macro, which generates an implementation of the `syn::parse::Parse` trait
for the annotated AST node type. Adding [`#[derive(FromStr)]`](derive.FromStr.html)
also implements the standard `FromStr` trait for the type, by simply forwarding to
its `Parse` impl.

In addition, a [`#[derive(ToTokens)]`](derive.ToTokens.html) macro is provided,
for easily obtaining the source representation of a specific AST node via the
`quote` crate. This in turn helps with getting its `Span` due to the blanket
[`impl<T: ToTokens> Spanned for T`](https://docs.rs/syn/latest/syn/spanned/trait.Spanned.html#implementors).
Adding [`#[derive(Display)]`](derive.Display.html) also implements the standard
`Display` trait for the type, by simply forwarding to its `ToTokens` impl.

Furthermore, the [`ast` module](ast/index.html) provides a number of helper types
for common needs, such as optional productions, repetition, parenthesization, and
grouping. These are mostly lightweight wrappers around parsing collections and
parsing logic already provided by `syn`. However, some very useful `syn` types,
such as `Option<T: Parse>` and `Punctuated`, have multiple, equally valid parses,
so they don't implement `Parse` in order to avoid amibiguity. Parsel handles this
ambiguity at the type level, by splitting the set of valid parses into multiple,
unambiguously parseable types.

### Examples and How It Works

The fundamental idea behind Parsel is the observation that `struct`s and `enum`s
directly correspond to sequences and alternation in grammars, and that they are
composable: one does not need to know the exact implementation of sub-expressions
in order to produce a parser for the current rule.

AST nodes that have a `struct` type correspond to sequences: every field (whether
named or numbered) will be parsed and populated one after another, in the order
specified in the source.

AST nodes having an `enum` type correspond to alternation: their variants will be
tried in order, and the first one that succeeds will be returned. Fields of tuple
and struct variants are treated in the same sequential manner as `struct` fields.

Accordingly, you define your grammar by specifying the fields and variants of AST
nodes, and Parsel will generate a parser from them. Let's see what this looks like
in the context of the parser and the printer for a simple, JSON-like language:

```rust
use core::iter::FromIterator;
use core::convert::TryFrom;
use parsel::{Parse, ToTokens};
use parsel::ast::{Bracket, Brace, Punctuated, LitBool, LitInt, LitFloat, LitStr};
use parsel::ast::token::{Comma, Colon};

mod kw {
    parsel::custom_keyword!(null);
}

#[derive(PartialEq, Eq, Debug, Parse, ToTokens)]
enum Value {
    Null(kw::null),
    Bool(LitBool),
    Int(LitInt),
    Float(LitFloat),
    Str(LitStr),
    Array(
        #[parsel(recursive)]
        Bracket<Punctuated<Value, Comma>>
    ),
    Object(
        #[parsel(recursive)]
        Brace<Punctuated<KeyValue, Comma>>
    ),
}

#[derive(PartialEq, Eq, Debug, Parse, ToTokens)]
struct KeyValue {
    key: LitStr,
    colon: Colon,
    value: Value,
}

let actual: Value = parsel::parse_quote!({
    "key1": "string value",
    "other key": 318,
    "recursive": [
        1.6180,
        2.7182,
        3.1416,
        null
    ],
    "inner": {
        "nested key": true,
        "hard to write a parser": false
    }
});
let expected = Value::Object(Brace::from(Punctuated::from_iter([
    KeyValue {
        key: LitStr::from("key1"),
        colon: Colon::default(),
        value: Value::Str(LitStr::from("string value")),
    },
    KeyValue {
        key: LitStr::from("other key"),
        colon: Colon::default(),
        value: Value::Int(LitInt::from(318)),
    },
    KeyValue {
        key: LitStr::from("recursive"),
        colon: Colon::default(),
        value: Value::Array(Bracket::from(Punctuated::from_iter([
            Value::Float(LitFloat::try_from(1.6180).unwrap()),
            Value::Float(LitFloat::try_from(2.7182).unwrap()),
            Value::Float(LitFloat::try_from(3.1416).unwrap()),
            Value::Null(kw::null::default()),
        ]))),
    },
    KeyValue {
        key: LitStr::from("inner"),
        colon: Colon::default(),
        value: Value::Object(Brace::from(Punctuated::from_iter([
            KeyValue {
                key: LitStr::from("nested key"),
                colon: Colon::default(),
                value: Value::Bool(LitBool::from(true)),
            },
            KeyValue {
                key: LitStr::from("hard to write a parser"),
                colon: Colon::default(),
                value: Value::Bool(LitBool::from(false)),
            },
        ]))),
    },
])));

assert_eq!(actual, expected);
```

### Recursive AST Nodes and Cyclic Constraints

Most useful real-world grammars are recursive, i.e., they contain productions that
refer to themselves directly (direct recursion) or indirectly (mutual recursion).
This results in AST node types that contain pointers to the same type. Even more
importantly, it leads to cyclic constraints in the implementations of `Parse` and
`ToTokens`. These cyclic constraints are trivially satisfied and resolvable, but
the constraint solver of the Rust compiler is currently struggling with them due
to [Issue #48214](https://github.com/rust-lang/rust/issues/48214).

Thus, one must break such constraint cycles when deriving the implementations of
`Parse` and `ToTokens`. Parsel supports this use case by providing the attribute
`#[parsel(recursive)]`, or an equivalent spelling, `#[parsel(recursive = true)]`.
Adding this attribute to a field of a `struct` or a variant of an `enum` has the
effect of omitting all `FieldType: Parse` and `FieldType: ToTokens` constraints
from the `where` clause of the generated `Parse` and `ToTokens` impls, breaking
the constraint cycle, and thus allowing the code to compile.

It is sufficient to break each constraint cycle on one single type (practically
on the one that requires adding the smallest number of `#[parsel(recursive)]`
annotations). However, if the grammar contains several self-referential cycles,
it is necessary to break each of them. Furthermore, if breaking a cycle requires
omitting a constraint on a type which appears in multiple fields of a `struct` or
a variant, then it is necessary to add `#[parsel(recursive)]` to **all** of those
fields.

As an example, consider the following grammar for simple Boolean operations and
the accompanying comments:

```rust
use parsel::{Parse, ToTokens};
use parsel::ast::{Paren, LitBool};
use parsel::ast::token::{Or, And, Bang};

#[derive(PartialEq, Eq, Debug, Parse, ToTokens)]
enum Expr {
    Or {
        lhs: Conjunction,
        op: Or,
        #[parsel(recursive)] // break direct recursion
        rhs: Box<Expr>,
    },
    Conjunction(Conjunction),
}

#[derive(PartialEq, Eq, Debug, Parse, ToTokens)]
enum Conjunction {
    And {
        lhs: Term,
        op: And,
        #[parsel(recursive)] // break direct recursion
        rhs: Box<Conjunction>,
    },
    Term(Term),
}

#[derive(PartialEq, Eq, Debug, Parse, ToTokens)]
enum Term {
    Literal(LitBool),
    Not(
        Bang,
        #[parsel(recursive)] // break direct recursion
        Box<Term>,
    ),
    Group(
        #[parsel(recursive)] // break mutual recursion
        Paren<Box<Expr>>
    ),
}

let expr: Expr = parsel::parse_str("true & (false | true & true) & !false").unwrap();

assert_eq!(
    expr,
    Expr::Conjunction(Conjunction::And {
        lhs: Term::Literal(LitBool::from(true)),
        op: And::default(),
        rhs: Box::new(Conjunction::And {
            lhs: Term::Group(Paren::from(Box::new(Expr::Or {
                lhs: Conjunction::Term(Term::Literal(LitBool::from(false))),
                op: Or::default(),
                rhs: Box::new(Expr::Conjunction(Conjunction::And {
                    lhs: Term::Literal(LitBool::from(true)),
                    op: And::default(),
                    rhs: Box::new(Conjunction::Term(Term::Literal(LitBool::from(true)))),
                }))
            }))),
            op: And::default(),
            rhs: Box::new(Conjunction::Term(Term::Not(
                Bang::default(),
                Box::new(Term::Literal(LitBool::from(false))),
            ))),
        })
    })
);
```

### Dealing with Left Recursion

If you carefully examine the grammar, you can notice it's right-recursive, i.e.,
the subexpression with identical precedence appears on the right-hand side, while
the left-hand side descends one level to the next tightest-binding subexpression.
This in turn means that consecutive operations of equal precedence will associate
to the right. The reason for this is that recursive descent parsers, such as the
ones generated by Parsel, fall into infinite recursion if they attempt parsing a
left-recursive grammar. For instance, if our top-level expression were defined as

```text
expr = expr '|' conjunction
     | conjunction
```

then the code generated for `expr` would immediately and unconditionally try to
call itself again.

While it is fine to rewrite the grammar as right-recursive in the case of simple
Boolean expressions (since they are associative), it is generally not possible
to just omit left recursion altogether from a grammar. Operations which are not
associative care a lot about how they are grouped, and even e.g. basic algebraic
operations such as subtraction and division are defined to be left-associative
by widespread convention. Thus, it is required that Parsel support associating
terms to the left. There are two ways to achieve this goal:

1. Side-step the problem by simply not representing associativity in the AST.
   This is done by using a helper type capable of expressing explicit repetition
   of arbitrary length (e.g., [`Separated`](ast/struct.Separated.html)), instead
   of creating binary AST nodes. The repeated AST nodes will be sub-expressions
   at the next highest precedence level. This approach puts off the question of
   associativity until evaluation/codegen, that is, until tree-walking time.
2. Use the [`LeftAssoc`](ast/enum.LeftAssoc.html) helper type. This solves the
   problem of infinite recursion by parsing iteratively (just like `Separated`).
   It then transforms the resulting linear list of subexpressions into a properly
   left-associative (left-leaning) tree of AST nodes.

   Note that there is an analogous [`RightAssoc`](ast/enum.RightAssoc.html) type
   as well. Strictly speaking, this is not *necessary,* because right recursion
   makes progress and terminates just fine. However, deriving the parse tree in
   an iterative manner has the advantage of recursing less, and including the
   right-leaning counterpart is preferable for reasons of symmetry/consistency.

### Span and Error Reporting

Types that implement `ToTokens` get an automatic `impl Spanned for T: ToTokens`.
This means that by default, all types deriving `ToTokens` will also report their
span correctly, and parse errors will have useful span information.

However, there is an important caveat regarding alternations (`enum`s) in the
grammar. The way alternations can be parsed in a fully automatic and deceptively
simple way is by attempting to parse each alternative production, one after the
other, and pick the first one that parses successfully. However, if none of them
parses, then it is not obvious to the parser which of the errors it should report.

The heuristic we use to solve this problem is that we use `Span` information to
select the variant that got furthest in the token stream before having failed.
This works because most "nice" context-free grammars are constant lookahead, or
even better, LL(1), i.e. single-token lookahead. This means that if a production
involving more than one token fails in the middle, it will have advanced further
in the stream than other productions, which failed right at the very first token.

However, if span information is not available or not useful (i.e., when every
production is spanned to the same `Span::call_site()` source location), then this
heuristic breaks down, and it will select an arbitrary production, resulting in
subpar error messages. This means that you should try to preserve spans as much
as possible. This in turn implies that using `syn::parse_str()` for parsing code
outside procedural macros is preferable to using `syn::parse2()`, because the
former will result in a usefully-spanned AST, while the latter will not, at least
not when used on e.g. a `TokenStream` obtained via `quote!()` or `parse_quote!()`.

### Roadmap, TODOs

* [ ] Document all of the public API
* [ ] Document all of the non-public API as well
* [ ] Allow specifying custom error messages for each production/AST node type
    * [ ] Allow conditions/sorting criteria/other customization for discovering
          the best production/error message to report when parsing alternation
* [x] `enum Either` AST helper type for basic binary alternation
* [x] `Any` AST helper type for parsing until a given production succeeds. Unlike
      `Many`, it doesn't require the productions to extend until end-of-input.
* [x] Implement `AsRef`, `Deref`, and `Borrow` consistently for wrapper types
      (e.g., `Paren`, `Bracket`, `Brace`)
* [ ] Make the error reporting heuristic for alternation (based on the furthest
      parsing production) work even when span information is not useful. **Nota
      bene:** this absolutely **shouldn't** be done by just counting the number
      of tokens/bytes in the remaining input, because that will result in an
      **accidentally quadratic parsing performance!**
