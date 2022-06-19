use core::iter::FromIterator;
use anyhow::{ensure, Result};
use parsel::quote::quote;
use parsel::{Parse, ToTokens};
use parsel::ast::{token, ident, Many, Brace, Ident};


#[derive(PartialEq, Eq, Debug, Parse, ToTokens)]
struct Struct {
    struct_kw: token::Struct,
    name: Ident,
    fields: Brace<Many<Field>>,
}

#[derive(PartialEq, Eq, Debug, Parse, ToTokens)]
struct Field {
    name: Ident,
    colon: token::Colon,
    ty: Ident,
    comma: token::Comma,
}

#[derive(PartialEq, Eq, Debug, Parse, ToTokens)]
struct Enum {
    enum_kw: token::Enum,
    name: Ident,
    variants: Brace<Many<Variant>>,
}

#[derive(PartialEq, Eq, Debug, Parse, ToTokens)]
struct Variant(Ident, token::Comma);

#[derive(PartialEq, Eq, Debug, Parse, ToTokens)]
enum Item {
    Struct(Struct),
    Enum(Enum),
}

#[test]
fn parse_of_to_tokens_is_identity() -> Result<()> {
    let ast_original = Many::from_iter([
        Item::Struct(Struct {
            struct_kw: Default::default(),
            name: ident("ThisIsANewtypeStruct"),
            fields: Brace::from(
                Many::from_iter([
                    Field {
                        name: ident("inner"),
                        colon: Default::default(),
                        ty: ident("ThisIsAnEmptyStruct"),
                        comma: Default::default(),
                    }
                ])
            ),
        }),
        Item::Enum(Enum {
            enum_kw: Default::default(),
            name: ident("Option"),
            variants: Brace::from(
                Many::from_iter([
                    Variant(ident("None"), Default::default()),
                    Variant(ident("Some"), Default::default()),
                ]),
            ),
        }),
        Item::Struct(Struct {
            struct_kw: Default::default(),
            name: ident("ThisIsAnEmptyStruct"),
            fields: Brace::default(),
        }),
    ]);
    let ts = ast_original.to_token_stream();
    let ast_parsed: Many<Item> = parsel::parse2(ts)?;

    ensure!(
        ast_parsed == ast_original,
        "parsed: {:#?}\noriginal:\n{:#?}",
        ast_parsed, ast_original,
    );

    Ok(())
}

#[test]
fn to_tokens_of_parse_is_identity() -> Result<()> {
    let ts_original = quote!{
        enum Bool {
            False,
            True,
        }

        struct Foo {
            bar: Bar,
            baz: Qux,
            lol: What,
        }
    };
    let parsed: Many<Item> = parsel::parse2(ts_original.clone())?;
    let ts_emitted = parsed.to_token_stream();

    ensure!(
        ts_emitted.to_string().trim() == ts_original.to_string().trim(),
        "emitted:\n{}\noriginal:\n{}",
        ts_emitted, ts_original,
    );

    Ok(())
}
