//! Actual implementation of `#[derive(Parse)]`.

use proc_macro2::TokenStream;
use syn::{Error, Result, DeriveInput, Data, DataStruct, DataEnum, Fields, Variant};
use syn::{Token, Ident};
use syn::punctuated::Punctuated;
use syn::parse_quote;
use quote::{quote, format_ident};
use crate::util::add_bounds;


/// Actual implementation of `#[derive(Parse)]`.
pub fn expand(stream: TokenStream) -> Result<TokenStream> {
    let item: DeriveInput = syn::parse2(stream)?;
    let ty_name = &item.ident;

    let body = match &item.data {
        Data::Union(_) => return Err(Error::new(ty_name.span(), "unions are not supported")),
        Data::Enum(data) => expand_enum(ty_name, data)?,
        Data::Struct(data) => expand_struct(ty_name, data)?,
    };

    let (impl_gen, ty_gen, where_clause) = item.generics.split_for_impl();
    let bounds = parse_quote!(::parsel::Parse);
    let where_clause = add_bounds(&item, where_clause, bounds)?;

    Ok(quote!{
        #[automatically_derived]
        #[allow(non_snake_case)]
        impl #impl_gen ::parsel::Parse for #ty_name #ty_gen #where_clause {
            fn parse(input: ::parsel::syn::parse::ParseStream<'_>) -> ::parsel::Result<Self> {
                #body
            }
        }
    })
}

fn expand_struct(ty_name: &Ident, data: &DataStruct) -> Result<TokenStream> {
    expand_fields(None, ty_name, &data.fields)
}

/// Parses every field in sequence, in the order they are specified in the source.
fn expand_fields(enum_name: Option<&Ident>, ctor_name: &Ident, fields: &Fields) -> Result<TokenStream> {
    let enum_name = enum_name.into_iter();
    match fields {
        Fields::Named(fields) => {
            let inits: Vec<_> = fields.named
                .iter()
                .map(|field| {
                    let field_name = field.ident.as_ref().ok_or_else(|| {
                        Error::new(ctor_name.span(), "unnamed field in named struct")
                    })?;

                    Ok(quote!{
                        #field_name: ::parsel::syn::parse::ParseBuffer::parse(input)?
                    })
                })
                .collect::<Result<_>>()?;

            Ok(quote!{
                let ast_node = #(#enum_name::)* #ctor_name {
                    #(#inits,)*
                };
                ::parsel::Result::Ok(ast_node)
            })
        }
        Fields::Unnamed(fields) => {
            let inits = fields.unnamed.iter().map(|_| {
                quote!{ ::parsel::syn::parse::ParseBuffer::parse(input)? }
            });

            Ok(quote!{
                let ast_node = #(#enum_name::)* #ctor_name(#(#inits),*);
                ::parsel::Result::Ok(ast_node)
            })
        }
        Fields::Unit => {
            Ok(quote!{
                let ast_node = #(#enum_name::)* #ctor_name;
                ::parsel::Result::Ok(ast_node)
            })
        }
    }
}

fn expand_enum(ty_name: &Ident, data: &DataEnum) -> Result<TokenStream> {
    let parsers = expand_variants(ty_name, &data.variants)?;

    Ok(quote!{
        // This is only added so that the non-inherent methods don't break.
        use ::core::iter::{Iterator, IntoIterator};

        let mut errors = ::std::vec::Vec::new();

        #parsers

        // Heuristic: choose the error that got the furthest in parsing.
        // That is likely to be the thing that is _actually_ being parsed.
        // If no variant succeeds but there are no errors, then the
        // enum to be parsed was uninhabited (no variants). Return an
        // appropriate error in this case.
        let error = errors
            .into_iter()
            .max_by_key(|e| e.span().end())
            .unwrap_or_else(|| input.error("parsing an empty choice (enum) always fails"));

        ::parsel::Result::Err(error)
    })
}

/// Attempts to parse each variant, one after another, in the order specified in the source.
/// The first one that parses successfully wins.
fn expand_variants(ty_name: &Ident, variants: &Punctuated<Variant, Token![,]>) -> Result<TokenStream> {
    variants
        .iter()
        .map(|variant| {
            let variant_name = &variant.ident;
            let body = expand_fields(Some(ty_name), variant_name, &variant.fields)?;

            let fork_name = format_ident!("parsel_fork_{}", variant_name);
            let parser_fn_name = format_ident!("parsel_parse_{}", variant_name);
            let ty_str = ty_name.to_string();
            let variant_str = variant_name.to_string();

            Ok(quote!{
                let #parser_fn_name = |input: ::parsel::syn::parse::ParseStream<'_>| -> ::parsel::Result<_> {
                    #body
                };
                let #fork_name = ::parsel::syn::parse::ParseBuffer::fork(input);

                match #parser_fn_name(&#fork_name) {
                    ::parsel::Result::Ok(ast) => {
                        ::parsel::syn::parse::discouraged::Speculative::advance_to(
                            input,
                            &#fork_name
                        );
                        return ::parsel::Result::Ok(ast);
                    }
                    ::parsel::Result::Err(cause) => {
                        let err = ::parsel::util::chain_error(&cause, #ty_str, #variant_str);
                        errors.push(err);
                    }
                }
            })
        })
        .collect()
}
