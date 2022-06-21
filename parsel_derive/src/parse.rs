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
    // these are passed to `chain_error()` for describing the production currently being parsed
    let enum_str = enum_name.map(Ident::to_string).unwrap_or_default();
    let ctor_str = ctor_name.to_string();
    let enum_name = enum_name.into_iter();

    match fields {
        Fields::Named(fields) => {
            let inits: Vec<_> = fields.named
                .iter()
                .map(|field| {
                    let field_name = field.ident.as_ref().ok_or_else(|| {
                        Error::new(ctor_name.span(), "unnamed field in named struct")
                    })?;
                    let field_str = field_name.to_string();

                    Ok(quote!{
                        #field_name: input.parse().map_err(|cause| {
                            ::parsel::util::chain_error(cause, #enum_str, #ctor_str, #field_str)
                        })?
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
            let inits = fields.unnamed.iter().enumerate().map(|(index, _)| {
                quote!{
                    input.parse().map_err(|cause| {
                        ::parsel::util::chain_error(cause, #enum_str, #ctor_str, #index)
                    })?
                }
            });

            Ok(quote!{
                let ast_node = #(#enum_name::)* #ctor_name(#(#inits),*);
                ::parsel::Result::Ok(ast_node)
            })
        }
        Fields::Unit => {
            Ok(quote!{
                ::parsel::Result::Ok(#(#enum_name::)* #ctor_name)
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
                        errors.push(cause);
                    }
                }
            })
        })
        .collect()
}
