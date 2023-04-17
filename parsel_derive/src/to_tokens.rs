//! Actual implementation of `#[derive(ToTokens)]`.

use proc_macro2::TokenStream;
use syn::{Error, Result, DeriveInput, Data, DataStruct, DataEnum, Fields};
use syn::{Ident, Index};
use syn::spanned::Spanned;
use syn::parse_quote;
use quote::{quote, format_ident};
use crate::util::add_bounds;


/// Actual implementation of `#[derive(ToTokens)]`.
pub fn expand(stream: TokenStream) -> Result<TokenStream> {
    let item: DeriveInput = syn::parse2(stream)?;
    let ty_name = item.ident.clone();

    let body = match &item.data {
        Data::Union(_) => return Err(Error::new_spanned(&item, "unions are not supported")),
        Data::Enum(data) => expand_enum(&ty_name, data)?,
        Data::Struct(data) => expand_struct(data)?,
    };
    let generics = item.generics.clone();
    let (impl_gen, ty_gen, where_clause) = generics.split_for_impl();
    let bounds = parse_quote!(::parsel::ToTokens);
    let where_clause = add_bounds(item, where_clause, bounds)?;

    Ok(quote!{
        #[automatically_derived]
        #[allow(non_snake_case)]
        impl #impl_gen ::parsel::ToTokens for #ty_name #ty_gen #where_clause {
            fn to_tokens(&self, tokens: &mut ::parsel::TokenStream) {
                #body
            }
        }
    })
}

/// Prints every field in sequence, in the order they are specified in the source.
fn expand_struct(data: &DataStruct) -> Result<TokenStream> {
    match &data.fields {
        Fields::Named(fields) => {
            fields.named
                .iter()
                .map(|field| {
                    let field_name = field.ident.as_ref().ok_or_else(|| {
                        Error::new(field.span(), "unnamed field in named struct")
                    })?;

                    Ok(quote!{
                        ::parsel::ToTokens::to_tokens(&self.#field_name, &mut *tokens);
                    })
                })
                .collect()
        }
        Fields::Unnamed(fields) => {
            fields.unnamed
                .iter()
                .zip(0..)
                .map(|(field, index)| {
                    let span = field.span();
                    let field_index = Index { index, span };

                    Ok(quote!{
                        ::parsel::ToTokens::to_tokens(&self.#field_index, &mut *tokens);
                    })
                })
                .collect()
        }
        Fields::Unit => Ok(TokenStream::new())
    }
}

fn expand_enum(ty_name: &Ident, data: &DataEnum) -> Result<TokenStream> {
    let body = expand_variants(ty_name, data)?;

    Ok(quote!{
        match self {
            #body
        }
    })
}

/// Generates a `match` so that the fields of the currently active variant
/// will be appended to the token stream.
fn expand_variants(ty_name: &Ident, data: &DataEnum) -> Result<TokenStream> {
    data.variants
        .iter()
        .map(|variant| {
            let variant_name = &variant.ident;
            let field_names = match &variant.fields {
                Fields::Unit => Vec::new(),
                Fields::Named(fields) => {
                    fields.named
                        .iter()
                        .map(|field| {
                            field.ident.clone().ok_or_else(|| {
                                Error::new(field.span(), "unnamed field in named struct")
                            })
                        })
                        .collect::<Result<_>>()?
                }
                Fields::Unnamed(fields) => {
                    fields.unnamed
                        .iter()
                        .enumerate()
                        .map(|(i, _)| format_ident!("parsel_field_{}_{}", variant_name, i))
                        .collect()
                }
            };
            let bindings = match &variant.fields {
                Fields::Unit => TokenStream::new(),
                Fields::Named(_) => quote!({ #(#field_names,)* }),
                Fields::Unnamed(_) => quote!{ (#(#field_names),*) },
            };

            Ok(quote!{
                #ty_name::#variant_name #bindings => {
                    #(::parsel::ToTokens::to_tokens(#field_names, &mut *tokens);)*
                }
            })
        })
        .collect()
}
