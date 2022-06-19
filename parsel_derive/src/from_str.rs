//! Actual implementation of `#[derive(FromStr)]`.

use proc_macro2::TokenStream;
use syn::{parse_quote, Result, DeriveInput, WhereClause};
use quote::quote;


/// Actual implementation of `#[derive(FromStr)]`.
pub fn expand(stream: TokenStream) -> Result<TokenStream> {
    let item: DeriveInput = syn::parse2(stream)?;
    let ty_name = &item.ident;
    let (impl_gen, ty_gen, where_clause) = item.generics.split_for_impl();

    let mut where_clause = where_clause.cloned().unwrap_or_else(|| {
        WhereClause {
            where_token: Default::default(),
            predicates: Default::default(),
        }
    });

    where_clause.predicates.push(parse_quote!{
        Self: ::parsel::Parse
    });

    Ok(quote!{
        #[automatically_derived]
        impl #impl_gen ::core::str::FromStr for #ty_name #ty_gen #where_clause {
            type Err = ::parsel::Error;

            fn from_str(string: &::core::primitive::str) -> ::parsel::Result<Self> {
                ::parsel::parse_str(string)
            }
        }
    })
}
