//! Actual implementation of `#[derive(Display)]`.

use proc_macro2::TokenStream;
use syn::{parse_quote, Result, DeriveInput, WhereClause};
use quote::quote;


/// Actual implementation of `#[derive(Display)]`.
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
        Self: ::parsel::ToTokens
    });

    Ok(quote!{
        #[automatically_derived]
        impl #impl_gen ::core::fmt::Display for #ty_name #ty_gen #where_clause {
            fn fmt(&self, formatter: &mut ::core::fmt::Formatter<'_>) -> ::core::fmt::Result {
                let stream = ::parsel::ToTokens::to_token_stream(self);
                let mut ts_fmt = ::parsel::util::TokenStreamFormatter::new(formatter);
                ts_fmt.write(stream)
            }
        }
    })
}
