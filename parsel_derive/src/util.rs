//! Helpers that don't fit anywhere else.

use std::collections::HashSet;
use proc_macro::TokenStream;
use proc_macro2::TokenStream as TokenStream2;
use darling::FromMeta;
use syn::parse_quote;
use syn::punctuated::Punctuated;
use syn::{Error, Result, Token, DeriveInput, Fields, Data, Field, Type};
use syn::{WhereClause, WherePredicate, TypeParamBound, Attribute, NestedMeta};


/// Generates a `where` clause with the specified bounds applied to all field types.
pub fn add_bounds(
    input: &DeriveInput,
    where_clause: Option<&WhereClause>,
    bounds: Punctuated<TypeParamBound, Token![+]>,
) -> Result<WhereClause> {
    let unique_types: HashSet<_> = match &input.data {
        Data::Union(_) => return Err(Error::new_spanned(input, "unions are not supported")),
        Data::Struct(data) => match &data.fields {
            Fields::Unit => HashSet::new(),
            Fields::Named(fields) => {
                fields.named
                    .iter()
                    .filter_map(|f| field_type(f).transpose())
                    .collect::<Result<_>>()?
            }
            Fields::Unnamed(fields) => {
                fields.unnamed
                    .iter()
                    .filter_map(|f| field_type(f).transpose())
                    .collect::<Result<_>>()?
            }
        },
        Data::Enum(data) => {
            data.variants
                .iter()
                .flat_map(|v| {
                    match &v.fields {
                        Fields::Unit => Vec::new(),
                        Fields::Named(fields) => {
                            fields.named
                                .iter()
                                .filter_map(|f| field_type(f).transpose())
                                .collect::<Vec<_>>()
                        }
                        Fields::Unnamed(fields) => {
                            fields.unnamed
                                .iter()
                                .filter_map(|f| field_type(f).transpose())
                                .collect::<Vec<_>>()
                        }
                    }
                })
                .collect::<Result<_>>()?
        }
    };

    let mut where_clause = where_clause.cloned().unwrap_or_else(|| {
        WhereClause {
            where_token: Default::default(),
            predicates: Default::default(),
        }
    });

    where_clause.predicates.extend(
        unique_types.iter().map(|ty| -> WherePredicate {
            parse_quote!{
                #ty: #bounds
            }
        })
    );

    Ok(where_clause)
}

/// Return the type of the field if it isn't marked
/// with the `#[parsel(recursive)]` attribute.
fn field_type(field: &Field) -> Result<Option<&Type>> {
    let attrs = Attrs::new(field.attrs.clone())?;
    let ty = if attrs.recursive {
        None
    } else {
        Some(&field.ty)
    };

    Ok(ty)
}

/// Wraps a fallible derive function so that it accepts and returns a `proc_macro::TokenStream`.
pub fn wrap_derive<F>(expand: F, ts: TokenStream) -> TokenStream
where
    F: FnOnce(TokenStream2) -> Result<TokenStream2>,
{
    expand(ts.into())
        .unwrap_or_else(Error::into_compile_error)
        .into()
}

/// Helper type for parsing the meta attributes of the
/// type for which `Parse` and `ToTokens` are being `#[derive]`d.
#[derive(Clone, Default, Debug, FromMeta)]
#[darling(default)]
pub struct Attrs {
    /// Indicates that the field participates in (possibly mutual) recursion
    /// at the type level, e.g. a parent-child relationship within the same
    /// struct/enum. The type of such fields will be omitted from the `where`
    /// clause in the derived implementations, becuse the corresponding
    /// constraints can't be satisfied, and the code compiles without them.
    ///
    /// Hopefully, this can be removed in the future once Chalk lands;
    /// see [this issue](https://github.com/rust-lang/rust/issues/48214)
    pub recursive: bool,
}

impl Attrs {
    pub fn new<I>(iter: I) -> Result<Self>
    where
        I: IntoIterator<Item = Attribute>,
    {
        // Combine all `neodyn(...)` attributes into one list, in
        // order to rely on Darling's built-in duplicate detection.
        iter
            .into_iter()
            .filter_map(|attr| {
                if attr.path == parse_quote!(parsel) {
                    Some(attr.parse_args().map(NestedMeta::Meta).map_err(From::from))
                } else {
                    None
                }
            })
            .collect::<darling::Result<Vec<_>>>()
            .and_then(|metas| Attrs::from_list(&metas))
            .map_err(From::from)
    }
}
