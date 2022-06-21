#![doc = include_str!(concat!(env!("CARGO_MANIFEST_DIR"), "/README.md"))]

#![forbid(unsafe_code)]
#![warn(elided_lifetimes_in_paths, keyword_idents, macro_use_extern_crate, meta_variable_misuse,
       missing_abi, missing_copy_implementations, missing_debug_implementations,
       non_ascii_idents, noop_method_call, pointer_structural_match, single_use_lifetimes,
       trivial_casts, trivial_numeric_casts, unsafe_op_in_unsafe_fn, unused_extern_crates,
       unused_import_braces, unused_lifetimes, unused_qualifications, unused_results,
       variant_size_differences)]
#![warn(clippy::cast_lossless, clippy::cast_possible_truncation, clippy::cast_possible_wrap,
        clippy::cast_precision_loss, clippy::cast_ptr_alignment, clippy::cast_sign_loss,
        clippy::checked_conversions, clippy::cloned_instead_of_copied,
        clippy::cognitive_complexity, clippy::copy_iterator, clippy::create_dir,
        clippy::dbg_macro, clippy::debug_assert_with_mut_call,
        clippy::decimal_literal_representation, clippy::default_numeric_fallback,
        clippy::disallowed_script_idents, clippy::doc_markdown, clippy::else_if_without_else,
        clippy::empty_line_after_outer_attr,  clippy::enum_glob_use, clippy::exit,
        clippy::expl_impl_clone_on_copy, clippy::explicit_deref_methods,
        clippy::explicit_into_iter_loop, clippy::explicit_iter_loop, clippy::fallible_impl_from,
        clippy::filter_map_next, clippy::flat_map_option, clippy::float_cmp,
        clippy::float_cmp_const, clippy::future_not_send, clippy::get_unwrap,
        clippy::if_not_else, clippy::implicit_clone, clippy::implicit_hasher,
        clippy::implicit_saturating_sub, clippy::imprecise_flops,
        clippy::inconsistent_struct_constructor, clippy::inefficient_to_string,
        clippy::inline_always, clippy::invalid_upcast_comparisons,
        clippy::items_after_statements, clippy::large_digit_groups,
        clippy::let_underscore_drop, clippy::linkedlist, clippy::lossy_float_literal,
        clippy::macro_use_imports, clippy::manual_ok_or, clippy::many_single_char_names,
        clippy::map_err_ignore, clippy::map_unwrap_or, clippy::match_bool,
        clippy::match_on_vec_items, clippy::match_same_arms, clippy::match_wild_err_arm,
        clippy::match_wildcard_for_single_variants, clippy::mem_forget,
        clippy::module_name_repetitions, clippy::multiple_crate_versions, clippy::mut_mut,
        clippy::mutex_atomic, clippy::mutex_integer, clippy::needless_continue,
        clippy::needless_for_each, clippy::nonstandard_macro_braces, clippy::option_option,
        clippy::panic, clippy::panic_in_result_fn, clippy::path_buf_push_overwrite,
        clippy::print_stderr, clippy::print_stdout, clippy::ptr_as_ptr, clippy::range_minus_one,
        clippy::range_plus_one, clippy::rc_buffer, clippy::rc_mutex,
        clippy::redundant_closure_for_method_calls,
        clippy::redundant_pub_crate, clippy::ref_binding_to_reference, clippy::ref_option_ref,
        clippy::rest_pat_in_fully_bound_structs, clippy::same_functions_in_if_condition,
        clippy::semicolon_if_nothing_returned, clippy::shadow_unrelated, clippy::similar_names,
        clippy::single_match_else, clippy::stable_sort_primitive, clippy::str_to_string,
        clippy::string_add, clippy::string_add_assign, clippy::string_lit_as_bytes,
        clippy::string_to_string, clippy::suboptimal_flops,
        clippy::suspicious_operation_groupings, clippy::todo, clippy::too_many_lines,
        clippy::trait_duplication_in_bounds, clippy::transmute_ptr_to_ptr,
        clippy::trivial_regex, clippy::try_err, clippy::type_repetition_in_bounds,
        clippy::unicode_not_nfc, clippy::unimplemented, clippy::unnecessary_self_imports,
        clippy::unnecessary_wraps, clippy::unneeded_field_pattern, clippy::unnested_or_patterns,
        clippy::unreadable_literal, clippy::unsafe_derive_deserialize,
        clippy::unseparated_literal_suffix, clippy::unused_async, clippy::unused_self,
        clippy::unwrap_in_result, clippy::unwrap_used, clippy::use_debug,
        clippy::used_underscore_binding, clippy::useless_let_if_seq,
        clippy::verbose_file_reads, clippy::while_let_on_iterator,
        clippy::wildcard_dependencies, clippy::wildcard_imports, clippy::zero_sized_map_values)]

pub use proc_macro2;
pub use syn;
pub use quote;

pub use core::str::FromStr;
pub use core::fmt::Display;
pub use proc_macro2::{TokenStream, TokenTree, Span};
pub use ordered_float::NotNan;
pub use syn::parse::{Parse, Error, Result};
pub use syn::{parse2, parse_str};
pub use syn::{parse_quote, parse_quote_spanned, custom_keyword, custom_punctuation};
pub use syn::spanned::Spanned;
pub use quote::ToTokens;
pub use parsel_derive::{Parse, ToTokens, FromStr, Display};

pub mod ast;
pub mod util;
