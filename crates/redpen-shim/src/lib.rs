//! This crate only exists so that users of `redpen` can build their code
//! using their regular workflow without causing "unknown tool" errors.

extern crate proc_macro;
use proc_macro::TokenStream;

#[proc_macro_attribute]
pub fn deny(_attr: TokenStream, item: TokenStream) -> TokenStream {
    item
}

#[proc_macro_attribute]
pub fn allow(_attr: TokenStream, item: TokenStream) -> TokenStream {
    item
}

#[proc_macro_attribute]
pub fn assume_ok(_attr: TokenStream, item: TokenStream) -> TokenStream {
    item
}

#[proc_macro_attribute]
pub fn assume_bad(_attr: TokenStream, item: TokenStream) -> TokenStream {
    item
}