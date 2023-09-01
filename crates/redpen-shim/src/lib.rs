//! This crate only exists so that users of `redpen` can build their code
//! using their regular workflow without causing "unknown tool" errors.

extern crate proc_macro;
use proc_macro::TokenStream;

#[proc_macro_attribute]
pub fn wont_panic(_attr: TokenStream, item: TokenStream) -> TokenStream {
    item
}
#[proc_macro_attribute]
pub fn dont_panic(_attr: TokenStream, item: TokenStream) -> TokenStream {
    item
}
#[proc_macro_attribute]
pub fn disallow(_attr: TokenStream, item: TokenStream) -> TokenStream {
    item
}
