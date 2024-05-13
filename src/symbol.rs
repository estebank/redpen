#![allow(non_upper_case_globals)]

use rustc_span::Symbol;
use std::sync::LazyLock;

macro_rules! def {
    ($($name: ident,)*) => {
        $(pub static $name: LazyLock<Symbol> = LazyLock::new(|| Symbol::intern(stringify!($name)));)*
    };
}

def! {
    allow,
    deny,
    assume_ok,
    assume_bad,
    redpen,
}
