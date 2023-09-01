#![allow(non_upper_case_globals)]

use rustc_span::Symbol;
use std::sync::LazyLock;

macro_rules! def {
    ($($name: ident,)*) => {
        $(pub static $name: LazyLock<Symbol> = LazyLock::new(|| Symbol::intern(stringify!($name)));)*
    };
}

def! {
    Waker,
    Write,
    adjust,
    disallow,
    dont_panic,
    drop_preempt_count,
    dump_mir,
    error,
    expect,
    index,
    redpen,
    preempt_count,
    report_preempt_count,
    task,
    unchecked,
    wake,
    wake_by_ref,
    wont_panic,
    write,
}
