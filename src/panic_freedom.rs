use crate::attribute::RedpenAttribute;
use crate::reachability_check::{Config, ReachabilityCheck};
use rustc_lint::Lint;
use rustc_session::{declare_tool_lint, impl_lint_pass};

pub struct DontPanic;

impl Config for DontPanic {
    fn new() -> DontPanic {
        DontPanic
    }

    fn lint(&self) -> &'static Lint {
        PANICS
    }

    fn is_relevant_leaf(&self, path: &str) -> bool {
        [
            "<usize as std::slice::SliceIndex<[T]>>::index",
            "<usize as std::slice::SliceIndex<[T]>>::index_mut",
            "core::panicking::panic_explicit",
            "core::panicking::panic_fmt",
            "core::panicking::panic",
            "std::rt::panic_fmt",
        ]
        .contains(&path)
    }

    fn is_disabled_scope(&self, attr: &RedpenAttribute) -> bool {
        matches!(attr, RedpenAttribute::WontPanic)
    }
    fn affected_description(&self) -> &'static str {
        "can panic"
    }
}

declare_tool_lint! {
    pub redpen::PANICS,
    Allow,
    "The marked function cannot transitively call `panic!()`"
}

impl_lint_pass!(ReachabilityCheck<'_, DontPanic> => [PANICS]);

pub type PanicFreedom<'a> = ReachabilityCheck<'a, DontPanic>;
