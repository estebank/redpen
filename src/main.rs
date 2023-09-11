#![feature(rustc_private)]
#![feature(lazy_cell)]
#![feature(min_specialization)]
#![feature(box_patterns)]
#![feature(if_let_guard)]
#![feature(let_chains)]
#![feature(never_type)]
#![warn(rustc::internal)]
#![allow(rustc::potential_query_instability)]

extern crate rustc_ast;
extern crate rustc_data_structures;
extern crate rustc_driver;
extern crate rustc_errors;
extern crate rustc_hir;
extern crate rustc_hir_typeck;
extern crate rustc_index;
extern crate rustc_infer;
extern crate rustc_interface;
extern crate rustc_lint;
extern crate rustc_macros;
extern crate rustc_middle;
extern crate rustc_mir_dataflow;
extern crate rustc_monomorphize;
extern crate rustc_serialize;
extern crate rustc_session;
extern crate rustc_span;
extern crate rustc_symbol_mangling;
extern crate rustc_target;
extern crate rustc_trait_selection;

#[macro_use]
extern crate tracing;

use std::process::ExitCode;
use std::sync::atomic::AtomicPtr;

use rustc_driver::Callbacks;
use rustc_interface::interface::Config;
use rustc_session::config::ErrorOutputType;
use rustc_session::EarlyErrorHandler;
use std::sync::atomic::Ordering;
use rustc_hir::{Item, ItemKind, Impl, def::{DefKind, Res}};

use crate::attribute::RedpenAttribute;

mod attribute;
mod disallow;
mod infallible_allocation;
mod monomorphize_collector;
// mod panic_freedom;
mod reachability_check;
mod symbol;

rustc_session::declare_tool_lint! {
    pub redpen::INCORRECT_ATTRIBUTE,
    Forbid,
    "Incorrect usage of redpen attributes"
}

struct MyCallbacks;

impl Callbacks for MyCallbacks {
    fn config(&mut self, config: &mut Config) {
        config.override_queries = Some(|_, provider, _| {
            static ORIGINAL_OPTIMIZED_MIR: AtomicPtr<()> = AtomicPtr::new(std::ptr::null_mut());

            ORIGINAL_OPTIMIZED_MIR.store(provider.optimized_mir as *mut (), Ordering::Relaxed);
            provider.optimized_mir = |tcx, def_id| {
                // Calling `optimized_mir` will steal the result of query `mir_drops_elaborated_and_const_checked`,
                // so hijack `optimized_mir` to run `analysis_mir` first.

                // // Skip `analysis_mir` call if this is a constructor, since it will be delegated back to
                // // `optimized_mir` for building ADT constructor shim.
                // if !tcx.is_constructor(def_id.to_def_id()) {
                //     crate::mir::local_analysis_mir(tcx, def_id);
                // }

                let ptr = ORIGINAL_OPTIMIZED_MIR.load(Ordering::Relaxed);
                assert!(!ptr.is_null());
                let original_optimized_mir =
                    unsafe { std::mem::transmute::<*mut (), fn(_, _) -> _>(ptr) };
                original_optimized_mir(tcx, def_id)
            };
        });
        config.register_lints = Some(Box::new(move |sess, lint_store| {
            // Skip checks for proc-macro crates.
            if rustc_interface::util::collect_crate_types(sess, &[])
                .contains(&rustc_session::config::CrateType::ProcMacro)
            {
                return;
            }

            lint_store.register_lints(&[
                &INCORRECT_ATTRIBUTE,
                &disallow::DISALLOW,
                &reachability_check::DONT_PANIC,
                &reachability_check::DONT_PANIC_IN_DROP,
                &reachability_check::DONT_ALLOCATE,
                &reachability_check::DONT_LEAK,
                &reachability_check::FROM_RAW_PARTS,
                &reachability_check::CALL_UNSAFE,
                &infallible_allocation::INFALLIBLE_ALLOCATION,
            ]);

            lint_store.register_late_pass(|tcx| Box::new(disallow::Disallow::new(tcx)));
            let panic_paths = &[
                "<usize as std::slice::SliceIndex<[T]>>::index",
                "<usize as std::slice::SliceIndex<[T]>>::index_mut",
                "core::panicking::panic_fmt",
                "core::panicking::panic",
                "std::rt::panic_fmt",

                // "core::num::<impl u8>::checked_add",
                // "core::num::<impl u16>::checked_add",
                // "core::num::<impl u32>::checked_add",
                // "core::num::<impl u64>::checked_add",
                // "core::num::<impl u128>::checked_add",
                // "core::num::<impl usize>::checked_add",
                // "core::num::<impl i8>::checked_add",
                // "core::num::<impl i16>::checked_add",
                // "core::num::<impl i32>::checked_add",
                // "core::num::<impl i64>::checked_add",
                // "core::num::<impl i128>::checked_add",
                // "core::num::<impl isize>::checked_add",

                // "core::num::<impl u8>::checked_sub",
                // "core::num::<impl u16>::checked_sub",
                // "core::num::<impl u32>::checked_sub",
                // "core::num::<impl u64>::checked_sub",
                // "core::num::<impl u128>::checked_sub",
                // "core::num::<impl usize>::checked_sub",
                // "core::num::<impl i8>::checked_sub",
                // "core::num::<impl i16>::checked_sub",
                // "core::num::<impl i32>::checked_sub",
                // "core::num::<impl i64>::checked_sub",
                // "core::num::<impl i128>::checked_sub",
                // "core::num::<impl isize>::checked_sub",
            ];
            lint_store.register_late_pass(|tcx| {
                Box::new(reachability_check::UnsafetyCheck::new(
                    tcx,
                    RedpenAttribute::WontPanic,
                    &[],
                    "unsafe",
                    reachability_check::CALL_UNSAFE,
                    true,
                    Box::new(|_, _| true),
                ))
            });
            // lint_store.register_late_pass(|tcx| {
            //     Box::new(reachability_check::ReachabilityCheck::new(
            //         tcx,
            //         RedpenAttribute::WontPanic,
            //         panic_paths,
            //         "panic",
            //         reachability_check::DONT_PANIC,
            //         true,
            //         Box::new(|_, _| true),
            //     ))
            // });
            // lint_store.register_late_pass(|tcx| {
            //     Box::new(reachability_check::ReachabilityCheck::new(
            //         tcx,
            //         RedpenAttribute::WontPanic,
            //         panic_paths,
            //         "panic in a `Drop` implementation",
            //         reachability_check::DONT_PANIC_IN_DROP,
            //         true,
            //         Box::new(|tcx, def_id| {
            //             if tcx.def_kind(def_id) != DefKind::AssocFn {
            //                 return false;
            //             }
            //             let def_id = tcx.parent(def_id);
            //             let item = tcx.hir().expect_item(def_id.expect_local());
            //             let ItemKind::Impl(Impl { of_trait: Some(item), .. }) = item.kind else {
            //                 return false;
            //             };
            //             let Res::Def(_, trait_def_id) = item.path.res else {
            //                 return false;
            //             };
            //             Some(trait_def_id) == tcx.lang_items().drop_trait()
            //         }),
            //     ))
            // });
            // lint_store.register_late_pass(|tcx| {
            //     Box::new(reachability_check::ReachabilityCheck::new(
            //         tcx,
            //         RedpenAttribute::WontAllocate,
            //         &[
            //             "alloc::alloc::__rust_alloc",
            //             "alloc::alloc::__rust_alloc_zeroed",
            //             "alloc::alloc::__rust_realloc",
            //             "alloc::alloc::__rust_dealloc",
            //             // Fallible allocation function
            //             "alloc::string::String::try_reserve",
            //             "alloc::string::String::try_reserve_exact",
            //         ],
            //         "allocate",
            //         reachability_check::DONT_ALLOCATE,
            //         true,
            //         Box::new(|_, _| true),
            //     ))
            // });
            // lint_store.register_late_pass(|tcx| {
            //     Box::new(reachability_check::ReachabilityCheck::new(
            //         tcx,
            //         RedpenAttribute::WontLeak,
            //         &[
            //             "std::mem::forget",
            //             "std::boxed::Box::<T, A>::leak",
            //             "std::slice::from_raw_parts",
            //         ],
            //         "leak memory",
            //         reachability_check::DONT_LEAK,
            //         false,
            //         Box::new(|_, _| true),
            //     ))
            // });
            // lint_store.register_late_pass(|tcx| {
            //     Box::new(reachability_check::ReachabilityCheck::new(
            //         tcx,
            //         RedpenAttribute::WontLeak,
            //         &[
            //             "std::process::exit",
            //         ],
            //         "terminate the process",
            //         reachability_check::DONT_LEAK,
            //         true,
            //         Box::new(|_, _| true),
            //     ))
            // });
            // lint_store.register_late_pass(|tcx| {
            //     Box::new(reachability_check::ReachabilityCheck::new(
            //         tcx,
            //         RedpenAttribute::WontLeak,
            //         &[
            //         ],
            //         "call `std::slice::from_raw_parts`",
            //         reachability_check::FROM_RAW_PARTS,
            //         false,
            //         Box::new(|_, _| true),
            //     ))
            // });


        }));
    }
}

fn main() -> ExitCode {
    let handler = EarlyErrorHandler::new(ErrorOutputType::default());
    rustc_driver::init_env_logger(&handler, "REDPEN_LOG");
    let args: Vec<_> = std::env::args().collect();

    match rustc_driver::RunCompiler::new(&args, &mut MyCallbacks).run() {
        Ok(_) => ExitCode::SUCCESS,
        Err(_) => ExitCode::FAILURE,
    }
}
