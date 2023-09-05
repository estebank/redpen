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

mod attribute;
mod disallow;
mod infallible_allocation;
mod monomorphize_collector;
mod panic_freedom;
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
            if sess
                .crate_types()
                .contains(&rustc_session::config::CrateType::ProcMacro)
            {
                return;
            }

            lint_store.register_lints(&[
                &INCORRECT_ATTRIBUTE,
                &disallow::DISALLOW,
                &panic_freedom::DONT_PANIC,
                &infallible_allocation::INFALLIBLE_ALLOCATION,
            ]);
            lint_store.register_late_pass(|tcx| Box::new(disallow::Disallow::new(tcx)));
            lint_store.register_late_pass(|tcx| Box::new(panic_freedom::DontPanic::new(tcx)));
            lint_store
                .register_late_pass(|_| Box::new(infallible_allocation::InfallibleAllocation));
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
