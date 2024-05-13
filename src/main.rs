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
extern crate stable_mir;

#[macro_use]
extern crate tracing;

use std::process::ExitCode;
use std::sync::atomic::AtomicPtr;

use rustc_driver::Callbacks;
use rustc_interface::interface::Config;
use rustc_session::config::ErrorOutputType;
use rustc_session::EarlyDiagCtxt;
use std::sync::atomic::Ordering;

mod attribute;
mod blocking_async;
mod infallible_allocation;
mod monomorphize_collector;
mod symbol;

rustc_session::declare_tool_lint! {
    pub redpen::INCORRECT_ATTRIBUTE,
    Forbid,
    "Incorrect usage of redpen attributes"
}

struct MyCallbacks;

impl Callbacks for MyCallbacks {
    fn config(&mut self, config: &mut Config) {
        config.override_queries = Some(|_, provider| {
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
            if rustc_session::output::collect_crate_types(sess, &[])
                .contains(&rustc_session::config::CrateType::ProcMacro)
            {
                return;
            }

            lint_store.register_lints(&[&INCORRECT_ATTRIBUTE, &blocking_async::BLOCKING_ASYNC]);

            lint_store.register_late_pass(|_tcx| Box::new(blocking_async::BlockingAsync));
        }));
    }
}

fn main() -> ExitCode {
    // let handler = EarlyDiagCtxt::new(ErrorOutputType::default());
    // rustc_driver::init_logger(&handler, "REDPEN_LOG");
    let args: Vec<_> = std::env::args().collect();

    match rustc_driver::RunCompiler::new(&args, &mut MyCallbacks).run() {
        Ok(_) => ExitCode::SUCCESS,
        Err(_) => ExitCode::FAILURE,
    }
}
