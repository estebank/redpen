use rustc_hir::{def_id::LocalDefId, Constness};
use rustc_lint::{LateContext, LateLintPass};
use rustc_middle::mir::mono::MonoItem;
use rustc_middle::ty::{Instance, InternalSubsts, ParamEnv, TyCtxt};
use rustc_session::{declare_tool_lint, impl_lint_pass};
use rustc_span::Span;

use crate::ctxt::AnalysisCtxt;
use crate::preempt_count::*;

// A description of how atomic context analysis works.
//
// This analysis can be treated as checking the preemption count, except that the check is
// performed in compile-time and the checking is not disabled when compiling an non-preemptible
// kernel.
//
// We assign all functions two properties, one is the current preemption count that it expects,
// and another is the adjustment to the preemption count that it will make. For example, the majority
// of functions would have an adjustment of zero, and either makes no expectation to the preemption
// count or requires it to be zero. Taking a spinlock would have an adjustment of 1, and releasing a
// spinlock would have an adjustment of -1.
//
// In the ideal world all of these properties can be inferred from the source code, however it obviously
// is not practical. The difficulty (apart from some complex control flow) arise from:
// * Rust calls into C functions
// * C calls into Rust functions
// * Indirect function calls
// * Generic functions
// * Recursion
//
// Generic functions are tricky because it makes it impossible for us to assign the properties to a
// generic function. For example, in the following code
// ```
// fn foo<T, F: FnOnce() -> T>(f: F) -> T {
//     f()
// }
// ```
// the property of `foo` depends on `F`. If `F` takes a spinlock, e.g. `let guard = foo(|| spinlock.lock())`,
// then `foo` will have an adjustment of 1. But `F` could well be a no-op function and thus `foo` should
// have an adjustment of 0. One way around this would be to work with monomorphized function only, but that
// can require a lot of redundant checking since most functions should have a fixed context property regardless
// of the type parameters. The solution to the generic function would be to try infer the properties of a function
// without generic parameters substituted, and then if the check fails or encountered a type parameter (like `F`
// in the example above), we would bail out and try to re-check the function with substituted type parameters.
//
// The first three categories are more fundamental, because the indirection or FFI makes us unable to infer
// properties in the compile-time. We would therefore have to make some assumptions: all functions are considered
// to make no adjustments to the preemption count, and all functions have no expectations on the preemption count.
// If the functions do not satisfy the expectation, then escape hatch or manual annotation would be required.
// This assumption also means that when a function pointer is *created*, it must also satisfy the assumption.
// Similarly, as using traits with dynamic dispatch is also indirection, we would require explicit markings on
// trait method signatures.
//
// Now finally, recursion. If we want to properly handle recursion, then we are effectively going to find a fixed
// point globally in a call graph. This is not very practical, so we would instead require explicit markings on
// these recursive functions, and if unmarked, assume these functions to make no adjustments to the preemption
// count and have no expectations on the preemption count.

declare_tool_lint! {
    pub klint::ATOMIC_CONTEXT,
    Deny,
    ""
}

pub const FFI_USE_DEFAULT: (i32, ExpectationRange) = (0, ExpectationRange::single_value(0));
pub const FFI_DEF_DEFAULT: (i32, ExpectationRange) = (0, ExpectationRange::top());

pub const INDIRECT_DEFAULT: (i32, ExpectationRange) = (0, ExpectationRange::single_value(0));
pub const VDROP_DEFAULT: (i32, ExpectationRange) = (0, ExpectationRange::single_value(0));
pub const VCALL_DEFAULT: (i32, ExpectationRange) = (0, ExpectationRange::single_value(0));

impl<'tcx> AnalysisCtxt<'tcx> {
    pub fn ffi_property(&self, instance: Instance<'tcx>) -> Option<(i32, ExpectationRange)> {
        const NO_ASSUMPTION: (i32, ExpectationRange) = (0, ExpectationRange::top());
        const MIGHT_SLEEP: (i32, ExpectationRange) = (0, ExpectationRange::single_value(0));
        const SPIN_LOCK: (i32, ExpectationRange) = (1, ExpectationRange::top());
        const SPIN_UNLOCK: (i32, ExpectationRange) = (-1, ExpectationRange { lo: 1, hi: None });

        const USE_SPINLOCK: (i32, ExpectationRange) = (0, ExpectationRange::top());

        let mut symbol = self.symbol_name(instance).name;

        // Skip LLVM intrinsics
        if symbol.starts_with("llvm.") {
            return Some(NO_ASSUMPTION);
        }

        // Skip helpers.
        if symbol.starts_with("rust_helper_") {
            symbol = &symbol["rust_helper_".len()..];
        }

        // If the name starts with `__` and ends with `_init` or `_exit` then it's the generated
        // init/exit function for a module. These are sleepable.
        if symbol.starts_with("__") && (symbol.ends_with("_init") || symbol.ends_with("_exit")) {
            return Some(MIGHT_SLEEP);
        }

        Some(match symbol {
            // Interfacing between libcore and panic runtime
            "rust_begin_unwind" => NO_ASSUMPTION,
            // Basic string operations depended by libcore.
            "memcmp" | "strlen" | "memchr" => NO_ASSUMPTION,

            // Compiler-builtins
            "__eqsf2" | "__gesf2" | "__lesf2" | "__nesf2" | "__unordsf2" | "__unorddf2"
            | "__ashrti3" | "__muloti4" | "__multi3" | "__ashlti3" | "__lshrti3"
            | "__udivmodti4" | "__udivti3" | "__umodti3" | "__aeabi_fcmpeq" | "__aeabi_fcmpun"
            | "__aeabi_dcmpun" | "__aeabi_uldivmod" => NO_ASSUMPTION,

            // Memory allocations glues depended by liballoc.
            // Allocation functions may sleep.
            "__rust_alloc"
            | "__rust_alloc_zeroed"
            | "__rust_realloc"
            | "__rg_alloc"
            | "__rg_alloc_zeroed"
            | "__rg_realloc" => MIGHT_SLEEP,

            // Deallocation function will not sleep.
            "__rust_dealloc" | "__rg_dealloc" => USE_SPINLOCK,

            // What krealloc does depend on flags. Assume it may sleep for conservative purpose.
            "krealloc" => MIGHT_SLEEP,
            "kfree" => USE_SPINLOCK,
            "slab_is_available" => NO_ASSUMPTION,

            // Error helpers.
            "IS_ERR" | "PTR_ERR" | "errname" => NO_ASSUMPTION,

            // Refcount helpers.
            "REFCOUNT_INIT" | "refcount_inc" | "refcount_dec_and_test" => NO_ASSUMPTION,

            // Printk can be called from any context.
            "_printk" | "_dev_printk" | "BUG" | "rust_fmt_argument" => NO_ASSUMPTION,
            "rust_build_error" => NO_ASSUMPTION,

            "ioremap" | "iounmap" => MIGHT_SLEEP,

            // I/O functions do not sleep.
            "readb" | "readw" | "readl" | "readq" | "readb_relaxed" | "readw_relaxed"
            | "readl_relaxed" | "readq_relaxed" | "writeb" | "writew" | "writel" | "writeq"
            | "writeb_relaxed" | "writew_relaxed" | "writel_relaxed" | "writeq_relaxed"
            | "memcpy_fromio" => NO_ASSUMPTION,

            // `init_module` and `cleanup_module` exposed from Rust modules are allowed to sleep.
            "init_module" | "cleanup_module" => MIGHT_SLEEP,

            "wait_for_random_bytes" => MIGHT_SLEEP,

            // Userspace memory access might fault, and thus sleep.
            "copy_from_user" | "copy_to_user" | "clear_user" | "copy_from_iter"
            | "copy_to_iter" | "iov_iter_zero" => MIGHT_SLEEP,

            // Spinlock functions.
            "__spin_lock_init" | "_raw_spin_lock_init" => NO_ASSUMPTION,
            "spin_lock" | "spin_lock_irqsave" | "raw_spin_lock" | "raw_spin_lock_irqsave" => {
                SPIN_LOCK
            }
            "spin_unlock"
            | "spin_unlock_irqrestore"
            | "raw_spin_unlock"
            | "raw_spin_unlock_irqrestore" => SPIN_UNLOCK,

            // Mutex functions.
            "__init_rwsem" | "__mutex_init" => NO_ASSUMPTION,
            "down_read" | "down_write" | "mutex_lock" | "kernel_param_lock" => MIGHT_SLEEP,
            "up_read" | "up_write" | "mutex_unlock" | "kernel_param_unlock" => MIGHT_SLEEP,

            // RCU
            "rcu_read_lock" => SPIN_LOCK,
            "rcu_read_unlock" => SPIN_UNLOCK,
            "synchronize_rcu" => MIGHT_SLEEP,

            // Scheduling related functions.
            "get_current" | "signal_pending" => NO_ASSUMPTION,
            "schedule" => MIGHT_SLEEP,

            // Wait
            "init_wait" => NO_ASSUMPTION,
            "prepare_to_wait_exclusive" | "finish_wait" => USE_SPINLOCK,
            "init_waitqueue_func_entry" => NO_ASSUMPTION,
            "add_wait_queue" | "remove_wait_queue" => USE_SPINLOCK,

            // Workqueue
            "__INIT_WORK_WITH_KEY" | "queue_work_on" => NO_ASSUMPTION,
            "destroy_workqueue" => MIGHT_SLEEP,

            "dev_name" => NO_ASSUMPTION,

            // IRQ handlers
            "handle_level_irq" | "handle_edge_irq" | "handle_bad_irq" => NO_ASSUMPTION,

            "cdev_alloc" | "cdev_add" | "cdev_del" => MIGHT_SLEEP,
            "alloc_chrdev_region" | "unregister_chrdev_region" => MIGHT_SLEEP,
            "clk_get_rate"
            | "clk_prepare_enable"
            | "clk_disable_unprepare"
            | "clk_get"
            | "clk_put" => MIGHT_SLEEP,

            // Params
            "fs_param_is_bool" | "fs_param_is_enum" | "fs_param_is_s32" | "fs_param_is_string"
            | "fs_param_is_u32" | "fs_param_is_u64" => NO_ASSUMPTION,

            "__cant_sleep" => (0, ExpectationRange { lo: 1, hi: None }),
            "__might_sleep" | "msleep" => MIGHT_SLEEP,
            _ => {
                warn!("Unable to determine property for FFI function `{}`", symbol);
                return None;
            }
        })
    }
}

pub struct AtomicContext<'tcx> {
    cx: AnalysisCtxt<'tcx>,
}

impl<'tcx> AtomicContext<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self {
            cx: AnalysisCtxt::new(tcx),
        }
    }
}

impl_lint_pass!(AtomicContext<'_> => [ATOMIC_CONTEXT]);

impl<'tcx> LateLintPass<'tcx> for AtomicContext<'tcx> {
    fn check_crate(&mut self, _: &LateContext<'tcx>) {
        use rustc_hir::intravisit as hir_visit;
        use rustc_hir::*;

        struct FnAdtVisitor<'tcx, F, A> {
            tcx: TyCtxt<'tcx>,
            fn_callback: F,
            adt_callback: A,
        }

        impl<'tcx, F, A> hir_visit::Visitor<'tcx> for FnAdtVisitor<'tcx, F, A>
        where
            F: FnMut(LocalDefId),
            A: FnMut(LocalDefId),
        {
            type NestedFilter = rustc_middle::hir::nested_filter::All;

            /// Because lints are scoped lexically, we want to walk nested
            /// items in the context of the outer item, so enable
            /// deep-walking.
            fn nested_visit_map(&mut self) -> Self::Map {
                self.tcx.hir()
            }

            fn visit_item(&mut self, i: &'tcx Item<'tcx>) {
                match i.kind {
                    ItemKind::Struct(..) | ItemKind::Union(..) | ItemKind::Enum(..) => {
                        (self.adt_callback)(i.item_id().owner_id.def_id);
                    }
                    ItemKind::Trait(..) => {
                        // Not exactly an ADT, but we want to track drop_preempt_count on traits as well.
                        (self.adt_callback)(i.item_id().owner_id.def_id);
                    }
                    _ => (),
                }
                hir_visit::walk_item(self, i);
            }

            fn visit_foreign_item(&mut self, i: &'tcx ForeignItem<'tcx>) {
                match i.kind {
                    ForeignItemKind::Fn(..) => {
                        (self.fn_callback)(i.owner_id.def_id);
                    }
                    _ => (),
                }
                hir_visit::walk_foreign_item(self, i);
            }

            fn visit_trait_item(&mut self, ti: &'tcx TraitItem<'tcx>) {
                match ti.kind {
                    TraitItemKind::Fn(_, TraitFn::Required(_)) => {
                        (self.fn_callback)(ti.owner_id.def_id);
                    }
                    _ => (),
                }
                hir_visit::walk_trait_item(self, ti)
            }

            fn visit_fn(
                &mut self,
                fk: hir_visit::FnKind<'tcx>,
                fd: &'tcx FnDecl<'tcx>,
                b: BodyId,
                _: Span,
                id: LocalDefId,
            ) {
                (self.fn_callback)(id);
                hir_visit::walk_fn(self, fk, fd, b, id)
            }
        }

        // Do this before the lint pass to ensure that errors, if any, are nicely sorted.
        self.cx
            .hir()
            .visit_all_item_likes_in_crate(&mut FnAdtVisitor {
                tcx: self.cx.tcx,
                fn_callback: |def_id: LocalDefId| {
                    let annotation = self.cx.preemption_count_annotation(def_id.into());
                    self.cx
                        .sql_store::<crate::preempt_count::annotation::preemption_count_annotation>(
                            def_id.into(), annotation,
                        );
                },
                adt_callback: |def_id: LocalDefId| {
                    let annotation = self.cx.drop_preemption_count_annotation(def_id.into());
                    self.cx
                        .sql_store::<crate::preempt_count::annotation::drop_preemption_count_annotation>(
                            def_id.into(), annotation,
                        );
                },
            });
    }

    fn check_fn(
        &mut self,
        cx: &LateContext<'tcx>,
        _: rustc_hir::intravisit::FnKind<'tcx>,
        _: &'tcx rustc_hir::FnDecl<'tcx>,
        _body: &'tcx rustc_hir::Body<'tcx>,
        _: rustc_span::Span,
        def_id: LocalDefId,
    ) {
        // Building MIR for `fn`s with unsatisfiable preds results in ICE.
        if crate::util::fn_has_unsatisfiable_preds(cx, def_id.to_def_id()) {
            return;
        }

        let identity = cx
            .tcx
            .erase_regions(InternalSubsts::identity_for_item(self.cx.tcx, def_id));
        let instance = Instance::new(def_id.into(), identity);
        let param_and_instance = self
            .cx
            .param_env_reveal_all_normalized(def_id)
            .with_constness(Constness::NotConst)
            .and(instance);
        let _ = self.cx.instance_adjustment(param_and_instance);
        let _ = self.cx.instance_expectation(param_and_instance);
        let _ = self.cx.instance_check(param_and_instance);
    }

    fn check_crate_post(&mut self, cx: &LateContext<'tcx>) {
        let mono_items = super::monomorphize_collector::collect_crate_mono_items(
            cx.tcx,
            crate::monomorphize_collector::MonoItemCollectionMode::Eager,
        )
        .0;

        for mono_item in mono_items {
            if let MonoItem::Fn(instance) = mono_item {
                let param_and_instance = ParamEnv::reveal_all().and(instance);
                if let Err(Error::TooGeneric) = self.cx.instance_adjustment(param_and_instance) {
                    bug!("monomorphized function should not be too generic");
                }
                if let Err(Error::TooGeneric) = self.cx.instance_expectation(param_and_instance) {
                    bug!("monomorphized function should not be too generic");
                }
            }
        }

        self.cx.encode_mir();
    }
}
