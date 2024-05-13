// FIXME: verify and unify with don't panic.

use rustc_data_structures::fx::{FxHashMap, FxHashSet};
use rustc_lint::{LateContext, LateLintPass, LintContext};
use rustc_middle::mir::mono::MonoItem;
use rustc_middle::ty::Instance;
use rustc_session::{declare_lint_pass, declare_tool_lint};
use rustc_span::source_map::Spanned;
use rustc_span::symbol::sym;

use crate::monomorphize_collector::MonoItemCollectionMode;

declare_tool_lint! {
    pub redpen::BLOCKING_ASYNC,
    Warn,
    ""
}

declare_lint_pass!(BlockingAsync => [BLOCKING_ASYNC]);

impl<'tcx> LateLintPass<'tcx> for BlockingAsync {
    fn check_crate(&mut self, cx: &LateContext<'tcx>) {
        info!("blocking async check crate");
        // Collect all mono items to be codegened with this crate. Discard the inline map, it does
        // not contain enough information for us; we will collect them ourselves later.
        //
        // Use eager mode here so dead code is also linted on.
        let mono_items = super::monomorphize_collector::collect_crate_mono_items(
            cx.tcx,
            MonoItemCollectionMode::Eager,
        );
        info!("mono items {mono_items:#?}");
        let access_map = mono_items.1;

        // Build a forward and backward dependency graph with span information.
        let mut forward = FxHashMap::default();
        let mut backward = FxHashMap::<_, Vec<_>>::default();

        access_map.for_each_item_and_its_used_items(|accessor, accessees| {
            info!("accessor {accessor:#?}");
            let accessor = match accessor {
                MonoItem::Static(s) => Instance::mono(cx.tcx, s),
                MonoItem::Fn(v) => v,
                _ => return,
            };
            info!("accessor {accessor:#?}");
            info!("accessees {accessees:#?}");

            let fwd_list = forward
                .entry(accessor)
                .or_insert_with(|| Vec::with_capacity(accessees.len()));

            let mut def_span = None;

            for accessee in accessees {
                info!("accessee node {:#?}", accessee.node);
                let accessee_node = match accessee.node {
                    MonoItem::Static(s) => Instance::mono(cx.tcx, s),
                    MonoItem::Fn(v) => v,
                    _ => return,
                };

                // For const-evaluated items, they're collected from miri, which does not have span
                // information. Synthesize one with the accessor.
                let span = if accessee.span.is_dummy() {
                    *def_span.get_or_insert_with(|| cx.tcx.def_span(accessor.def_id()))
                } else {
                    accessee.span
                };

                fwd_list.push(Spanned {
                    node: accessee_node,
                    span,
                });
                backward.entry(accessee_node).or_default().push(Spanned {
                    node: accessor,
                    span,
                });
            }
        });

        // Find all fallible functions
        let mut visited = FxHashSet::default();
        let mut work_queue = Vec::new();

        info!("backward accessees {backward:#?}");
        for accessee in backward.keys() {
            let name = cx.tcx.def_path_str(accessee.def_id());
            info!("{name}");
            // if crate::attribute::attributes_for_id(accessee.def_id()).
            if (if let Some(local_id) = accessee.def_id().as_local() {
                let hir_id = cx.tcx.local_def_id_to_hir_id(local_id);
                let mut consider_blocking = false;
                for attr in cx.tcx.hir().attrs(hir_id) {
                    // println!("{attr:#?}");
                    if let Some(crate::attribute::RedpenAttribute::AssumeBad(name)) =
                        crate::attribute::parse_redpen_attribute(cx.tcx, hir_id, attr)
                        && name.contains("blocking_async")
                    {
                        consider_blocking = true;
                    }
                }
                consider_blocking
            } else {
                println!("{name}");
                match name.as_str() {
                    "std::io::_print" => true,
                    "dependency::blocking" => true,

                    // "std::fmt::Write::write_fmt" => true,
                    _ => false,
                }
            }) {
                // visited.insert(*accessee);
                work_queue.push(*accessee);
            }
        }

        info!("visited {visited:#?}");

        let mut relevant = FxHashSet::default();
        // for accessee in backward.keys() {
        //     // Only go-through non-local-copy items.
        //     // This allows us to not to be concerned about `len()`, `is_empty()`,
        //     // because they are all inlineable.
        //     if forward.contains_key(accessee) {
        //         continue;
        //     }
        // }

        // Propagate relevant property.
        while let Some(work_item) = work_queue.pop() {
            info!("work_item {work_item:#?}");
            if visited.contains(&work_item) {
                info!("already visited: skipping");
                continue;
            }

            let mut consider_non_blocking = false;
            if let Some(local_id) = work_item.def_id().as_local() {
                let hir_id = cx.tcx.local_def_id_to_hir_id(local_id);
                for attr in cx.tcx.hir().attrs(hir_id) {
                    // println!("{attr:#?}");
                    if let Some(crate::attribute::RedpenAttribute::AssumeOk(name)) =
                        crate::attribute::parse_redpen_attribute(cx.tcx, hir_id, attr)
                        && name.contains("blocking_async")
                    {
                        consider_non_blocking = true;
                    }
                }
            };
            if !consider_non_blocking {
                relevant.insert(work_item);
            }
            visited.insert(work_item);

            info!("marked as relevant and visited");

            // Stop at local items to prevent over-linting
            // if work_item.def_id().is_local() {
            //     continue;
            // }

            info!("accessors {:#?}", backward.get(&work_item));
            for accessor in backward.get(&work_item).unwrap_or(&Vec::new()) {
                work_queue.push(accessor.node);
            }
        }
        info!("relevant {relevant:#?}");

        for (accessor, accessees) in forward.iter() {
            let name = cx.tcx.def_path_str(accessor.def_id());
            info!("{name}");
            for accessee in accessees {
                let name = cx.tcx.def_path_str(accessee.node.def_id());
                info!(" -> {name:#?}");
            }
            // Don't report on non-local items
            if !accessor.def_id().is_local() {
                info!("not local accessor");
                continue;
            }

            // Fast path
            if !relevant.contains(&accessor) {
                info!("not relevant");
                continue;
            }
            info!("---");
            if cx.tcx.asyncness(accessor.def_id()).is_async() {
                info!("is async");
                // FIXME : here else deny attr
            } else {
                info!("not async");
                // We *only* report against blocking functions in async functions.
                continue;
            }

            for item in accessees {
                let accessee = item.node;
                let name = cx.tcx.def_path_str(accessee.def_id());
                info!(" -> {name:#?}");

                if accessee.def_id().is_local() {
                    info!("local");
                } else {
                    info!("non local");
                }
                if relevant.contains(&accessee) {
                    info!("relevant");
                } else {
                    info!("non relevant");
                }
                // if !accessee.def_id().is_local() && relevant.contains(&accessee) {
                if relevant.contains(&accessee) {
                    let def_kind = cx.tcx.def_kind(accessee.def_id());
                    info!("{def_kind:#?}");
                    let is_generic = accessor
                        .args
                        .non_erasable_generics(cx.tcx, accessee.def_id())
                        .next()
                        .is_some();
                    let generic_note = if is_generic {
                        format!(
                            " when the caller is monomorphized as `{}`",
                            cx.tcx
                                .def_path_str_with_args(accessor.def_id(), accessor.args)
                        )
                    } else {
                        String::new()
                    };

                    let accessee_path = cx
                        .tcx
                        .def_path_str_with_args(accessee.def_id(), accessee.args);

                    cx.span_lint(
                        &BLOCKING_ASYNC,
                        item.span,
                        format!("`{}` can block{}", accessee_path, generic_note),
                        |diag| {
                            // For generic functions try to display a stacktrace until a non-generic one.
                            let mut caller = *accessor;
                            let mut visited = FxHashSet::default();
                            visited.insert(*accessor);
                            visited.insert(accessee);
                            while caller
                                .args
                                .non_erasable_generics(cx.tcx, caller.def_id())
                                .next()
                                .is_some()
                            {
                                let spanned_caller = match backward
                                    .get(&caller)
                                    .map(|x| &**x)
                                    .unwrap_or(&[])
                                    .iter()
                                    .find(|x| !visited.contains(&x.node))
                                {
                                    Some(v) => *v,
                                    None => break,
                                };
                                caller = spanned_caller.node;
                                visited.insert(caller);

                                diag.span_note(
                                    spanned_caller.span,
                                    format!(
                                        "which is called from `{}`",
                                        cx.tcx.def_path_str_with_args(caller.def_id(), caller.args)
                                    ),
                                );
                            }

                            // Generate some help messages for why the function is determined to be relevant.
                            let mut msg: &str =
                                &format!("`{}` is determined to block because it", accessee_path);
                            let mut callee = accessee;
                            loop {
                                let callee_callee = match forward
                                    .get(&callee)
                                    .map(|x| &**x)
                                    .unwrap_or(&[])
                                    .iter()
                                    .find(|x| {
                                        relevant.contains(&x.node) && !visited.contains(&x.node)
                                    }) {
                                    Some(v) => v,
                                    None => break,
                                };
                                callee = callee_callee.node;
                                visited.insert(callee);

                                diag.span_note(
                                    callee_callee.span,
                                    format!(
                                        "{} calls into `{}`",
                                        msg,
                                        cx.tcx.def_path_str_with_args(callee.def_id(), callee.args)
                                    ),
                                );
                                msg = "which";
                            }
                            // FIXME: point at relevant attribute if that's the reason

                            // diag.note(format!("{} may call `alloc_error_handler`", msg));
                        },
                    );
                }
            }
        }
    }
}
