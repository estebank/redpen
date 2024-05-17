// FIXME: verify and unify with don't panic.

use rustc_data_structures::fx::{FxHashMap, FxHashSet};
use rustc_errors::{Diag, MultiSpan};
use rustc_hir::def::DefKind;
use rustc_lint::{LateContext, LateLintPass, LintContext};
use rustc_middle::mir::mono::MonoItem;
use rustc_middle::ty::{Instance, TyCtxt};
use rustc_session::{declare_lint_pass, declare_tool_lint};
use rustc_span::def_id::DefId;
use rustc_span::source_map::Spanned;

use crate::attribute::{attributes_for_id, RedpenAttribute};
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
        let tcx = cx.tcx;
        // Collect all mono items to be codegened with this crate. Discard the inline map, it does
        // not contain enough information for us; we will collect them ourselves later.
        //
        // Use eager mode here so dead code is also linted on.
        let mono_items = super::monomorphize_collector::collect_crate_mono_items(
            tcx,
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
                MonoItem::Static(s) => Instance::mono(tcx, s),
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
                    MonoItem::Static(s) => Instance::mono(tcx, s),
                    MonoItem::Fn(v) => v,
                    _ => return,
                };

                // For const-evaluated items, they're collected from miri, which does not have span
                // information. Synthesize one with the accessor.
                let span = if accessee.span.is_dummy() {
                    *def_span.get_or_insert_with(|| tcx.def_span(accessor.def_id()))
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
            let name = tcx.def_path_str(accessee.def_id());
            if attributes_for_id(tcx, accessee.def_id())
                .into_iter()
                .any(|(attr, _span)| {
                    matches!(
                        attr,
                        RedpenAttribute::AssumeBad(name)
                        if name.contains("blocking_async")
                    )
                })
                || [
                    "std::thread::sleep",
                    "std::io::_print",
                    "tokio::runtime::Runtime::block_on",
                ]
                .contains(&name.as_str())
            {
                work_queue.push(*accessee);
            }
        }

        info!("visited {visited:#?}");

        let mut relevant = FxHashSet::default();

        // Propagate relevant property.
        while let Some(work_item) = work_queue.pop() {
            info!("work_item {work_item:#?}");
            if visited.contains(&work_item) {
                info!("already visited: skipping");
                continue;
            }

            if !attributes_for_id(tcx, work_item.def_id())
                .into_iter()
                .any(|(attr, _span)| {
                    matches!(
                        attr,
                        RedpenAttribute::AssumeOk(name)
                        if name.contains("blocking_async")
                    )
                })
            {
                relevant.insert(work_item);
            }
            visited.insert(work_item);

            info!("accessors {:#?}", backward.get(&work_item));
            for accessor in backward.get(&work_item).unwrap_or(&Vec::new()) {
                work_queue.push(accessor.node);
            }
        }
        info!("relevant {relevant:#?}");

        eprintln!("{forward:#?}");
        for (accessor, accessees) in forward.iter() {
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

            if tcx.asyncness(accessor.def_id()).is_async() {
                // We'll visit the desugared inner-closure in a bit, skip the outer fn.
                continue;
            }
            let accessor_def_id = async_fn_def_id(tcx, accessor.def_id());
            let accessor_path = tcx.def_path_str(accessor_def_id);
            let is_generic = accessor
                .args
                .non_erasable_generics(tcx, accessor_def_id)
                .next()
                .is_some();
            let generic_note = if is_generic {
                format!(
                    " when the caller is monomorphized as `{}`",
                    tcx.def_path_str_with_args(accessor_def_id, accessor.args)
                )
            } else {
                String::new()
            };
            cx.span_lint(
                &BLOCKING_ASYNC,
                tcx.def_span(accessor_def_id),
                format!("function `{accessor_path}` can block{generic_note} {accessor_def_id:?}"),
                |diag| {
                    for item in accessees {
                        let accessee = item.node;
                        let accessee_def_id = async_fn_def_id(tcx, accessee.def_id());
                        diag.note(format!("{accessee_def_id:?}"));
                        if accessee_def_id == accessor_def_id {
                            // This is the fake "desugared async fn to closure" edge
                            continue;
                        }
                        let name = tcx.def_path_str(accessee_def_id);

                        if relevant.contains(&accessee) {
                            // For generic functions try to display a stacktrace until a non-generic one.
                            let mut caller = *accessor;
                            let mut visited = FxHashSet::default();
                            visited.insert(*accessor);
                            visited.insert(accessee);
                            let caller_def_id = async_fn_def_id(tcx, caller.def_id());
                            while caller
                                .args
                                .non_erasable_generics(tcx, caller_def_id)
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
                                        tcx.def_path_str_with_args(caller.def_id(), caller.args)
                                    ),
                                );
                            }

                            // Generate some help messages for why the function is determined to be relevant.
                            let mut msg: &str =
                                &format!("`{name}` is determined to block because it");
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

                                let callee_def_id = async_fn_def_id(tcx, callee.def_id());
                                let path = tcx.def_path_str_with_args(callee_def_id, callee.args);
                                diag.span_note(
                                    callee_callee.span,
                                    format!("{msg} calls into `{path}`"),
                                );
                                explicit_attr(tcx, callee_def_id, diag);
                                msg = "which";
                            }
                        }
                    }
                },
            );
        }
    }
}

fn explicit_attr(tcx: TyCtxt<'_>, def_id: DefId, diag: &mut Diag<'_, ()>) {
    let path = tcx.def_path_str(def_id);
    for (attr, span) in attributes_for_id(tcx, def_id) {
        if matches!(
            attr,
            RedpenAttribute::AssumeBad(name)
            if name.contains("blocking_async")
        ) {
            let mut span: MultiSpan = span.into();
            span.push_span_label(tcx.def_span(def_id), "");
            diag.span_note(span, format!("`{path}` is considered to be blocking because it was explicitly marked as such in the source code"));
        }
    }
}

fn async_fn_def_id(tcx: TyCtxt<'_>, def_id: DefId) -> DefId {
    if tcx.is_closure_like(def_id)
        && let parent = tcx.parent(def_id)
        && let DefKind::Fn = tcx.def_kind(parent)
        && tcx.asyncness(parent).is_async()
    {
        // We want to refer to the `async fn` name, not its desugared inner-closure.
        return parent;
    }
    def_id
}
