// FIXME: verify and unify with don't panic.
use rustc_data_structures::fx::{FxHashMap, FxHashSet};
use rustc_errors::{Diag, MultiSpan};
use rustc_hir::def::DefKind;
use rustc_lint::{LateContext, LateLintPass, LintContext};
use rustc_middle::mir::mono::MonoItem;
use rustc_middle::ty::{Instance, TyCtxt};
use rustc_session::{declare_lint_pass, declare_tool_lint};
use rustc_span::def_id::{DefId, LOCAL_CRATE};
use rustc_span::source_map::Spanned;

use crate::attribute::{attributes_for_id, RedpenAttribute};
use crate::monomorphize_collector::MonoItemCollectionMode;

declare_tool_lint! {
    pub redpen::BLOCKING_ASYNC,
    Warn,
    ""
}

const KNOWN_BLOCKING: &[&str] = &[
    "std::thread::sleep",
    "std::io::_print",
    "tokio::runtime::Runtime::block_on",
];

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
            let accessor = match accessor {
                MonoItem::Static(s) => Instance::mono(tcx, s),
                MonoItem::Fn(v) => v,
                _ => return,
            };

            let fwd_list = forward
                .entry(accessor)
                .or_insert_with(|| Vec::with_capacity(accessees.len()));

            let mut def_span = None;

            for accessee in accessees {
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
            if attributes_for_id(tcx, accessee.def_id())
                .into_iter()
                .any(|(attr, _span)| {
                    matches!(
                        attr,
                        RedpenAttribute::AssumeBad(name)
                        if name.contains("blocking_async")
                    )
                })
                || KNOWN_BLOCKING.contains(&def_path(tcx, accessee.def_id()).as_str())
            {
                work_queue.push(*accessee);
            }
        }

        let mut relevant = FxHashSet::default();

        // Propagate relevant property.
        while let Some(work_item) = work_queue.pop() {
            if visited.contains(&work_item) {
                info!("already visited {work_item:?}: skipping");
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

            for accessor in backward.get(&work_item).unwrap_or(&Vec::new()) {
                work_queue.push(accessor.node);
            }
        }

        // eprintln!("{forward:#?}");
        for (accessor, accessees) in forward.iter() {
            // Don't report on non-local items
            info!(?accessor);
            if !accessor.def_id().is_local() {
                info!("not local accessor");
                continue;
            }

            // Fast path
            if !relevant.contains(&accessor) {
                info!("not relevant");
                continue;
            }

            let accessor_def_id = async_fn_def_id(tcx, accessor.def_id());
            // let asyncness = tcx.asyncness(accessor.def_id());
            let asyncness = tcx.asyncness(accessor_def_id);
            if !asyncness.is_async() {
                // We'll visit the desugared inner-closure in a bit, skip the outer fn.
                continue;
            }
            if accessor_def_id == accessor.def_id() {
                // We only care about the inner closure, which is the one that has the actual call
                continue;
            }
            let accessor_path = tcx.def_path_str(accessor_def_id);
            cx.span_lint(
                &BLOCKING_ASYNC,
                tcx.def_span(accessor_def_id),
                format!("async function `{accessor_path}` can block"),
                |diag| {
                    describe(
                        tcx,
                        accessor_def_id,
                        &relevant,
                        &forward,
                        diag,
                        &accessees,
                        false,
                    );
                },
            );
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

pub fn def_path(tcx: TyCtxt<'_>, def_id: DefId) -> String {
    let crate_name = if def_id.is_local() {
        tcx.crate_name(LOCAL_CRATE)
    } else {
        let cstore = &*tcx.cstore_untracked();
        cstore.crate_name(def_id.krate)
    };

    format!(
        "{crate_name}{}",
        tcx.def_path(def_id).to_string_no_crate_verbose()
    )
}

fn describe<'tcx>(
    tcx: TyCtxt<'tcx>,
    accessor_def_id: DefId,
    relevant: &FxHashSet<Instance<'tcx>>,
    forward: &FxHashMap<Instance<'tcx>, Vec<Spanned<Instance<'tcx>>>>,
    diag: &mut Diag<'_, ()>,
    calls: &[Spanned<Instance<'tcx>>],
    into_note: bool,
) {
    let mut visited = FxHashSet::default();
    let mut spans = vec![];
    for call in calls {
        let call_def_id = async_fn_def_id(tcx, call.node.def_id());
        // if call_def_id == accessor_def_id {
        //     // Is this indeed needed? I don't think so anymore.
        //     continue;
        // }
        if !relevant.contains(&call.node) {
            // This call doesn't block, skip.
            continue;
        }
        if !tcx.asyncness(call_def_id).is_async() || call_def_id != call.node.def_id() {
            // This is a direct fn call to a non-async fn
        } else {
            continue;
        }
        visited.insert(call.node);

        if into_note {
            // This is not the beginning of the chain, we'll put this information in its own note.
            spans.push(call.span);
        } else {
            // Beginning of the chain, add the label to the main sub-diagnostic.
            diag.span_label(call.span, "this might block");
        }
        if KNOWN_BLOCKING.contains(&def_path(tcx, call.node.def_id()).as_str()) {
            let name = tcx.def_path_str(call.node.def_id());
            diag.note(format!("`{name}` is known to be blocking"));
        }
    }
    let mut visited = visited.into_iter();

    // If the called function is marked explicitly as blocking, then we point at the attribute.
    let mut explicit_annotation = false;
    for (attr, span) in attributes_for_id(tcx, accessor_def_id) {
        if matches!(
            attr,
            RedpenAttribute::AssumeBad(name)
            if name.contains("blocking_async")
        ) {
            let mut span: MultiSpan = span.into();
            span.push_span_label(tcx.def_span(accessor_def_id), "");
            let name = tcx.def_path_str(accessor_def_id);
            diag.span_note(span, format!("`{name}` is considered to block because it was explicitly marked as such in the source code"));
            explicit_annotation = true;
        }
    }

    // Otherwise, if there's a single reason the called function is blocking, we explain it, going
    // back in the chain until we either find an explicit reason, or we find a function with
    // multiple reasons.
    if !explicit_annotation
        && let Some(call) = visited.next()
        && let None = visited.next()
        && let Some(calls) = forward.get(&call)
    {
        let call_def_id = async_fn_def_id(tcx, call.def_id());
        if !spans.is_empty() {
            let mut sp: MultiSpan = tcx.def_span(accessor_def_id).into();
            let name = tcx.def_path_str(accessor_def_id);
            // let mut sp: MultiSpan = spans.clone().into();
            for span in spans {
                sp.push_span_label(span, "this might block");
            }
            diag.span_note(
                sp,
                format!("`{name}` is considered to block due to these calls"),
            );
        }
        describe(tcx, call_def_id, relevant, forward, diag, calls, true);
    }
}
