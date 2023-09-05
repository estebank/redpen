use rustc_data_structures::fx::{FxHashMap, FxHashSet};

use hir::def_id::DefId;
use rustc_errors::MultiSpan;
use rustc_hir as hir;
use rustc_hir::intravisit::Visitor;
use rustc_lint::{LateContext, LateLintPass};
use rustc_middle::mir::mono::MonoItem;
use rustc_middle::ty::{self, Instance, TyCtxt};
use rustc_session::{declare_tool_lint, impl_lint_pass};
use rustc_span::source_map::Spanned;
use rustc_span::Span;

use crate::attribute::{parse_redpen_attribute as parse_attr, RedpenAttribute};
use crate::monomorphize_collector::MonoItemCollectionMode;

pub struct DontPanic<'tcx> {
    tcx: TyCtxt<'tcx>,
    affected: FxHashSet<DefId>,
    skipped: FxHashSet<DefId>,
    map: FxHashMap<Span, hir::HirId>,
    in_wont_panic: bool,
}

impl<'tcx> DontPanic<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self {
            tcx,
            affected: FxHashSet::default(),
            skipped: FxHashSet::default(),
            map: FxHashMap::default(),
            in_wont_panic: false,
        }
    }

    fn visit(&mut self, def_id: DefId, callback: impl Fn(&mut Self)) {
        let prev = self.in_wont_panic;
        self.in_wont_panic = self.check_attrs(def_id);
        if prev || self.in_wont_panic {
            self.skipped.insert(def_id);
        }
        callback(self);
        self.in_wont_panic = prev;
        return;
    }

    pub fn check_attrs(&mut self, def_id: DefId) -> bool {
        if let Some(did) = def_id.as_local()
            && let hir_id = self.tcx.local_def_id_to_hir_id(did)
            && let Some(_) = self.tcx
                .hir()
                .attrs(hir_id)
                .iter()
                .filter_map(|attr| parse_attr(self.tcx, hir_id, attr))
                .filter(|attr| matches!(attr, RedpenAttribute::WontPanic))
                .next()
        {
            // The item is annotated as ensuring that it won't panic, despite what the call graph
            // might imply, so we won't complain about it.
            true
        } else {
            false
        }
    }
}

declare_tool_lint! {
    pub redpen::DONT_PANIC,
    Allow,
    "The marked function cannot transitively call `panic!()`"
}

impl_lint_pass!(DontPanic<'_> => [DONT_PANIC]);

impl<'tcx> Visitor<'tcx> for DontPanic<'tcx> {
    type NestedFilter = rustc_middle::hir::nested_filter::All;

    fn nested_visit_map(&mut self) -> Self::Map {
        self.tcx.hir()
    }

    fn visit_trait_item(&mut self, it: &'tcx hir::TraitItem<'tcx>) {
        let def_id = it.owner_id.def_id.to_def_id();
        self.visit(def_id, |this| hir::intravisit::walk_trait_item(this, it));
    }

    fn visit_impl_item(&mut self, it: &'tcx hir::ImplItem<'tcx>) {
        let def_id = it.owner_id.def_id.to_def_id();
        self.visit(def_id, |this| hir::intravisit::walk_impl_item(this, it));
    }

    fn visit_item(&mut self, it: &'tcx hir::Item<'tcx>) {
        let def_id = it.owner_id.def_id.to_def_id();
        self.visit(def_id, |this| hir::intravisit::walk_item(this, it));
        // Check for "C-unwind" foreign functions.
    }

    fn visit_expr(&mut self, expr: &'tcx hir::Expr<'tcx>) {
        self.map.insert(expr.span, expr.hir_id);
        match expr.kind {
            hir::ExprKind::Index(_rcvr, _idx) => {
                // FIXME: we really want to do the following in order to explicitly check if the
                // impl could panic.
                // let method = fcx.try_overloaded_place_op(
                //     expr.span,
                //     rcvr_ty,
                //     &[idx_ty],
                //     rustc_hir_typeck::PlaceOp::Index,
                // );
                // In the meantime, until we can make try_overloaded_place_op public, we always
                // complain about index access :-/
                // let Some(tr) = self.tcx.lang_items().index_trait() else {
                //     return;
                // };
                // FIXME: follow `wont_panic` directive. Should `wont_panic` also mean
                // `allow(redpen::dont_panic)`? I don't think so.
                self.tcx.struct_span_lint_hir(
                    &DONT_PANIC,
                    expr.hir_id,
                    expr.span,
                    "indexing operations can panic if the indexed value isn't present",
                    |diag| diag,
                );
            }
            _ => {}
        }
        hir::intravisit::walk_expr(self, expr);
    }
}

impl<'tcx> LateLintPass<'tcx> for DontPanic<'tcx> {
    fn check_crate(&mut self, _cx: &LateContext<'tcx>) {
        // Collect all mono items to be codegened with this crate. Discard the inline map, it does
        // not contain enough information for us; we will collect them ourselves later.
        //
        // Use eager mode here so dead code is also linted on.
        let (_, access_map, trait_objects) =
            super::monomorphize_collector::collect_crate_mono_items(
                self.tcx,
                MonoItemCollectionMode::Eager,
            );

        // Build a forward and backward dependency graph with span information.
        let mut forward = FxHashMap::default();
        let mut backward = FxHashMap::<_, Vec<_>>::default();

        access_map.for_each_item_and_its_used_items(|accessor, accessees| {
            let accessor = match accessor {
                MonoItem::Static(s) => Instance::mono(self.tcx, s),
                MonoItem::Fn(v) => v,
                _ => return,
            };

            let fwd_list = forward
                .entry(accessor)
                .or_insert_with(|| Vec::with_capacity(accessees.len()));
            let mut def_span = None;

            for accessee in accessees {
                let accessee_node = match accessee.node {
                    MonoItem::Static(s) => Instance::mono(self.tcx, s),
                    MonoItem::Fn(v) => v,
                    _ => return,
                };

                // For const-evaluated items, they're collected from miri, which does not have span
                // information. Synthesize one with the accessor.
                let span = if accessee.span.is_dummy() {
                    *def_span.get_or_insert_with(|| self.tcx.def_span(accessor.def_id()))
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

        // Find all relevant functions
        let mut visited = FxHashSet::default();
        let mut affected = FxHashSet::default();
        let mut root = FxHashSet::default();
        for (accessee, accessed) in &backward {
            let name = self.tcx.def_path_str(accessee.def_id());
            match name.as_str() {
                "core::panicking::panic_fmt" | "core::panicking::panic" | "std::rt::panic_fmt" => {
                    visited.insert(*accessee);
                    affected.insert(*accessee);
                    root.insert(*accessee);
                    for accessed in accessed {
                        affected.insert(accessed.node);
                    }
                }
                _ => (),
            }
        }

        let mut work_queue = Vec::new();
        for (accessee, _accessed) in &backward {
            work_queue.push(*accessee);
        }

        // Propagate infallible property.
        while let Some(work_item) = work_queue.pop() {
            if visited.contains(&work_item) {
                continue;
            }
            visited.insert(work_item);

            for accessor in backward.get(&work_item).unwrap_or(&Vec::new()) {
                if affected.contains(&work_item) {
                    affected.insert(accessor.node);
                }
                work_queue.push(accessor.node);
            }
        }

        self.affected = affected.iter().map(|x| x.def_id()).collect();

        self.tcx.hir().visit_all_item_likes_in_crate(self);

        for (accessor, accessees) in forward.iter() {
            if !accessor.def_id().is_local() {
                continue;
            }
            for item in accessees {
                let accessee = item.node;
                if affected.contains(&accessee) {
                    if self.skipped.contains(&accessee.def_id()) {
                        continue;
                    }
                    let Some(&hir_id) = self.map.get(&item.span) else {
                        continue;
                    };
                    let is_generic = accessor.substs.non_erasable_generics().next().is_some();
                    let generic_note = if is_generic {
                        format!(
                            " when the caller is monomorphized as `{}`",
                            self.tcx
                                .def_path_str_with_substs(accessor.def_id(), accessor.substs)
                        )
                    } else {
                        String::new()
                    };

                    let accessee_path = self
                        .tcx
                        .def_path_str_with_substs(accessee.def_id(), accessee.substs);

                    self.tcx.struct_span_lint_hir(
                        &DONT_PANIC,
                        hir_id,
                        item.span,
                        format!("calling `{}` can panic{}", accessee_path, generic_note),
                        |diag| {
                            diag.span_label(item.span, "this call can panic");
                            let mut called = accessee;
                            let mut caller = accessee;
                            let mut visited = FxHashSet::default();
                            visited.insert(*accessor);
                            visited.insert(accessee);
                            loop {
                                if !caller.def_id().is_local() {
                                    break;
                                }
                                let all_called = forward
                                    .get(&called)
                                    .map(|x| &**x)
                                    .unwrap_or(&[])
                                    .iter()
                                    .filter(|x| {
                                        affected.contains(&x.node)
                                            && !self.skipped.contains(&x.node.def_id())
                                    })
                                    .collect::<Vec<_>>();
                                if all_called.len() > 1 {
                                    // point at all the callers, but don't dig into the chain
                                    let mut span: MultiSpan = all_called
                                        .iter()
                                        .map(|x| x.span.source_callsite())
                                        .collect::<Vec<_>>()
                                        .into();
                                    span.push_span_label(self.tcx.def_span(caller.def_id()), "");
                                    diag.span_note(
                                        span,
                                        format!(
                                            "`{}` can panic here",
                                            self.tcx.def_path_str_with_substs(
                                                caller.def_id(),
                                                caller.substs
                                            )
                                        ),
                                    );
                                    break;
                                } else if all_called.len() == 1 {
                                    // chain
                                } else {
                                    // nothing to point at
                                    break;
                                }

                                called = all_called[0].node;
                                visited.insert(called);

                                let mut span: MultiSpan =
                                    all_called[0].span.source_callsite().into();
                                span.push_span_label(self.tcx.def_span(caller.def_id()), "");

                                diag.span_note(
                                    span,
                                    format!(
                                        "`{}` can panic here",
                                        self.tcx.def_path_str_with_substs(
                                            caller.def_id(),
                                            caller.substs
                                        )
                                    ),
                                );
                                caller = called;
                            }
                            diag
                        },
                    );
                }
            }
        }

        for (span, to_def_id, substs) in trait_objects {
            if let Some(impl_item) = self.tcx.opt_associated_item(to_def_id) {
                let def_id = impl_item.container_id(self.tcx);
                let mut relevant_impls = vec![];
                self.tcx.for_each_impl(def_id, |x| {
                    relevant_impls.push(x);
                });
                let mut impl_methods = vec![];
                for relevant in relevant_impls {
                    if let Some(assoc) = self.tcx.associated_items(relevant).find_by_name_and_kind(
                        self.tcx,
                        impl_item.ident(self.tcx),
                        ty::AssocKind::Fn,
                        relevant,
                    ) {
                        impl_methods.push(assoc.def_id);
                    }
                }
                impl_methods.push(to_def_id); // account for fn in trait with body
                if impl_methods
                    .iter()
                    .any(|&method_def_id| self.affected.contains(&method_def_id))
                {
                    let accessee_path = self.tcx.def_path_str_with_substs(def_id, substs);
                    let Some(&hir_id) = self.map.get(&span) else {
                        continue;
                    };
                    self.tcx.struct_span_lint_hir(
                        &DONT_PANIC,
                        hir_id,
                        span,
                        format!("calling `{}` can panic in a trait object", accessee_path),
                        |diag| {
                            let mut spans = vec![];
                            let mut sec_spans = vec![];
                            for def_id in impl_methods.iter().filter(|&def_id| {
                                self.affected.contains(&def_id) && !self.skipped.contains(&def_id)
                            }) {
                                for instance in forward.keys() {
                                    if instance.def_id() == *def_id
                                        && let Some(instances) = forward.get(instance)
                                    {
                                        for accessed in instances {
                                            spans.push(accessed.span.source_callsite());
                                        }
                                        sec_spans.push(self.tcx.def_span(instance.def_id()));
                                    }
                                }
                            }
                            let s = if spans.len() > 1 { "s" } else { "" };

                            let mut span: MultiSpan = spans.into();
                            for sp in sec_spans {
                                span.push_span_label(sp, "");
                            }
                            diag.span_note(
                                span,
                                format!("the following `fn` definition{s} can panic"),
                            );
                            diag
                        },
                    );
                }
            }
        }
    }
}
