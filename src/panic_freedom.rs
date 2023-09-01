use std::collections::{HashMap, HashSet};
use std::io::{Read, Write};

use hir::def_id::DefId;
use rustc_hir as hir;
use rustc_hir::def::DefKind;
use rustc_hir::intravisit::Visitor;
use rustc_hir_typeck::{FnCtxt, Inherited};
use rustc_lint::{LateContext, LateLintPass};
use rustc_middle::ty::{self, TyCtxt};
use rustc_session::{declare_tool_lint, impl_lint_pass};
use rustc_span::{Span, DUMMY_SP};

use crate::attribute::{parse_redpen_attribute as parse_attr, RedpenAttribute};

const FILE_NAME: &'static str = "symbols";

pub struct DontPanic<'tcx> {
    tcx: TyCtxt<'tcx>,
    current_item: Option<DefId>,
    map: HashMap<DefId, HashMap<DefId, Span>>,
    foreign: HashSet<String>,
}

impl<'tcx> DontPanic<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        let mut map = HashMap::<DefId, HashMap<DefId, Span>>::default();
        for (def_id, span) in [
            tcx.lang_items().panic_fn(),
            tcx.lang_items().panic_fmt(),
            tcx.lang_items().panic_nounwind(),
        ]
        .into_iter()
        .flatten()
        .map(|id| (id, DUMMY_SP))
        {
            map.entry(def_id).or_default().insert(def_id, span);
        }
        let mut foreign = HashSet::<String>::default();
        let mut s = String::new();
        let mut x = tcx.output_filenames(()).out_directory.clone();
        x.push(FILE_NAME);
        if let Ok(mut file) = std::fs::OpenOptions::new().read(true).open(x)
            && let Ok(_) = file.read_to_string(&mut s)
        {
            for line in s.lines() {
                foreign.insert(line.to_string());
            }
        }

        Self {
            tcx,
            map,
            current_item: None,
            foreign,
        }
    }

    fn symbol(&self, def_id: DefId) -> String {
        let args = ty::InternalSubsts::identity_for_item(self.tcx, def_id);
        let instance = ty::Instance::new(def_id, args);
        rustc_symbol_mangling::symbol_name_for_instance_in_crate(self.tcx, instance, def_id.krate)
    }

    fn visit(&mut self, def_id: DefId, callback: impl Fn(&mut Self)) {
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
            // might imply, so we won't add this item to the graph to avoid pointing at calls to it
            // anywhere else.
            return;
        }
        match self.tcx.def_kind(def_id) {
            DefKind::Const
            | DefKind::TyParam
            | DefKind::ConstParam
            | DefKind::Static(_)
            | DefKind::Ctor(..)
            | DefKind::Macro(_)
            | DefKind::AssocConst
            | DefKind::Use
            | DefKind::ForeignMod
            | DefKind::ExternCrate
            | DefKind::Field
            | DefKind::OpaqueTy
            | DefKind::AnonConst
            | DefKind::InlineConst
            | DefKind::LifetimeParam
            | DefKind::GlobalAsm
            | DefKind::Struct
            | DefKind::Union
            | DefKind::Enum
            | DefKind::Variant
            | DefKind::TyAlias
            | DefKind::TraitAlias
            | DefKind::AssocTy
            | DefKind::ImplTraitPlaceholder
            | DefKind::ForeignTy => {
                return;
            }
            DefKind::Mod | DefKind::Trait | DefKind::Impl { .. } => {
                let prev = self.current_item.clone();
                self.current_item = None;
                callback(self);
                self.current_item = prev;
                return;
            }
            DefKind::Fn | DefKind::Closure | DefKind::AssocFn | DefKind::Generator => {
                // ok
            }
        }

        if self.map.get(&def_id).is_some()
            // Avoid infinite recursion in `core`
            || Some(def_id) == self.tcx.lang_items().drop_in_place_fn()
        {
            return;
        }
        // println!("visit {def_id:?} {:?} {:?}", self.tcx.def_kind(def_id), self.current_item);
        let prev = self.current_item.clone();
        self.current_item = Some(def_id);
        // MAYBE?
        self.map.entry(def_id).or_default();
        callback(self);
        self.current_item = prev;
    }
}

impl<'tcx> Drop for DontPanic<'tcx> {
    fn drop(&mut self) {
        let mut x = self.tcx.output_filenames(()).out_directory.clone();
        x.push(FILE_NAME);
        if let Ok(mut file) = std::fs::OpenOptions::new()
            .create(true)
            .append(true)
            .open(x)
        {
            for (&def_id, _) in self.map.iter().filter(|(_, values)| !values.is_empty()) {
                let _ = file.write(self.symbol(def_id).as_bytes());
                let _ = file.write(b"\n");
            }
        }
    }
}

declare_tool_lint! {
    pub redpen::DONT_PANIC,
    Deny,
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
        let Some(current_def_id) = self.current_item else {
            return;
        };
        let Some(local_def_id) = current_def_id.as_local() else {
            return;
        };
        // println!("{:?}", expr.hir_id);
        match expr.kind {
            hir::ExprKind::Closure(closure) => {
                self.visit(closure.def_id.to_def_id(), |this| {
                    hir::intravisit::walk_expr(this, expr)
                });
                return;
            }
            hir::ExprKind::MethodCall(segment, rcvr, _args, span) => {
                let inh = Inherited::new(self.tcx, local_def_id);
                let fcx = FnCtxt::new(&inh, self.tcx.param_env(local_def_id), local_def_id);
                let rcvr_ty = if let Some(rcvr_ty) = fcx.node_ty_opt(rcvr.hir_id) {
                    rcvr_ty
                } else if let Some(rcvr_ty) = self
                    .tcx
                    .has_typeck_results(current_def_id)
                    .then(|| self.tcx.typeck(local_def_id))
                    .and_then(|typeck| typeck.node_type_opt(rcvr.hir_id))
                {
                    rcvr_ty
                } else {
                    hir::intravisit::walk_expr(self, expr);
                    return;
                };
                let Ok(method) =
                    fcx.lookup_method_for_diagnostic(rcvr_ty, segment, span, expr, rcvr)
                else {
                    // TODO: What should we do if we don't find the method?
                    hir::intravisit::walk_expr(self, expr);
                    return;
                };

                // For `impl Trait` and `Box<dyn Trait>` we instead look at *every* impl and
                // tell the user that the call might panic if *any `impl`* of `Trait` might panic,
                // because we don't know at compile time which of those is actually being called.
                let trait_object_or_impl_trait = match rcvr_ty.kind() {
                    ty::Adt(def, args) if def.is_box() => {
                        match args.get(0).and_then(|ty| ty.as_type()).map(|ty| ty.kind()) {
                            Some(ty::Dynamic(..)) => true,
                            _ => false,
                        }
                    }
                    ty::Alias(ty::Opaque, _) => true,
                    _ if rcvr_ty.to_string().starts_with("impl ") => true,
                    _ => false,
                };
                if trait_object_or_impl_trait {
                    let mut relevant_impls = vec![];
                    if let Some(impl_item) = self.tcx.opt_associated_item(method.def_id) {
                        self.tcx
                            .for_each_impl(impl_item.container_id(self.tcx), |def_id| {
                                relevant_impls.push(def_id);
                            });
                    }
                    let mut impl_methods = vec![];
                    for relevant in relevant_impls {
                        if let Some(assoc) =
                            self.tcx.associated_items(relevant).find_by_name_and_kind(
                                self.tcx,
                                segment.ident,
                                ty::AssocKind::Fn,
                                relevant,
                            )
                        {
                            impl_methods.push(assoc.def_id);
                        }
                    }
                    if impl_methods.iter().any(|&method_def_id| {
                        if let Some(local_def_id) = method_def_id.as_local()
                            && let Some(hir_id) = self.tcx.opt_local_def_id_to_hir_id(local_def_id)
                            && let Some(hir::Node::Item(item)) = self.tcx.hir().find(hir_id)
                        {
                            self.visit_item(item);
                        }
                        match self.map.get(&method_def_id) {
                            Some(ids) if !ids.is_empty() => true,
                            _ => self.foreign.contains(&self.symbol(method_def_id)),
                        }
                    }) {
                        self.map
                            .entry(current_def_id)
                            .or_default()
                            .insert(method.def_id, segment.ident.span);
                        hir::intravisit::walk_expr(self, expr);
                        return;
                    }
                }

                // `method.def_id` corresponds to the method's associated item, but we wan't the
                // trait's, so we look for relevant implementations and if we find one, we use its
                // `DefId` instead.
                let mut method_def_id = method.def_id;
                let mut relevant_impls = vec![];
                if let Some(impl_item) = self.tcx.opt_associated_item(method.def_id) {
                    self.tcx.for_each_relevant_impl(
                        impl_item.container_id(self.tcx),
                        rcvr_ty,
                        |def_id| {
                            relevant_impls.push(def_id);
                        },
                    );
                }
                if let [relevant] = &relevant_impls[..] {
                    if let Some(assoc) = self.tcx.associated_items(*relevant).find_by_name_and_kind(
                        self.tcx,
                        segment.ident,
                        ty::AssocKind::Fn,
                        *relevant,
                    ) {
                        method_def_id = assoc.def_id;
                    }
                }

                match self.map.get(&method_def_id) {
                    None => {
                        if let Some(local_def_id) = method_def_id.as_local()
                            && let Some(hir_id) = self.tcx.opt_local_def_id_to_hir_id(local_def_id)
                            && let Some(hir::Node::Item(item)) = self.tcx.hir().find(hir_id)
                        {
                            self.visit_item(item);
                        } else if self.foreign.contains(&self.symbol(method_def_id)) {
                            self.map
                                .entry(current_def_id)
                                .or_default()
                                .insert(method_def_id, segment.ident.span);
                        }
                    }
                    Some(ids) => {
                        if !ids.is_empty() {
                            // This method transitively calls panic.
                            self.map
                                .entry(current_def_id)
                                .or_default()
                                .insert(method_def_id, segment.ident.span);
                        }
                    }
                }
            }
            hir::ExprKind::Call(rcvr, _args) => {
                let Some(ty) = self.tcx.typeck(local_def_id).expr_ty_adjusted_opt(rcvr) else {
                    hir::intravisit::walk_expr(self, expr);
                    return;
                };
                let def_id = match ty.peel_refs().kind() {
                    ty::FnDef(def_id, _) => def_id,
                    ty::Closure(def_id, _) => {
                        self.visit(*def_id, |this| hir::intravisit::walk_expr(this, rcvr));
                        def_id
                    }
                    _ => {
                        hir::intravisit::walk_expr(self, expr);
                        return;
                    }
                };
                match self.map.get(def_id) {
                    None => {
                        if let Some(local_def_id) = def_id.as_local()
                            && let Some(hir_id) = self.tcx.opt_local_def_id_to_hir_id(local_def_id)
                            && let Some(hir::Node::Item(item)) = self.tcx.hir().find(hir_id)
                        {
                            self.visit_item(item);
                        } else if let Some(local_def_id) = def_id.as_local()
                            && let Some(hir_id) = self.tcx.opt_local_def_id_to_hir_id(local_def_id)
                            && let Some(hir::Node::Expr(expr)) = self.tcx.hir().find(hir_id)
                        {
                            self.visit_expr(expr);
                        } else if self.foreign.contains(&self.symbol(*def_id)) {
                            self.map.entry(current_def_id).or_default().insert(*def_id, rcvr.span);
                        }
                    }
                    Some(ids) => {
                        if !ids.is_empty() {
                            // This function calls panic
                            self.map
                                .entry(current_def_id)
                                .or_default()
                                .insert(*def_id, rcvr.span);
                        }
                    }
                }
            }
            hir::ExprKind::Index(_rcvr, _idx) => {
                let Some(tr) = self.tcx.lang_items().index_trait() else {
                    return;
                };
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
                self.map
                    .entry(current_def_id)
                    .or_default()
                    .insert(tr, expr.span);
            }
            _ => {}
        }
        hir::intravisit::walk_expr(self, expr);
    }
}

impl<'tcx> LateLintPass<'tcx> for DontPanic<'tcx> {
    fn check_crate(&mut self, cx: &LateContext<'tcx>) {
        self.tcx.hir().visit_all_item_likes_in_crate(self);

        let mut set = self.map.iter().filter(|(_, values)| !values.is_empty()).map(|(&def_id, _)| def_id).collect::<Vec<_>>();
        set.sort();
        for def_id in set {
            if let Some(calls) = self.map.get(&def_id) && !calls.is_empty()
                && let Some(did) = def_id.as_local()
            {
                let hir_id = self.tcx.local_def_id_to_hir_id(did);
                let Some((_, attr_span)) = self.tcx
                    .hir()
                    .attrs(hir_id)
                    .iter()
                    .filter_map(|attr| parse_attr(cx.tcx, hir_id, attr).map(|a| (a, attr.span)))
                    .filter(|(attr, _)| matches!(attr, RedpenAttribute::DontPanic))
                    .next()
                else {
                    continue;
                };
                let span = self.tcx.def_span(def_id);
                self.tcx.struct_span_lint_hir(
                    DONT_PANIC,
                    self.tcx.local_def_id_to_hir_id(did),
                    span,
                    format!(
                        "`{}` can panic",
                        self.tcx.def_path_str(def_id).to_string(),
                    ),
                    |diag| {
                        diag.span_label(attr_span, "the function can't panic due to this annotation");
                        diag.span_label(span, "this function can panic");
                        for span in calls.iter().map(|(_, &span)| span.source_callsite()).collect::<HashSet<Span>>() {
                            diag.span_label(span, "panic can occur here");
                        }
                        diag
                    }
                );
            }
        }
    }
}
