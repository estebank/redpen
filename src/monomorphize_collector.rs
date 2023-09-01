// This module is from rustc_monomorphize/collector.rs, modified so that
// * All uses are collected, including those that should not be codegen-ed locally.
// * `inlines` field is removed from `InliningMap`.
// * Due to the above reasons, `InliningMap` is renamed to `AccessMap`.
// * `Spanned<MonoItem>` is returned in `AccessMap` instead of just `MonoItem`.

use rustc_data_structures::fx::{FxHashMap, FxHashSet};
use rustc_data_structures::sync::{par_for_each_in, MTLock, MTLockRef};
use rustc_hir as hir;
use rustc_hir::def::DefKind;
use rustc_hir::def_id::{DefId, DefIdMap, LocalDefId};
use rustc_hir::lang_items::LangItem;
use rustc_middle::mir::interpret::{AllocId, ConstValue};
use rustc_middle::mir::interpret::{ErrorHandled, GlobalAlloc, Scalar};
use rustc_middle::mir::mono::MonoItem;
use rustc_middle::mir::visit::Visitor as MirVisitor;
use rustc_middle::mir::{self, Local, Location};
use rustc_middle::query::TyCtxtAt;
use rustc_middle::ty::adjustment::{CustomCoerceUnsized, PointerCoercion};
use rustc_middle::ty::print::with_no_trimmed_paths;
use rustc_middle::ty::subst::{GenericArgKind, InternalSubsts};
use rustc_middle::ty::{
    self, GenericParamDefKind, Instance, Ty, TyCtxt, TypeFoldable, TypeVisitableExt, VtblEntry,
};
use rustc_middle::{middle::codegen_fn_attrs::CodegenFnAttrFlags, mir::visit::TyContext};
use rustc_session::config::EntryFnType;
use rustc_session::Limit;
use rustc_span::source_map::{dummy_spanned, respan, Span, Spanned, DUMMY_SP};
use rustc_trait_selection::traits;
use std::ops::Range;
use std::path::PathBuf;

// From rustc_monomorphize/lib.rs
fn custom_coerce_unsize_info<'tcx>(
    tcx: TyCtxtAt<'tcx>,
    param_env: ty::ParamEnv<'tcx>,
    source_ty: Ty<'tcx>,
    target_ty: Ty<'tcx>,
) -> CustomCoerceUnsized {
    let trait_ref = ty::TraitRef::from_lang_item(
        tcx.tcx,
        LangItem::CoerceUnsized,
        tcx.span,
        [source_ty, target_ty],
    );

    match tcx.codegen_select_candidate((param_env, trait_ref)) {
        Ok(traits::ImplSource::UserDefined(traits::ImplSourceUserDefinedData {
            impl_def_id,
            ..
        })) => tcx.coerce_unsized_info(impl_def_id).custom_kind.unwrap(),
        impl_source => {
            bug!("invalid `CoerceUnsized` impl_source: {:?}", impl_source);
        }
    }
}

#[derive(PartialEq)]
pub enum MonoItemCollectionMode {
    Eager,
    Lazy,
}

pub struct UsageMap<'tcx> {
    // Maps every mono item to the mono items used by it. Those mono items
    // are represented as a range, which indexes into `used_items`.
    used_map: FxHashMap<MonoItem<'tcx>, Range<usize>>,

    // A mono item that is used by N different other mono items will appear
    // here N times. Indexed into by the ranges in `used_map`.
    used_items: Vec<Spanned<MonoItem<'tcx>>>,
}

impl<'tcx> UsageMap<'tcx> {
    fn new() -> UsageMap<'tcx> {
        UsageMap {
            used_map: FxHashMap::default(),
            used_items: Vec::new(),
        }
    }

    fn record_used(&mut self, user_item: MonoItem<'tcx>, used_items: &[Spanned<MonoItem<'tcx>>]) {
        let old_len = self.used_items.len();

        self.used_items.extend_from_slice(used_items);

        let new_len = self.used_items.len();
        let new_items_range = old_len..new_len;
        assert!(self.used_map.insert(user_item, new_items_range).is_none());
    }

    // Internally iterate over all items and the things each accesses.
    pub fn for_each_item_and_its_used_items<F>(&self, mut f: F)
    where
        F: FnMut(MonoItem<'tcx>, &[Spanned<MonoItem<'tcx>>]),
    {
        for (&item, range) in &self.used_map {
            f(item, &self.used_items[range.clone()])
        }
    }
}

pub fn collect_crate_mono_items(
    tcx: TyCtxt<'_>,
    mode: MonoItemCollectionMode,
) -> (FxHashSet<MonoItem<'_>>, UsageMap<'_>) {
    let _prof_timer = tcx.prof.generic_activity("monomorphization_collector");

    let roots = tcx
        .sess
        .time("monomorphization_collector_root_collections", || {
            collect_roots(tcx, mode)
        });

    debug!("building mono item graph, beginning at roots");

    let mut visited = MTLock::new(FxHashSet::default());
    let mut usage_map = MTLock::new(UsageMap::new());
    let recursion_limit = tcx.recursion_limit();

    {
        let visited: MTLockRef<'_, _> = &mut visited;
        let usage_map: MTLockRef<'_, _> = &mut usage_map;

        tcx.sess.time("monomorphization_collector_graph_walk", || {
            par_for_each_in(roots, |root| {
                let mut recursion_depths = DefIdMap::default();
                let should_gen = match root {
                    MonoItem::Static(def_id) => {
                        let instance = Instance::mono(tcx, def_id);
                        should_codegen_locally(tcx, &instance)
                    }
                    MonoItem::Fn(instance) => should_codegen_locally(tcx, &instance),
                    MonoItem::GlobalAsm(_) => true,
                };
                if should_gen {
                    collect_items_rec(
                        tcx,
                        dummy_spanned(root),
                        visited,
                        &mut recursion_depths,
                        recursion_limit,
                        usage_map,
                    );
                }
            });
        });
    }

    (visited.into_inner(), usage_map.into_inner())
}

// Find all non-generic items by walking the HIR. These items serve as roots to
// start monomorphizing from.
fn collect_roots(tcx: TyCtxt<'_>, mode: MonoItemCollectionMode) -> Vec<MonoItem<'_>> {
    debug!("collecting roots");
    let mut roots = Vec::new();

    {
        let entry_fn = tcx.entry_fn(());

        debug!("collect_roots: entry_fn = {:?}", entry_fn);

        let mut collector = RootCollector {
            tcx,
            mode,
            entry_fn,
            output: &mut roots,
        };

        let crate_items = tcx.hir_crate_items(());

        for id in crate_items.items() {
            collector.process_item(id);
        }

        for id in crate_items.impl_items() {
            collector.process_impl_item(id);
        }

        collector.push_extra_entry_roots();
    }

    // We can only codegen items that are instantiable - items all of
    // whose predicates hold. Luckily, items that aren't instantiable
    // can't actually be used, so we can just skip codegenning them.
    roots
        .into_iter()
        .filter_map(
            |Spanned {
                 node: mono_item, ..
             }| { mono_item.is_instantiable(tcx).then_some(mono_item) },
        )
        .collect()
}

/// Collect all monomorphized items reachable from `starting_point`, and emit a note diagnostic if a
/// post-monorphization error is encountered during a collection step.
fn collect_items_rec<'tcx>(
    tcx: TyCtxt<'tcx>,
    starting_item: Spanned<MonoItem<'tcx>>,
    visited: MTLockRef<'_, FxHashSet<MonoItem<'tcx>>>,
    recursion_depths: &mut DefIdMap<usize>,
    recursion_limit: Limit,
    usage_map: MTLockRef<'_, UsageMap<'tcx>>,
) {
    if !visited.lock_mut().insert(starting_item.node) {
        // We've been here already, no need to search again.
        return;
    }

    let mut used_items = Vec::new();
    let recursion_depth_reset;

    //
    // Post-monomorphization errors MVP
    //
    // We can encounter errors while monomorphizing an item, but we don't have a good way of
    // showing a complete stack of spans ultimately leading to collecting the erroneous one yet.
    // (It's also currently unclear exactly which diagnostics and information would be interesting
    // to report in such cases)
    //
    // This leads to suboptimal error reporting: a post-monomorphization error (PME) will be
    // shown with just a spanned piece of code causing the error, without information on where
    // it was called from. This is especially obscure if the erroneous mono item is in a
    // dependency. See for example issue #85155, where, before minimization, a PME happened two
    // crates downstream from libcore's stdarch, without a way to know which dependency was the
    // cause.
    //
    // If such an error occurs in the current crate, its span will be enough to locate the
    // source. If the cause is in another crate, the goal here is to quickly locate which mono
    // item in the current crate is ultimately responsible for causing the error.
    //
    // To give at least _some_ context to the user: while collecting mono items, we check the
    // error count. If it has changed, a PME occurred, and we trigger some diagnostics about the
    // current step of mono items collection.
    //
    // FIXME: don't rely on global state, instead bubble up errors. Note: this is very hard to do.
    let error_count = tcx.sess.diagnostic().err_count();

    match starting_item.node {
        MonoItem::Static(def_id) => {
            let instance = Instance::mono(tcx, def_id);

            // Sanity check whether this ended up being collected accidentally
            debug_assert!(should_codegen_locally(tcx, &instance));

            let ty = instance.ty(tcx, ty::ParamEnv::reveal_all());
            visit_drop_use(tcx, ty, true, starting_item.span, &mut used_items);

            recursion_depth_reset = None;

            if let Ok(alloc) = tcx.eval_static_initializer(def_id) {
                for id in alloc.inner().provenance().provenances() {
                    collect_miri(tcx, id, &mut used_items);
                }
            }
        }
        MonoItem::Fn(instance) => {
            // Sanity check whether this ended up being collected accidentally
            debug_assert!(should_codegen_locally(tcx, &instance));

            // Keep track of the monomorphization recursion depth
            recursion_depth_reset = Some(check_recursion_limit(
                tcx,
                instance,
                starting_item.span,
                recursion_depths,
                recursion_limit,
            ));
            check_type_length_limit(tcx, instance);

            rustc_data_structures::stack::ensure_sufficient_stack(|| {
                collect_used_items(tcx, instance, &mut used_items);
            });
        }
        MonoItem::GlobalAsm(item_id) => {
            recursion_depth_reset = None;

            let item = tcx.hir().item(item_id);
            if let hir::ItemKind::GlobalAsm(asm) = item.kind {
                for (op, op_sp) in asm.operands {
                    match op {
                        hir::InlineAsmOperand::Const { .. } => {
                            // Only constants which resolve to a plain integer
                            // are supported. Therefore the value should not
                            // depend on any other items.
                        }
                        hir::InlineAsmOperand::SymFn { anon_const } => {
                            let fn_ty = tcx
                                .typeck_body(anon_const.body)
                                .node_type(anon_const.hir_id);
                            visit_fn_use(tcx, fn_ty, false, *op_sp, &mut used_items);
                        }
                        hir::InlineAsmOperand::SymStatic { path: _, def_id } => {
                            trace!("collecting static {:?}", def_id);
                            used_items.push(dummy_spanned(MonoItem::Static(*def_id)));
                        }
                        hir::InlineAsmOperand::In { .. }
                        | hir::InlineAsmOperand::Out { .. }
                        | hir::InlineAsmOperand::InOut { .. }
                        | hir::InlineAsmOperand::SplitInOut { .. } => {
                            span_bug!(*op_sp, "invalid operand type for global_asm!")
                        }
                    }
                }
            } else {
                span_bug!(
                    item.span,
                    "Mismatch between hir::Item type and MonoItem type"
                )
            }
        }
    }

    // Check for PMEs and emit a diagnostic if one happened. To try to show relevant edges of the
    // mono item graph.
    if tcx.sess.diagnostic().err_count() > error_count
        && starting_item.node.is_generic_fn()
        && starting_item.node.is_user_defined()
    {
        let formatted_item = with_no_trimmed_paths!(starting_item.node.to_string());
        tcx.sess.span_note_without_error(
            starting_item.span,
            format!(
                "the above error was encountered while instantiating `{}`",
                formatted_item
            ),
        );
    }

    usage_map
        .lock_mut()
        .record_used(starting_item.node, &used_items);

    for neighbour in used_items {
        let should_gen = match neighbour.node {
            MonoItem::Static(def_id) => {
                let instance = Instance::mono(tcx, def_id);
                should_codegen_locally(tcx, &instance)
            }
            MonoItem::Fn(instance) => should_codegen_locally(tcx, &instance),
            MonoItem::GlobalAsm(_) => true,
        };
        if should_gen {
            collect_items_rec(
                tcx,
                neighbour,
                visited,
                recursion_depths,
                recursion_limit,
                usage_map,
            );
        }
    }

    if let Some((def_id, depth)) = recursion_depth_reset {
        recursion_depths.insert(def_id, depth);
    }
}

/// Format instance name that is already known to be too long for rustc.
/// Show only the first 2 types if it is longer than 32 characters to avoid blasting
/// the user's terminal with thousands of lines of type-name.
///
/// If the type name is longer than before+after, it will be written to a file.
fn shrunk_instance_name<'tcx>(
    tcx: TyCtxt<'tcx>,
    instance: &Instance<'tcx>,
) -> (String, Option<PathBuf>) {
    let s = instance.to_string();

    // Only use the shrunk version if it's really shorter.
    // This also avoids the case where before and after slices overlap.
    if s.chars().nth(33).is_some() {
        let shrunk = format!("{}", ty::ShortInstance(instance, 4));
        if shrunk == s {
            return (s, None);
        }

        let path = tcx
            .output_filenames(())
            .temp_path_ext("long-type.txt", None);
        let written_to_path = std::fs::write(&path, s).ok().map(|_| path);

        (shrunk, written_to_path)
    } else {
        (s, None)
    }
}

fn check_recursion_limit<'tcx>(
    tcx: TyCtxt<'tcx>,
    instance: Instance<'tcx>,
    span: Span,
    recursion_depths: &mut DefIdMap<usize>,
    recursion_limit: Limit,
) -> (DefId, usize) {
    let def_id = instance.def_id();
    let recursion_depth = recursion_depths.get(&def_id).cloned().unwrap_or(0);
    debug!(" => recursion depth={}", recursion_depth);

    let adjusted_recursion_depth = if Some(def_id) == tcx.lang_items().drop_in_place_fn() {
        // HACK: drop_in_place creates tight monomorphization loops. Give
        // it more margin.
        recursion_depth / 4
    } else {
        recursion_depth
    };

    // Code that needs to instantiate the same function recursively
    // more than the recursion limit is assumed to be causing an
    // infinite expansion.
    if !recursion_limit.value_within_limit(adjusted_recursion_depth) {
        let def_span = tcx.def_span(def_id);
        let def_path_str = tcx.def_path_str(def_id);
        let (shrunk, written_to_path) = shrunk_instance_name(tcx, &instance);
        let error = format!(
            "reached the recursion limit while instantiating `{}`",
            shrunk
        );
        let mut err = tcx.sess.struct_span_fatal(span, error);
        err.span_note(def_span, format!("`{}` defined here", def_path_str));
        if let Some(path) = written_to_path {
            err.note(format!(
                "the full type name has been written to '{}'",
                path.display()
            ));
        }
        err.emit();
    }

    recursion_depths.insert(def_id, recursion_depth + 1);

    (def_id, recursion_depth)
}

fn check_type_length_limit<'tcx>(tcx: TyCtxt<'tcx>, instance: Instance<'tcx>) {
    let type_length = instance
        .substs
        .iter()
        .flat_map(|arg| arg.walk())
        .filter(|arg| match arg.unpack() {
            GenericArgKind::Type(_) | GenericArgKind::Const(_) => true,
            GenericArgKind::Lifetime(_) => false,
        })
        .count();
    debug!(" => type length={}", type_length);

    // Rust code can easily create exponentially-long types using only a
    // polynomial recursion depth. Even with the default recursion
    // depth, you can easily get cases that take >2^60 steps to run,
    // which means that rustc basically hangs.
    //
    // Bail out in these cases to avoid that bad user experience.
    if !tcx.type_length_limit().value_within_limit(type_length) {
        let (shrunk, written_to_path) = shrunk_instance_name(tcx, &instance);
        let msg = format!(
            "reached the type-length limit while instantiating `{}`",
            shrunk
        );
        let mut diag = tcx
            .sess
            .struct_span_fatal(tcx.def_span(instance.def_id()), msg);
        if let Some(path) = written_to_path {
            diag.note(format!(
                "the full type name has been written to '{}'",
                path.display()
            ));
        }
        diag.help(format!(
            "consider adding a `#![type_length_limit=\"{}\"]` attribute to your crate",
            type_length
        ));
        diag.emit();
    }
}

struct MirUsedCollector<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    body: &'a mir::Body<'tcx>,
    output: &'a mut Vec<Spanned<MonoItem<'tcx>>>,
    instance: Instance<'tcx>,
}

impl<'a, 'tcx> MirUsedCollector<'a, 'tcx> {
    pub fn monomorphize<T>(&self, value: T) -> T
    where
        T: TypeFoldable<TyCtxt<'tcx>>,
    {
        debug!("monomorphize: self.instance={:?}", self.instance);
        self.instance.subst_mir_and_normalize_erasing_regions(
            self.tcx,
            ty::ParamEnv::reveal_all(),
            ty::EarlyBinder::bind(value),
        )
    }
}

impl<'a, 'tcx> MirVisitor<'tcx> for MirUsedCollector<'a, 'tcx> {
    fn visit_rvalue(&mut self, rvalue: &mir::Rvalue<'tcx>, location: Location) {
        debug!("visiting rvalue {:?}", *rvalue);

        let span = self.body.source_info(location).span;

        match *rvalue {
            // When doing an cast from a regular pointer to a fat pointer, we
            // have to instantiate all methods of the trait being cast to, so we
            // can build the appropriate vtable.
            mir::Rvalue::Cast(
                mir::CastKind::PointerCoercion(PointerCoercion::Unsize),
                ref operand,
                target_ty,
            )
            | mir::Rvalue::Cast(mir::CastKind::DynStar, ref operand, target_ty) => {
                let target_ty = self.monomorphize(target_ty);
                let source_ty = operand.ty(self.body, self.tcx);
                let source_ty = self.monomorphize(source_ty);
                let (source_ty, target_ty) = find_vtable_types_for_unsizing(
                    self.tcx.at(span),
                    ty::ParamEnv::reveal_all(),
                    source_ty,
                    target_ty,
                );
                // This could also be a different Unsize instruction, like
                // from a fixed sized array to a slice. But we are only
                // interested in things that produce a vtable.
                if (target_ty.is_trait() && !source_ty.is_trait())
                    || (target_ty.is_dyn_star() && !source_ty.is_dyn_star())
                {
                    create_mono_items_for_vtable_methods(
                        self.tcx,
                        target_ty,
                        source_ty,
                        span,
                        self.output,
                    );
                }
            }
            mir::Rvalue::Cast(
                mir::CastKind::PointerCoercion(PointerCoercion::ReifyFnPointer),
                ref operand,
                _,
            ) => {
                let fn_ty = operand.ty(self.body, self.tcx);
                let fn_ty = self.monomorphize(fn_ty);
                visit_fn_use(self.tcx, fn_ty, false, span, &mut self.output);
            }
            mir::Rvalue::Cast(
                mir::CastKind::PointerCoercion(PointerCoercion::ClosureFnPointer(_)),
                ref operand,
                _,
            ) => {
                let source_ty = operand.ty(self.body, self.tcx);
                let source_ty = self.monomorphize(source_ty);
                match *source_ty.kind() {
                    ty::Closure(def_id, substs) => {
                        let instance = Instance::resolve_closure(
                            self.tcx,
                            def_id,
                            substs,
                            ty::ClosureKind::FnOnce,
                        )
                        .expect("failed to normalize and resolve closure during codegen");
                        self.output
                            .push(create_fn_mono_item(self.tcx, instance, span));
                    }
                    _ => bug!(),
                }
            }
            mir::Rvalue::ThreadLocalRef(def_id) => {
                assert!(self.tcx.is_thread_local_static(def_id));
                trace!("collecting thread-local static {:?}", def_id);
                self.output.push(respan(span, MonoItem::Static(def_id)));
            }
            _ => { /* not interesting */ }
        }

        self.super_rvalue(rvalue, location);
    }

    /// This does not walk the constant, as it has been handled entirely here and trying
    /// to walk it would attempt to evaluate the `ty::Const` inside, which doesn't necessarily
    /// work, as some constants cannot be represented in the type system.
    fn visit_constant(&mut self, constant: &mir::Constant<'tcx>, location: Location) {
        let literal = self.monomorphize(constant.literal);
        let val = match literal {
            mir::ConstantKind::Val(val, _) => val,
            mir::ConstantKind::Ty(ct) => match ct.kind() {
                ty::ConstKind::Value(val) => self.tcx.valtree_to_const_val((ct.ty(), val)),
                ty::ConstKind::Unevaluated(ct) => {
                    debug!(?ct);
                    let param_env = ty::ParamEnv::reveal_all();
                    match self.tcx.const_eval_resolve(param_env, ct.expand(), None) {
                        // The `monomorphize` call should have evaluated that constant already.
                        Ok(val) => val,
                        Err(ErrorHandled::Reported(_)) => return,
                        Err(ErrorHandled::TooGeneric) => span_bug!(
                            self.body.source_info(location).span,
                            "collection encountered polymorphic constant: {:?}",
                            literal
                        ),
                    }
                }
                _ => return,
            },
            mir::ConstantKind::Unevaluated(uv, _) => {
                let param_env = ty::ParamEnv::reveal_all();
                match self.tcx.const_eval_resolve(param_env, uv, None) {
                    // The `monomorphize` call should have evaluated that constant already.
                    Ok(val) => val,
                    Err(ErrorHandled::Reported(_)) => return,
                    Err(ErrorHandled::TooGeneric) => span_bug!(
                        self.body.source_info(location).span,
                        "collection encountered polymorphic constant: {:?}",
                        literal
                    ),
                }
            }
        };
        collect_const_value(self.tcx, val, self.output);
        MirVisitor::visit_ty(self, literal.ty(), TyContext::Location(location));
    }

    fn visit_terminator(&mut self, terminator: &mir::Terminator<'tcx>, location: Location) {
        debug!("visiting terminator {:?} @ {:?}", terminator, location);
        let source = self.body.source_info(location).span;

        let tcx = self.tcx;
        match terminator.kind {
            mir::TerminatorKind::Call { ref func, .. } => {
                let callee_ty = func.ty(self.body, tcx);
                let callee_ty = self.monomorphize(callee_ty);
                visit_fn_use(self.tcx, callee_ty, true, source, &mut self.output)
            }
            mir::TerminatorKind::Drop { ref place, .. } => {
                let ty = place.ty(self.body, self.tcx).ty;
                let ty = self.monomorphize(ty);
                visit_drop_use(self.tcx, ty, true, source, self.output);
            }
            mir::TerminatorKind::InlineAsm { ref operands, .. } => {
                for op in operands {
                    match *op {
                        mir::InlineAsmOperand::SymFn { ref value } => {
                            let fn_ty = self.monomorphize(value.literal.ty());
                            visit_fn_use(self.tcx, fn_ty, false, source, &mut self.output);
                        }
                        mir::InlineAsmOperand::SymStatic { def_id } => {
                            trace!("collecting asm sym static {:?}", def_id);
                            self.output.push(respan(source, MonoItem::Static(def_id)));
                        }
                        _ => {}
                    }
                }
            }
            mir::TerminatorKind::Assert { ref msg, .. } => {
                let lang_item = match &**msg {
                    mir::AssertKind::BoundsCheck { .. } => LangItem::PanicBoundsCheck,
                    _ => LangItem::Panic,
                };
                let instance = Instance::mono(tcx, tcx.require_lang_item(lang_item, Some(source)));
                self.output.push(create_fn_mono_item(tcx, instance, source));
            }
            mir::TerminatorKind::Terminate { .. } => {
                let instance = Instance::mono(
                    tcx,
                    tcx.require_lang_item(LangItem::PanicCannotUnwind, Some(source)),
                );
                self.output.push(create_fn_mono_item(tcx, instance, source));
            }
            mir::TerminatorKind::Goto { .. }
            | mir::TerminatorKind::SwitchInt { .. }
            | mir::TerminatorKind::Resume
            | mir::TerminatorKind::Return
            | mir::TerminatorKind::Unreachable => {}
            mir::TerminatorKind::GeneratorDrop
            | mir::TerminatorKind::Yield { .. }
            | mir::TerminatorKind::FalseEdge { .. }
            | mir::TerminatorKind::FalseUnwind { .. } => bug!(),
        }

        self.super_terminator(terminator, location);
    }

    fn visit_operand(&mut self, operand: &mir::Operand<'tcx>, location: Location) {
        self.super_operand(operand, location);
    }

    fn visit_local(
        &mut self,
        _place_local: Local,
        _context: mir::visit::PlaceContext,
        _location: Location,
    ) {
    }
}

fn visit_drop_use<'tcx>(
    tcx: TyCtxt<'tcx>,
    ty: Ty<'tcx>,
    is_direct_call: bool,
    source: Span,
    output: &mut Vec<Spanned<MonoItem<'tcx>>>,
) {
    let instance = Instance::resolve_drop_in_place(tcx, ty);
    visit_instance_use(tcx, instance, is_direct_call, source, output);
}

fn visit_fn_use<'tcx>(
    tcx: TyCtxt<'tcx>,
    ty: Ty<'tcx>,
    is_direct_call: bool,
    source: Span,
    output: &mut Vec<Spanned<MonoItem<'tcx>>>,
) {
    if let ty::FnDef(def_id, substs) = *ty.kind() {
        let instance = if is_direct_call {
            ty::Instance::expect_resolve(tcx, ty::ParamEnv::reveal_all(), def_id, substs)
        } else {
            match ty::Instance::resolve_for_fn_ptr(tcx, ty::ParamEnv::reveal_all(), def_id, substs)
            {
                Some(instance) => instance,
                _ => bug!("failed to resolve instance for {ty}"),
            }
        };
        visit_instance_use(tcx, instance, is_direct_call, source, output);
    }
}

fn visit_instance_use<'tcx>(
    tcx: TyCtxt<'tcx>,
    instance: ty::Instance<'tcx>,
    is_direct_call: bool,
    source: Span,
    output: &mut Vec<Spanned<MonoItem<'tcx>>>,
) {
    debug!(
        "visit_item_use({:?}, is_direct_call={:?})",
        instance, is_direct_call
    );

    match instance.def {
        ty::InstanceDef::Virtual(..) | ty::InstanceDef::Intrinsic(_) => {
            if !is_direct_call {
                bug!("{:?} being reified", instance);
            }
        }
        ty::InstanceDef::ThreadLocalShim(..) => {
            bug!("{:?} being reified", instance);
        }
        ty::InstanceDef::DropGlue(_, None) => {
            // Don't need to emit noop drop glue if we are calling directly.
            if !is_direct_call {
                output.push(create_fn_mono_item(tcx, instance, source));
            }
        }
        ty::InstanceDef::DropGlue(_, Some(_))
        | ty::InstanceDef::VTableShim(..)
        | ty::InstanceDef::ReifyShim(..)
        | ty::InstanceDef::ClosureOnceShim { .. }
        | ty::InstanceDef::Item(..)
        | ty::InstanceDef::FnPtrShim(..)
        | ty::InstanceDef::CloneShim(..)
        | ty::InstanceDef::FnPtrAddrShim(..) => {
            output.push(create_fn_mono_item(tcx, instance, source));
        }
    }
}

/// Returns `true` if we should codegen an instance in the local crate, or returns `false` if we
/// can just link to the upstream crate and therefore don't need a mono item.
pub fn should_codegen_locally<'tcx>(tcx: TyCtxt<'tcx>, instance: &Instance<'tcx>) -> bool {
    let Some(def_id) = instance.def.def_id_if_not_guaranteed_local_codegen() else {
        return true;
    };

    if tcx.is_foreign_item(def_id) {
        // Foreign items are always linked against, there's no way of instantiating them.
        return false;
    }

    if def_id.is_local() {
        // Local items cannot be referred to locally without monomorphizing them locally.
        return true;
    }

    if tcx.is_reachable_non_generic(def_id)
        || instance
            .polymorphize(tcx)
            .upstream_monomorphization(tcx)
            .is_some()
    {
        // We can link to the item in question, no instance needed in this crate.
        return false;
    }

    if let DefKind::Static(_) = tcx.def_kind(def_id) {
        // We cannot monomorphize statics from upstream crates.
        return false;
    }

    if !tcx.is_mir_available(def_id) {
        bug!("no MIR available for {:?}", def_id);
    }

    true
}

/// For a given pair of source and target type that occur in an unsizing coercion,
/// this function finds the pair of types that determines the vtable linking
/// them.
///
/// For example, the source type might be `&SomeStruct` and the target type
/// might be `&dyn SomeTrait` in a cast like:
///
/// ```rust,ignore (not real code)
/// let src: &SomeStruct = ...;
/// let target = src as &dyn SomeTrait;
/// ```
///
/// Then the output of this function would be (SomeStruct, SomeTrait) since for
/// constructing the `target` fat-pointer we need the vtable for that pair.
///
/// Things can get more complicated though because there's also the case where
/// the unsized type occurs as a field:
///
/// ```rust
/// struct ComplexStruct<T: ?Sized> {
///    a: u32,
///    b: f64,
///    c: T
/// }
/// ```
///
/// In this case, if `T` is sized, `&ComplexStruct<T>` is a thin pointer. If `T`
/// is unsized, `&SomeStruct` is a fat pointer, and the vtable it points to is
/// for the pair of `T` (which is a trait) and the concrete type that `T` was
/// originally coerced from:
///
/// ```rust,ignore (not real code)
/// let src: &ComplexStruct<SomeStruct> = ...;
/// let target = src as &ComplexStruct<dyn SomeTrait>;
/// ```
///
/// Again, we want this `find_vtable_types_for_unsizing()` to provide the pair
/// `(SomeStruct, SomeTrait)`.
///
/// Finally, there is also the case of custom unsizing coercions, e.g., for
/// smart pointers such as `Rc` and `Arc`.
pub fn find_vtable_types_for_unsizing<'tcx>(
    tcx: TyCtxtAt<'tcx>,
    param_env: ty::ParamEnv<'tcx>,
    source_ty: Ty<'tcx>,
    target_ty: Ty<'tcx>,
) -> (Ty<'tcx>, Ty<'tcx>) {
    let ptr_vtable = |inner_source: Ty<'tcx>, inner_target: Ty<'tcx>| {
        let type_has_metadata = |ty: Ty<'tcx>| -> bool {
            if ty.is_sized(tcx.tcx, param_env) {
                return false;
            }
            let tail = tcx.struct_tail_erasing_lifetimes(ty, param_env);
            match tail.kind() {
                ty::Foreign(..) => false,
                ty::Str | ty::Slice(..) | ty::Dynamic(..) => true,
                _ => bug!("unexpected unsized tail: {:?}", tail),
            }
        };
        if type_has_metadata(inner_source) {
            (inner_source, inner_target)
        } else {
            tcx.struct_lockstep_tails_erasing_lifetimes(inner_source, inner_target, param_env)
        }
    };

    match (&source_ty.kind(), &target_ty.kind()) {
        (&ty::Ref(_, a, _), &ty::Ref(_, b, _) | &ty::RawPtr(ty::TypeAndMut { ty: b, .. }))
        | (&ty::RawPtr(ty::TypeAndMut { ty: a, .. }), &ty::RawPtr(ty::TypeAndMut { ty: b, .. })) => {
            ptr_vtable(*a, *b)
        }
        (&ty::Adt(def_a, _), &ty::Adt(def_b, _)) if def_a.is_box() && def_b.is_box() => {
            ptr_vtable(source_ty.boxed_ty(), target_ty.boxed_ty())
        }

        // T as dyn* Trait
        (_, &ty::Dynamic(_, _, ty::DynStar)) => ptr_vtable(source_ty, target_ty),

        (&ty::Adt(source_adt_def, source_substs), &ty::Adt(target_adt_def, target_substs)) => {
            assert_eq!(source_adt_def, target_adt_def);

            let CustomCoerceUnsized::Struct(coerce_index) =
                custom_coerce_unsize_info(tcx, param_env, source_ty, target_ty);

            let source_fields = &source_adt_def.non_enum_variant().fields;
            let target_fields = &target_adt_def.non_enum_variant().fields;

            assert!(
                coerce_index.index() < source_fields.len()
                    && source_fields.len() == target_fields.len()
            );

            find_vtable_types_for_unsizing(
                tcx,
                param_env,
                source_fields[coerce_index].ty(*tcx, source_substs),
                target_fields[coerce_index].ty(*tcx, target_substs),
            )
        }
        _ => bug!(
            "find_vtable_types_for_unsizing: invalid coercion {:?} -> {:?}",
            source_ty,
            target_ty
        ),
    }
}

fn create_fn_mono_item<'tcx>(
    tcx: TyCtxt<'tcx>,
    instance: Instance<'tcx>,
    source: Span,
) -> Spanned<MonoItem<'tcx>> {
    respan(source, MonoItem::Fn(instance.polymorphize(tcx)))
}

/// Creates a `MonoItem` for each method that is referenced by the vtable for
/// the given trait/impl pair.
fn create_mono_items_for_vtable_methods<'tcx>(
    tcx: TyCtxt<'tcx>,
    trait_ty: Ty<'tcx>,
    impl_ty: Ty<'tcx>,
    source: Span,
    output: &mut Vec<Spanned<MonoItem<'tcx>>>,
) {
    assert!(!trait_ty.has_escaping_bound_vars() && !impl_ty.has_escaping_bound_vars());

    if let ty::Dynamic(ref trait_ty, ..) = trait_ty.kind() {
        if let Some(principal) = trait_ty.principal() {
            let poly_trait_ref = principal.with_self_ty(tcx, impl_ty);
            assert!(!poly_trait_ref.has_escaping_bound_vars());

            // Walk all methods of the trait, including those of its supertraits
            let entries = tcx.vtable_entries(poly_trait_ref);
            let methods = entries
                .iter()
                .filter_map(|entry| match entry {
                    VtblEntry::MetadataDropInPlace
                    | VtblEntry::MetadataSize
                    | VtblEntry::MetadataAlign
                    | VtblEntry::Vacant => None,
                    VtblEntry::TraitVPtr(_) => {
                        // all super trait items already covered, so skip them.
                        None
                    }
                    VtblEntry::Method(instance) => Some(*instance),
                })
                .map(|item| create_fn_mono_item(tcx, item, source));
            output.extend(methods);
        }

        // Also add the destructor.
        visit_drop_use(tcx, impl_ty, false, source, output);
    }
}

//=-----------------------------------------------------------------------------
// Root Collection
//=-----------------------------------------------------------------------------

struct RootCollector<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    mode: MonoItemCollectionMode,
    output: &'a mut Vec<Spanned<MonoItem<'tcx>>>,
    entry_fn: Option<(DefId, EntryFnType)>,
}

impl<'v> RootCollector<'_, 'v> {
    fn process_item(&mut self, id: hir::ItemId) {
        match self.tcx.def_kind(id.owner_id) {
            DefKind::Enum | DefKind::Struct | DefKind::Union => {
                if self.mode == MonoItemCollectionMode::Eager
                    && self.tcx.generics_of(id.owner_id).count() == 0
                {
                    debug!("RootCollector: ADT drop-glue for {id:?}",);

                    let item = self.tcx.hir().item(id);
                    let ty = Instance::new(item.owner_id.to_def_id(), InternalSubsts::empty())
                        .ty(self.tcx, ty::ParamEnv::reveal_all());
                    visit_drop_use(self.tcx, ty, true, DUMMY_SP, self.output);
                }
            }
            DefKind::GlobalAsm => {
                debug!(
                    "RootCollector: ItemKind::GlobalAsm({})",
                    self.tcx.def_path_str(id.owner_id.to_def_id())
                );
                self.output.push(dummy_spanned(MonoItem::GlobalAsm(id)));
            }
            DefKind::Static(..) => {
                debug!(
                    "RootCollector: ItemKind::Static({})",
                    self.tcx.def_path_str(id.owner_id.to_def_id())
                );
                self.output
                    .push(dummy_spanned(MonoItem::Static(id.owner_id.to_def_id())));
            }
            DefKind::Const => {
                // const items only generate mono items if they are
                // actually used somewhere. Just declaring them is insufficient.

                // but even just declaring them must collect the items they refer to
                if let Ok(val) = self.tcx.const_eval_poly(id.owner_id.to_def_id()) {
                    collect_const_value(self.tcx, val, &mut self.output);
                }
            }
            DefKind::Impl { .. } => {
                if self.mode == MonoItemCollectionMode::Eager {
                    create_mono_items_for_default_impls(self.tcx, id, self.output);
                }
            }
            DefKind::Fn => {
                self.push_if_root(id.owner_id.def_id);
            }
            _ => {}
        }
    }

    fn process_impl_item(&mut self, id: hir::ImplItemId) {
        if matches!(self.tcx.def_kind(id.owner_id), DefKind::AssocFn) {
            self.push_if_root(id.owner_id.def_id);
        }
    }

    fn is_root(&self, def_id: LocalDefId) -> bool {
        !item_requires_monomorphization(self.tcx, def_id)
            && match self.mode {
                MonoItemCollectionMode::Eager => true,
                MonoItemCollectionMode::Lazy => {
                    self.entry_fn.and_then(|(id, _)| id.as_local()) == Some(def_id)
                        || self.tcx.is_reachable_non_generic(def_id)
                        || self
                            .tcx
                            .codegen_fn_attrs(def_id)
                            .flags
                            .contains(CodegenFnAttrFlags::RUSTC_STD_INTERNAL_SYMBOL)
                }
            }
    }

    /// If `def_id` represents a root, pushes it onto the list of
    /// outputs. (Note that all roots must be monomorphic.)
    fn push_if_root(&mut self, def_id: LocalDefId) {
        if self.is_root(def_id) {
            debug!("found root");

            let instance = Instance::mono(self.tcx, def_id.to_def_id());
            self.output
                .push(create_fn_mono_item(self.tcx, instance, DUMMY_SP));
        }
    }

    /// As a special case, when/if we encounter the
    /// `main()` function, we also have to generate a
    /// monomorphized copy of the start lang item based on
    /// the return type of `main`. This is not needed when
    /// the user writes their own `start` manually.
    fn push_extra_entry_roots(&mut self) {
        let Some((main_def_id, EntryFnType::Main { .. })) = self.entry_fn else {
            return;
        };

        let start_def_id = self.tcx.require_lang_item(LangItem::Start, None);
        let main_ret_ty = self
            .tcx
            .fn_sig(main_def_id)
            .no_bound_vars()
            .unwrap()
            .output();

        // Given that `main()` has no arguments,
        // then its return type cannot have
        // late-bound regions, since late-bound
        // regions must appear in the argument
        // listing.
        let main_ret_ty = self.tcx.normalize_erasing_regions(
            ty::ParamEnv::reveal_all(),
            main_ret_ty.no_bound_vars().unwrap(),
        );

        let start_instance = Instance::resolve(
            self.tcx,
            ty::ParamEnv::reveal_all(),
            start_def_id,
            self.tcx.mk_substs(&[main_ret_ty.into()]),
        )
        .unwrap()
        .unwrap();

        self.output
            .push(create_fn_mono_item(self.tcx, start_instance, DUMMY_SP));
    }
}

fn item_requires_monomorphization(tcx: TyCtxt<'_>, def_id: LocalDefId) -> bool {
    let generics = tcx.generics_of(def_id);
    generics.requires_monomorphization(tcx)
}

fn create_mono_items_for_default_impls<'tcx>(
    tcx: TyCtxt<'tcx>,
    item: hir::ItemId,
    output: &mut Vec<Spanned<MonoItem<'tcx>>>,
) {
    let polarity = tcx.impl_polarity(item.owner_id);
    if matches!(polarity, ty::ImplPolarity::Negative) {
        return;
    }

    if tcx
        .generics_of(item.owner_id)
        .own_requires_monomorphization()
    {
        return;
    }

    let Some(trait_ref) = tcx.impl_trait_ref(item.owner_id) else {
        return;
    };

    let trait_ref = trait_ref.subst_identity();

    let param_env = ty::ParamEnv::reveal_all();
    let trait_ref = tcx.normalize_erasing_regions(param_env, trait_ref);
    let overridden_methods = tcx.impl_item_implementor_ids(item.owner_id);

    for method in tcx.provided_trait_methods(trait_ref.def_id) {
        if overridden_methods.contains_key(&method.def_id) {
            continue;
        }

        if tcx
            .generics_of(method.def_id)
            .own_requires_monomorphization()
        {
            continue;
        }

        let substs = InternalSubsts::for_item(tcx, method.def_id, |param, _| match param.kind {
            GenericParamDefKind::Lifetime => tcx.lifetimes.re_erased.into(),
            GenericParamDefKind::Type { .. } | GenericParamDefKind::Const { .. } => {
                trait_ref.substs[param.index as usize]
            }
        });
        let instance = ty::Instance::expect_resolve(tcx, param_env, method.def_id, substs);

        let mono_item = create_fn_mono_item(tcx, instance, DUMMY_SP);
        if mono_item.node.is_instantiable(tcx) {
            output.push(mono_item);
        }
    }
}

/// Scans the miri alloc in order to find function calls, closures, and drop-glue.
fn collect_miri<'tcx>(
    tcx: TyCtxt<'tcx>,
    alloc_id: AllocId,
    output: &mut Vec<Spanned<MonoItem<'tcx>>>,
) {
    match tcx.global_alloc(alloc_id) {
        GlobalAlloc::Static(def_id) => {
            assert!(!tcx.is_thread_local_static(def_id));
            trace!("collecting static {:?}", def_id);
            output.push(dummy_spanned(MonoItem::Static(def_id)));
        }
        GlobalAlloc::Memory(alloc) => {
            trace!("collecting {:?} with {:#?}", alloc_id, alloc);
            for inner in alloc.inner().provenance().provenances() {
                rustc_data_structures::stack::ensure_sufficient_stack(|| {
                    collect_miri(tcx, inner, output);
                });
            }
        }
        GlobalAlloc::Function(fn_instance) => {
            trace!("collecting {:?} with {:#?}", alloc_id, fn_instance);
            output.push(create_fn_mono_item(tcx, fn_instance, DUMMY_SP));
        }
        GlobalAlloc::VTable(ty, trait_ref) => {
            let alloc_id = tcx.vtable_allocation((ty, trait_ref));
            collect_miri(tcx, alloc_id, output)
        }
    }
}

/// Scans the MIR in order to find function calls, closures, and drop-glue.
fn collect_used_items<'tcx>(
    tcx: TyCtxt<'tcx>,
    instance: Instance<'tcx>,
    output: &mut Vec<Spanned<MonoItem<'tcx>>>,
) {
    let body = tcx.instance_mir(instance.def);
    MirUsedCollector {
        tcx,
        body: &body,
        output,
        instance,
    }
    .visit_body(&body);
}

fn collect_const_value<'tcx>(
    tcx: TyCtxt<'tcx>,
    value: ConstValue<'tcx>,
    output: &mut Vec<Spanned<MonoItem<'tcx>>>,
) {
    match value {
        ConstValue::Scalar(Scalar::Ptr(ptr, _size)) => collect_miri(tcx, ptr.provenance, output),
        ConstValue::Slice {
            data: alloc,
            start: _,
            end: _,
        }
        | ConstValue::ByRef { alloc, .. } => {
            for id in alloc.inner().provenance().provenances() {
                collect_miri(tcx, id, output);
            }
        }
        _ => {}
    }
}
