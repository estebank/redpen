use rustc_errors::{DiagnosticBuilder, EmissionGuarantee, MultiSpan};
use rustc_hir::def_id::{CrateNum, DefId};
use rustc_hir::{Constness, LangItem};
use rustc_middle::mir::{Body, TerminatorKind, UnwindAction};
use rustc_middle::ty::{self, Instance, InternalSubsts, ParamEnv, ParamEnvAnd, Ty};
use rustc_mir_dataflow::Analysis;
use rustc_mir_dataflow::JoinSemiLattice;

use super::dataflow::{AdjustmentBoundsOrError, AdjustmentComputation};
use super::*;
use crate::ctxt::AnalysisCtxt;

impl<'tcx> AnalysisCtxt<'tcx> {
    fn drop_adjustment_overflow(&self, poly_ty: ParamEnvAnd<'tcx, Ty<'tcx>>) -> Result<!, Error> {
        let diag = self.sess.struct_err(format!(
            "preemption count overflow when trying to compute adjustment of type `{}",
            PolyDisplay(&poly_ty)
        ));
        Err(Error::Error(self.emit_with_use_site_info(diag)))
    }

    fn poly_instance_of_def_id(&self, def_id: DefId) -> ParamEnvAnd<'tcx, Instance<'tcx>> {
        let poly_param_env = self.param_env_reveal_all_normalized(def_id);
        let poly_substs = self.erase_regions(InternalSubsts::identity_for_item(self.tcx, def_id));
        poly_param_env.and(Instance::new(def_id, poly_substs))
    }

    pub fn emit_with_use_site_info<G: EmissionGuarantee>(
        &self,
        mut diag: DiagnosticBuilder<'tcx, G>,
    ) -> G {
        let call_stack = self.call_stack.borrow();

        let mut limit = usize::MAX;
        if !self.recursion_limit().value_within_limit(call_stack.len()) {
            // This is recursion limit overflow, we don't want to spam the screen
            limit = 1;
        }
        let mut call_stack_pos = call_stack.len();

        while call_stack_pos > 0 {
            let site = &call_stack[call_stack_pos - 1];

            if limit == 0 {
                limit = call_stack_pos.min(2);
                if call_stack_pos > limit {
                    diag.note(format!(
                        "{} calls omitted due to recursion",
                        call_stack_pos - limit
                    ));
                }
                call_stack_pos = limit;
                continue;
            }

            match &site.kind {
                UseSiteKind::Call(span) => {
                    if diag.span.is_dummy() {
                        diag.set_span(*span);
                    } else {
                        diag.span_note(*span, "which is called from here");
                        limit -= 1;
                    }
                }
                UseSiteKind::Drop {
                    drop_span,
                    place_span,
                } => {
                    let mut multispan = MultiSpan::from_span(*drop_span);
                    multispan.push_span_label(*place_span, "value being dropped is here");
                    if diag.span.is_dummy() {
                        diag.set_span(multispan);
                    } else {
                        diag.span_note(multispan, "which is dropped here");
                        limit -= 1;
                    }
                }
                UseSiteKind::PointerCoercion(span) => {
                    if diag.span.is_dummy() {
                        diag.set_span(*span);
                    } else {
                        diag.span_note(*span, "which is used as a pointer here");
                        limit -= 1;
                    }
                }
                UseSiteKind::Vtable(span) => {
                    if diag.span.is_dummy() {
                        diag.set_span(*span);
                    } else {
                        diag.span_note(*span, "which is used as a vtable here");
                        limit -= 1;
                    }
                }
            }
            let def_id = site.instance.value.def_id();
            if self.poly_instance_of_def_id(def_id) != site.instance {
                diag.note(format!(
                    "instance being checked is `{}`",
                    PolyDisplay(&site.instance)
                ));
            }

            call_stack_pos -= 1;
        }

        diag.emit()
    }

    fn report_adjustment_infer_error<'mir>(
        &self,
        instance: Instance<'tcx>,
        body: &'mir Body<'tcx>,
        results: &mut rustc_mir_dataflow::ResultsCursor<
            'mir,
            'tcx,
            AdjustmentComputation<'mir, 'tcx, '_>,
        >,
    ) -> ErrorGuaranteed {
        // First step, see if there are any path that leads to a `return` statement have `Top` directly.
        let mut return_bb = None;
        for (b, data) in rustc_middle::mir::traversal::reachable(body) {
            match data.terminator().kind {
                TerminatorKind::Return => (),
                _ => continue,
            }

            results.seek_to_block_start(b);
            // We can unwrap here because if this function is called, we know that no paths to `Return`
            // can contain `TooGeneric` or `Error` otherwise we would have returned early (in caller).
            if results.get().unwrap().is_single_value().is_some() {
                continue;
            }

            return_bb = Some(b);
            break;
        }

        // A catch-all error. MIR building usually should just have one `Return` terminator
        // so this usually shouldn't happen.
        let Some(return_bb) = return_bb else {
            return self.emit_with_use_site_info(self.tcx.sess.struct_span_err(
                self.tcx.def_span(instance.def_id()),
                "cannot infer preemption count adjustment of this function",
            ));
        };

        // Find the deepest single-value block in the dominator tree.
        let mut first_problematic_block = return_bb;
        let dominators = body.basic_blocks.dominators();
        loop {
            let b = dominators
                .immediate_dominator(first_problematic_block)
                .expect("block not reachable!");
            if b == first_problematic_block {
                // Shouldn't actually happen because the entry block should always have a single value.
                break;
            }

            results.seek_to_block_start(b);
            if results.get().unwrap().is_single_value().is_some() {
                break;
            }
            first_problematic_block = b;
        }

        // For this problematic block, try use a span that closest to the beginning of it.
        let span = body.basic_blocks[first_problematic_block]
            .statements
            .first()
            .map(|x| x.source_info.span)
            .unwrap_or_else(|| {
                body.basic_blocks[first_problematic_block]
                    .terminator()
                    .source_info
                    .span
            });

        let mut diag = self.tcx.sess.struct_span_err(
            span,
            "cannot infer preemption count adjustment at this point",
        );

        let mut count = 0;
        for mut prev_block in body.basic_blocks.predecessors()[first_problematic_block]
            .iter()
            .copied()
        {
            results.seek_to_block_end(prev_block);
            let mut end_adjustment = results.get().unwrap();
            results.seek_to_block_start(prev_block);
            let mut start_adjustment = results.get().unwrap();

            // If this block has made no changes to the adjustment, backtrack to the predecessors block
            // that made the change.
            while start_adjustment == end_adjustment {
                let pred = &body.basic_blocks.predecessors()[prev_block];

                // Don't continue backtracking if there are multiple predecessors.
                if pred.len() != 1 {
                    break;
                }
                let b = pred[0];

                // Don't continue backtracking if the predecessor block has multiple successors.
                let terminator = body.basic_blocks[b].terminator();
                let successor_count = terminator.successors().count();
                let has_unwind = terminator
                    .unwind()
                    .map(|x| matches!(x, UnwindAction::Cleanup(_)))
                    .unwrap_or(false);
                let normal_successor = successor_count - has_unwind as usize;
                if normal_successor != 1 {
                    break;
                }

                prev_block = b;
                results.seek_to_block_end(prev_block);
                end_adjustment = results.get().unwrap();
                results.seek_to_block_start(prev_block);
                start_adjustment = results.get().unwrap();
            }

            let terminator = body.basic_blocks[prev_block].terminator();
            let span = match terminator.kind {
                TerminatorKind::Goto { .. } => {
                    // Goto terminator of `if .. { .. } else { .. }` has span on the entire expression,
                    // which is not very useful.
                    // In this case we use the last statement's span instead.
                    body.basic_blocks[prev_block]
                        .statements
                        .last()
                        .map(|x| x.source_info)
                        .unwrap_or_else(|| terminator.source_info)
                        .span
                }
                _ => terminator.source_info.span,
            };

            let mut msg = match start_adjustment.is_single_value() {
                None => {
                    format!("preemption count adjustment is changed in the previous iteration of the loop")
                }
                Some(_) => {
                    format!(
                        "preemption count adjustment is {:?} after this",
                        end_adjustment
                    )
                }
            };

            match count {
                0 => (),
                1 => msg = format!("while {}", msg),
                _ => msg = format!("and {}", msg),
            }
            count += 1;
            diag.span_note(span, msg);
        }
        self.emit_with_use_site_info(diag)
    }

    pub fn do_infer_adjustment(
        &self,
        param_env: ParamEnv<'tcx>,
        instance: Instance<'tcx>,
        body: &Body<'tcx>,
    ) -> Result<i32, Error> {
        if self.should_dump_mir(instance.def_id()) {
            rustc_middle::mir::pretty::write_mir_fn(
                self.tcx,
                body,
                &mut |_, _| Ok(()),
                &mut std::io::stderr(),
            )
            .unwrap();
        }

        let mut analysis_result = AdjustmentComputation {
            checker: self,
            body,
            param_env,
            instance,
        }
        .into_engine(self.tcx, body)
        .iterate_to_fixpoint()
        .into_results_cursor(body);

        let mut adjustment = AdjustmentBoundsOrError::default();
        for (b, data) in rustc_middle::mir::traversal::reachable(body) {
            match data.terminator().kind {
                TerminatorKind::Return => {
                    adjustment.join(&analysis_result.results().entry_set_for_block(b));
                }
                _ => (),
            }
        }
        let adjustment = adjustment.into_result()?;

        let adjustment = if adjustment.is_empty() {
            // Diverging function, any value is fine, use the default 0.
            0
        } else if let Some(v) = adjustment.is_single_value() {
            v
        } else {
            return Err(Error::Error(self.report_adjustment_infer_error(
                instance,
                body,
                &mut analysis_result,
            )));
        };

        Ok(adjustment)
    }

    pub fn infer_adjustment(
        &self,
        param_env: ParamEnv<'tcx>,
        instance: Instance<'tcx>,
        body: &Body<'tcx>,
    ) -> Result<i32, Error> {
        if !self
            .recursion_limit()
            .value_within_limit(self.call_stack.borrow().len())
        {
            self.emit_with_use_site_info(self.sess.struct_fatal(format!(
                "reached the recursion limit while checking adjustment for `{}`",
                PolyDisplay(&param_env.and(instance))
            )));
        }

        rustc_data_structures::stack::ensure_sufficient_stack(|| {
            self.do_infer_adjustment(param_env, instance, body)
        })
    }
}

memoize!(
    #[instrument(skip(cx), fields(poly_ty = %PolyDisplay(&poly_ty)), ret)]
    pub fn drop_adjustment<'tcx>(
        cx: &AnalysisCtxt<'tcx>,
        poly_ty: ParamEnvAnd<'tcx, Ty<'tcx>>,
    ) -> Result<i32, Error> {
        let (param_env, ty) = poly_ty.into_parts();

        // If the type doesn't need drop, then there is trivially no adjustment.
        if !ty.needs_drop(cx.tcx, param_env) {
            return Ok(0);
        }

        match ty.kind() {
            ty::Closure(_, substs) => {
                return cx.drop_adjustment(param_env.and(substs.as_closure().tupled_upvars_ty()));
            }

            // Generator drops are non-trivial, use the generated drop shims instead.
            ty::Generator(..) => (),

            ty::Tuple(list) => {
                let mut adj = 0i32;
                for elem_ty in list.iter() {
                    let elem_adj = cx.drop_adjustment(param_env.and(elem_ty))?;
                    let Some(new_adj) = adj.checked_add(elem_adj) else {
                        cx.drop_adjustment_overflow(poly_ty)?
                    };
                    adj = new_adj;
                }
                return Ok(adj);
            }

            ty::Adt(def, substs) if def.is_box() => {
                let adj = cx.drop_adjustment(param_env.and(substs.type_at(0)))?;
                let drop_trait = cx.require_lang_item(LangItem::Drop, None);
                let drop_fn = cx.associated_item_def_ids(drop_trait)[0];
                let box_free =
                    ty::Instance::resolve(cx.tcx, param_env, drop_fn, cx.mk_substs(&[ty.into()]))
                        .unwrap()
                        .unwrap();
                let box_free_adj = cx.instance_adjustment(param_env.and(box_free))?;
                let Some(adj) = adj.checked_add(box_free_adj) else {
                    cx.drop_adjustment_overflow(poly_ty)?
                };
                return Ok(adj);
            }

            ty::Adt(def, _) => {
                // For Adts, we first try to not use any of the substs and just try the most
                // polymorphic version of the type.
                let poly_param_env = cx.param_env_reveal_all_normalized(def.did());
                let poly_substs =
                    cx.erase_regions(InternalSubsts::identity_for_item(cx.tcx, def.did()));
                let poly_poly_ty =
                    poly_param_env.and(cx.tcx.mk_ty_from_kind(ty::Adt(*def, poly_substs)));
                if poly_poly_ty != poly_ty {
                    match cx.drop_adjustment(poly_poly_ty) {
                        Err(Error::TooGeneric) => (),
                        adjustment => return adjustment,
                    }
                }

                // If that fails, we try to use the substs.
                // Fallthrough to the MIR drop shim based logic.

                if let Some(adj) = cx.drop_preemption_count_annotation(def.did()).adjustment {
                    info!("adjustment {} from annotation", adj);
                    return Ok(adj);
                }
            }

            ty::Dynamic(pred, _, _) => {
                if let Some(principal_trait) = pred.principal_def_id() {
                    if let Some(adj) = cx
                        .drop_preemption_count_annotation(principal_trait)
                        .adjustment
                    {
                        return Ok(adj);
                    }
                }
                return Ok(crate::atomic_context::VDROP_DEFAULT.0);
            }

            ty::Array(elem_ty, size) => {
                let size = size
                    .try_eval_target_usize(cx.tcx, param_env)
                    .ok_or(Error::TooGeneric);
                if size == Ok(0) {
                    return Ok(0);
                }
                let elem_adj = cx.drop_adjustment(param_env.and(*elem_ty))?;
                if elem_adj == 0 {
                    return Ok(0);
                }
                let Ok(size) = i32::try_from(size?) else {
                    cx.drop_adjustment_overflow(poly_ty)?
                };
                let Some(adj) = size.checked_mul(elem_adj) else {
                    cx.drop_adjustment_overflow(poly_ty)?
                };
                return Ok(adj);
            }

            ty::Slice(elem_ty) => {
                let elem_adj = cx.drop_adjustment(param_env.and(*elem_ty))?;
                if elem_adj != 0 {
                    let mut diag = cx.sess.struct_err(
                        "dropping element of slice causes non-zero preemption count adjustment",
                    );
                    diag.note(format!(
                        "adjustment for dropping `{}` is {}",
                        elem_ty, elem_adj
                    ));
                    diag.note(
                        "because slice can contain variable number of elements, adjustment \
                               for dropping the slice cannot be computed statically",
                    );
                    return Err(Error::Error(cx.emit_with_use_site_info(diag)));
                }
                return Ok(0);
            }

            _ => return Err(Error::TooGeneric),
        }

        // Do not call `resolve_drop_in_place` because we need param_env.
        let drop_in_place = cx.require_lang_item(LangItem::DropInPlace, None);
        let substs = cx.mk_substs(&[ty.into()]);
        let instance = ty::Instance::resolve(cx.tcx, param_env, drop_in_place, substs)
            .unwrap()
            .unwrap();
        let poly_instance = param_env.and(instance);

        assert!(matches!(
            instance.def,
            ty::InstanceDef::DropGlue(_, Some(_))
        ));

        if cx
            .call_stack
            .borrow()
            .iter()
            .rev()
            .any(|x| x.instance == poly_instance)
        {
            // Recursion encountered.
            if param_env.caller_bounds().is_empty() {
                return Ok(0);
            } else {
                // If we are handling generic functions, then defer decision to monomorphization time.
                return Err(Error::TooGeneric);
            }
        }

        let mir = crate::mir::drop_shim::build_drop_shim(cx, instance.def_id(), param_env, ty);
        let result = cx.infer_adjustment(param_env, instance, &mir);

        // Recursion encountered.
        if let Some(&recur) = cx.query_cache::<drop_adjustment>().borrow().get(&poly_ty) {
            match (result, recur) {
                (_, Err(Error::Error(_))) => bug!("recursive callee errors"),
                // Error already reported.
                (Err(Error::Error(_)), _) => (),
                (Err(_), Err(_)) => (),
                (Ok(a), Ok(b)) if a == b => (),
                (Ok(_), Err(_)) => bug!("recursive callee too generic but caller is not"),
                (Err(_), Ok(_)) => bug!("monormorphic caller too generic"),
                (Ok(adj), Ok(_)) => {
                    let mut diag = cx.sess.struct_span_err(
                        ty.ty_adt_def()
                            .map(|x| cx.def_span(x.did()))
                            .unwrap_or_else(|| cx.def_span(instance.def_id())),
                        "dropping this type causes recursion but preemption count adjustment is not 0",
                    );
                    diag.note(format!("adjustment is inferred to be {}", adj));
                    diag.note(format!("type being dropped is `{}`", ty));
                    diag.emit();
                }
            }
        }

        result
    }
);

memoize!(
    #[instrument(skip(cx), fields(poly_ty = %PolyDisplay(&poly_ty)), ret)]
    pub fn drop_adjustment_check<'tcx>(
        cx: &AnalysisCtxt<'tcx>,
        poly_ty: ParamEnvAnd<'tcx, Ty<'tcx>>,
    ) -> Result<(), Error> {
        let adjustment = cx.drop_adjustment(poly_ty)?;
        let (param_env, ty) = poly_ty.into_parts();

        // If the type doesn't need drop, then there is trivially no adjustment.
        if !ty.needs_drop(cx.tcx, param_env) {
            return Ok(());
        }

        let annotation;
        match ty.kind() {
            ty::Closure(..)
            | ty::Generator(..)
            | ty::Tuple(..)
            | ty::Dynamic(..)
            | ty::Array(..)
            | ty::Slice(..) => return Ok(()),

            // Box is always inferred
            ty::Adt(def, _) if def.is_box() => return Ok(()),

            ty::Adt(def, _) => {
                // For Adts, we first try to not use any of the substs and just try the most
                // polymorphic version of the type.
                let poly_param_env = cx.param_env_reveal_all_normalized(def.did());
                let poly_substs =
                    cx.erase_regions(InternalSubsts::identity_for_item(cx.tcx, def.did()));
                let poly_poly_ty =
                    poly_param_env.and(cx.tcx.mk_ty_from_kind(ty::Adt(*def, poly_substs)));
                if poly_poly_ty != poly_ty {
                    match cx.drop_adjustment_check(poly_poly_ty) {
                        Err(Error::TooGeneric) => (),
                        result => return result,
                    }
                }

                // If that fails, we try to use the substs.
                // Fallthrough to the MIR drop shim based logic.

                annotation = cx.drop_preemption_count_annotation(def.did());
                if let Some(adj) = annotation.adjustment {
                    assert!(adj == adjustment);
                }
            }

            _ => return Err(Error::TooGeneric),
        }

        // If adjustment is inferred or the type is annotated as unchecked,
        // then we don't need to do any further checks.
        if annotation.adjustment.is_none() || annotation.unchecked {
            return Ok(());
        }

        // Do not call `resolve_drop_in_place` because we need param_env.
        let drop_in_place = cx.require_lang_item(LangItem::DropInPlace, None);
        let substs = cx.mk_substs(&[ty.into()]);
        let instance = ty::Instance::resolve(cx.tcx, param_env, drop_in_place, substs)
            .unwrap()
            .unwrap();

        assert!(matches!(
            instance.def,
            ty::InstanceDef::DropGlue(_, Some(_))
        ));

        let mir = crate::mir::drop_shim::build_drop_shim(cx, instance.def_id(), param_env, ty);
        let adjustment_infer = cx.infer_adjustment(param_env, instance, &mir)?;
        // Check if the inferred adjustment matches the annotation.
        if let Some(adjustment) = annotation.adjustment {
            if adjustment != adjustment_infer {
                let mut diag = cx.sess.struct_span_err(
                    cx.def_span(instance.def_id()),
                    format!(
                        "type annotated to have drop preemption count adjustment of {adjustment}"
                    ),
                );
                diag.note(format!("but the adjustment inferred is {adjustment_infer}"));
                cx.emit_with_use_site_info(diag);
            }
        }

        Ok(())
    }
);

memoize!(
    #[instrument(skip(cx), fields(poly_instance = %PolyDisplay(&poly_instance)), ret)]
    pub fn instance_adjustment<'tcx>(
        cx: &AnalysisCtxt<'tcx>,
        poly_instance: ParamEnvAnd<'tcx, Instance<'tcx>>,
    ) -> Result<i32, Error> {
        let (param_env, instance) = poly_instance.into_parts();
        match instance.def {
            // No Rust built-in intrinsics will mess with preemption count.
            ty::InstanceDef::Intrinsic(_) => return Ok(0),
            // Empty drop glue, then it definitely won't mess with preemption count.
            ty::InstanceDef::DropGlue(_, None) => return Ok(0),
            ty::InstanceDef::DropGlue(_, Some(ty)) => return cx.drop_adjustment(param_env.and(ty)),
            ty::InstanceDef::Virtual(def_id, _) => {
                if let Some(adj) = cx.preemption_count_annotation(def_id).adjustment {
                    return Ok(adj);
                }

                return Ok(crate::atomic_context::VCALL_DEFAULT.0);
            }
            _ => (),
        }

        let mut generic = false;
        if matches!(instance.def, ty::InstanceDef::Item(_)) {
            let poly_param_env = cx
                .param_env_reveal_all_normalized(instance.def_id())
                .with_constness(Constness::NotConst);
            let poly_substs =
                cx.erase_regions(InternalSubsts::identity_for_item(cx.tcx, instance.def_id()));
            let poly_poly_instance =
                poly_param_env.and(Instance::new(instance.def_id(), poly_substs));
            generic = poly_poly_instance == poly_instance;
            if !generic {
                match cx.instance_adjustment(poly_poly_instance) {
                    Err(Error::TooGeneric) => (),
                    adjustment => return adjustment,
                }
            }
        }

        if cx.is_foreign_item(instance.def_id()) {
            return Ok(cx
                .ffi_property(instance)
                .unwrap_or(crate::atomic_context::FFI_USE_DEFAULT)
                .0);
        }

        if !crate::monomorphize_collector::should_codegen_locally(cx.tcx, &instance) {
            if let Some(p) = cx.sql_load::<instance_adjustment>(poly_instance) {
                return p;
            }

            // If we cannot load it, use annotation (e.g. libcore).
            return Ok(cx
                .preemption_count_annotation(instance.def_id())
                .adjustment
                .unwrap_or(0));
        }

        // Use annotation if available.
        if let Some(adj) = cx.preemption_count_annotation(instance.def_id()).adjustment {
            info!("adjustment {} from annotation", adj);
            return Ok(adj);
        }

        if cx
            .call_stack
            .borrow()
            .iter()
            .rev()
            .any(|x| x.instance == poly_instance)
        {
            // Recursion encountered.
            if param_env.caller_bounds().is_empty() {
                return Ok(0);
            } else {
                // If we are handling generic functions, then defer decision to monomorphization time.
                return Err(Error::TooGeneric);
            }
        }

        let mir = cx.analysis_instance_mir(instance.def);
        let result = cx.infer_adjustment(param_env, instance, mir);

        // Recursion encountered.
        if let Some(&recur) = cx
            .query_cache::<instance_adjustment>()
            .borrow()
            .get(&poly_instance)
        {
            match (result, recur) {
                (_, Err(Error::Error(_))) => bug!("recursive callee errors"),
                // Error already reported.
                (Err(Error::Error(_)), _) => (),
                (Err(_), Err(_)) => (),
                (Ok(a), Ok(b)) if a == b => (),
                (Ok(_), Err(_)) => bug!("recursive callee too generic but caller is not"),
                (Err(_), Ok(_)) => bug!("monormorphic caller too generic"),
                (Ok(adj), Ok(_)) => {
                    let mut diag = cx.sess.struct_span_err(
                        cx.def_span(instance.def_id()),
                        "this function is recursive but preemption count adjustment is not 0",
                    );
                    diag.note(format!("adjustment is inferred to be {}", adj));
                    if !generic {
                        diag.note(format!(
                            "instance being checked is `{}`",
                            PolyDisplay(&poly_instance)
                        ));
                    }
                    diag.help(format!(
                        "try annotate the function with `#[redpen::preempt_count(adjust = {adj})]`"
                    ));
                    diag.emit();
                }
            }
        }

        if instance.def_id().is_local() && (generic || param_env.caller_bounds().is_empty()) {
            cx.sql_store::<instance_adjustment>(poly_instance, result);
        }

        if cx.should_report_preempt_count(instance.def_id()) {
            let mut diag = cx.sess.diagnostic().struct_note_without_error(format!(
                "reporting preemption count for instance `{}`",
                PolyDisplay(&poly_instance)
            ));
            diag.set_span(cx.def_span(instance.def_id()));
            if let Ok(property) = result {
                diag.note(format!("adjustment is inferred to be {}", property));
            } else {
                diag.note("adjustment inference failed because this function is too generic");
            }
            diag.emit();
        }

        result
    }
);

memoize!(
    #[instrument(skip(cx), fields(poly_instance = %PolyDisplay(&poly_instance)), ret)]
    pub fn instance_adjustment_check<'tcx>(
        cx: &AnalysisCtxt<'tcx>,
        poly_instance: ParamEnvAnd<'tcx, Instance<'tcx>>,
    ) -> Result<(), Error> {
        let adjustment = cx.instance_adjustment(poly_instance)?;
        let (param_env, instance) = poly_instance.into_parts();

        // Only check locally codegenned instances.
        if !crate::monomorphize_collector::should_codegen_locally(cx.tcx, &instance) {
            return Ok(());
        }

        match instance.def {
            // No Rust built-in intrinsics will mess with preemption count.
            ty::InstanceDef::Intrinsic(_) => return Ok(()),
            // Empty drop glue, then it definitely won't mess with preemption count.
            ty::InstanceDef::DropGlue(_, None) => return Ok(()),
            ty::InstanceDef::DropGlue(_, Some(ty)) => {
                return cx.drop_adjustment_check(param_env.and(ty));
            }
            // Checked by indirect checks
            ty::InstanceDef::Virtual(_, _) => return Ok(()),
            _ => (),
        }

        // Prefer to do polymorphic check if possible.
        if matches!(instance.def, ty::InstanceDef::Item(_)) {
            let poly_param_env = cx
                .param_env_reveal_all_normalized(instance.def_id())
                .with_constness(Constness::NotConst);
            let poly_substs =
                cx.erase_regions(InternalSubsts::identity_for_item(cx.tcx, instance.def_id()));
            let poly_poly_instance =
                poly_param_env.and(Instance::new(instance.def_id(), poly_substs));
            let generic = poly_poly_instance == poly_instance;
            if !generic {
                match cx.instance_adjustment_check(poly_poly_instance) {
                    Err(Error::TooGeneric) => (),
                    result => return result,
                }
            }
        }

        // We need to perform the following checks:
        // * If there is an annotation, then `instance_adjustment` will just use that annotation.
        //   We need to make sure that the annotation is correct.
        // * If trait impl method has annotation, then we need to check that whatever we infer/annotate from
        //   `instance_adjustment` matches that one.
        // * If the method is callable from FFI, then we also need to check it matches our FFI adjustment.

        let annotation = cx.preemption_count_annotation(instance.def_id());
        if let Some(adj) = annotation.adjustment {
            assert!(adj == adjustment);
        }

        if annotation.adjustment.is_some() && !annotation.unchecked {
            let mir = cx.analysis_instance_mir(instance.def);
            let adjustment_infer = cx.infer_adjustment(param_env, instance, mir)?;
            // Check if the inferred adjustment matches the annotation.
            if adjustment != adjustment_infer {
                let mut diag = cx.sess.struct_span_err(
                    cx.def_span(instance.def_id()),
                    format!(
                        "function annotated to have preemption count adjustment of {adjustment}"
                    ),
                );
                diag.note(format!("but the adjustment inferred is {adjustment_infer}"));
                cx.emit_with_use_site_info(diag);
            }
        }

        // Addition check for trait impl methods.
        if matches!(instance.def, ty::InstanceDef::Item(_)) &&
            let Some(impl_) = cx.impl_of_method(instance.def_id()) &&
            let Some(trait_) = cx.trait_id_of_impl(impl_)
        {
            let trait_def = cx.trait_def(trait_);
            let trait_item = cx
                .associated_items(impl_)
                .in_definition_order()
                .find(|x| x.def_id == instance.def_id())
                .unwrap()
                .trait_item_def_id
                .unwrap();
            for ancestor in trait_def.ancestors(cx.tcx, impl_).unwrap() {
                let Some(ancestor_item) = ancestor.item(cx.tcx, trait_item) else { continue };
                if let Some(ancestor_adj) = cx.preemption_count_annotation(ancestor_item.def_id).adjustment {
                    if adjustment != ancestor_adj {
                        let mut diag = cx.sess.struct_span_err(
                            cx.def_span(instance.def_id()),
                            format!("trait method annotated to have preemption count adjustment of {ancestor_adj}"),
                        );
                        diag.note(format!("but the adjustment of this implementing function is {adjustment}"));
                        diag.span_note(cx.def_span(ancestor_item.def_id), "the trait method is defined here");
                        cx.emit_with_use_site_info(diag);
                    }
                }
            }
        }

        // Addition check for FFI functions.
        // Verify that the inferred result is compatible with the FFI list.
        if cx
            .codegen_fn_attrs(instance.def_id())
            .contains_extern_indicator()
        {
            // Verify that the inferred result is compatible with the FFI list.
            let ffi_property = cx
                .ffi_property(instance)
                .unwrap_or(crate::atomic_context::FFI_DEF_DEFAULT);

            if adjustment != ffi_property.0 {
                let mut diag = cx.tcx.sess.struct_span_err(
                    cx.def_span(instance.def_id()),
                    format!(
                        "extern function `{}` must have preemption count adjustment {}",
                        cx.def_path_str(instance.def_id()),
                        ffi_property.0,
                    ),
                );
                diag.note(format!(
                    "preemption count adjustment inferred is {adjustment}",
                ));
                diag.emit();
            }
        }

        Ok(())
    }
);

impl crate::ctxt::PersistentQuery for instance_adjustment {
    type LocalKey<'tcx> = Instance<'tcx>;

    fn into_crate_and_local<'tcx>(key: Self::Key<'tcx>) -> (CrateNum, Self::LocalKey<'tcx>) {
        let instance = key.value;
        (instance.def_id().krate, instance)
    }
}
