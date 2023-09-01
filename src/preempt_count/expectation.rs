use rustc_errors::{EmissionGuarantee, MultiSpan};
use rustc_hir::def_id::CrateNum;
use rustc_hir::{Constness, LangItem};
use rustc_middle::mir::{self, Body, TerminatorKind};
use rustc_middle::ty::{self, Instance, InternalSubsts, ParamEnv, ParamEnvAnd, Ty};
use rustc_mir_dataflow::lattice::MeetSemiLattice;
use rustc_mir_dataflow::Analysis;
use rustc_span::DUMMY_SP;

use super::dataflow::AdjustmentComputation;
use super::*;
use crate::ctxt::AnalysisCtxt;

impl<'tcx> AnalysisCtxt<'tcx> {
    pub fn terminator_expectation(
        &self,
        param_env: ParamEnv<'tcx>,
        instance: Instance<'tcx>,
        body: &Body<'tcx>,
        terminator: &mir::Terminator<'tcx>,
    ) -> Result<ExpectationRange, Error> {
        Ok(match &terminator.kind {
            TerminatorKind::Call { func, .. } => {
                let callee_ty = func.ty(body, self.tcx);
                let callee_ty = instance.subst_mir_and_normalize_erasing_regions(
                    self.tcx,
                    param_env,
                    ty::EarlyBinder::bind(callee_ty),
                );
                if let ty::FnDef(def_id, substs) = *callee_ty.kind() {
                    if let Some(v) = self.preemption_count_annotation(def_id).expectation {
                        // Fast path, no need to resolve the instance.
                        // This also avoids `TooGeneric` when def_id is an trait method.
                        v
                    } else {
                        let callee_instance =
                            ty::Instance::resolve(self.tcx, param_env, def_id, substs)
                                .unwrap()
                                .ok_or(Error::TooGeneric)?;
                        self.call_stack.borrow_mut().push(UseSite {
                            instance: param_env.and(instance),
                            kind: UseSiteKind::Call(terminator.source_info.span),
                        });
                        let result = self.instance_expectation(param_env.and(callee_instance));
                        self.call_stack.borrow_mut().pop();
                        result?
                    }
                } else {
                    crate::atomic_context::INDIRECT_DEFAULT.1
                }
            }
            TerminatorKind::Drop { place, .. } => {
                let ty = place.ty(body, self.tcx).ty;
                let ty = instance.subst_mir_and_normalize_erasing_regions(
                    self.tcx,
                    param_env,
                    ty::EarlyBinder::bind(ty),
                );

                self.call_stack.borrow_mut().push(UseSite {
                    instance: param_env.and(instance),
                    kind: UseSiteKind::Drop {
                        drop_span: terminator.source_info.span,
                        place_span: body.local_decls[place.local].source_info.span,
                    },
                });
                let result = self.drop_expectation(param_env.and(ty));
                self.call_stack.borrow_mut().pop();
                result?
            }
            _ => ExpectationRange::top(),
        })
    }

    #[instrument(skip(self, param_env, body, diag), fields(instance = %PolyDisplay(&param_env.and(instance))), ret)]
    pub fn report_body_expectation_error<G: EmissionGuarantee>(
        &self,
        param_env: ParamEnv<'tcx>,
        instance: Instance<'tcx>,
        body: &Body<'tcx>,
        expected: ExpectationRange,
        span: Option<MultiSpan>,
        diag: &mut rustc_errors::DiagnosticBuilder<'_, G>,
    ) -> Result<(), Error> {
        let mut analysis_result = AdjustmentComputation {
            checker: self,
            body,
            param_env,
            instance,
        }
        .into_engine(self.tcx, body)
        .iterate_to_fixpoint()
        .into_results_cursor(body);

        for (b, data) in rustc_middle::mir::traversal::reachable(body) {
            if data.is_cleanup {
                continue;
            }

            let expectation =
                self.terminator_expectation(param_env, instance, body, data.terminator())?;

            // Special case for no expectation at all. No need to check adjustment here.
            if expectation == ExpectationRange::top() {
                continue;
            }

            analysis_result.seek_to_block_start(b);
            let adjustment = analysis_result.get().into_result()?;

            let call_expected = expected + adjustment;
            if expectation.contains_range(call_expected) {
                continue;
            }

            // This call violates the expectation rules. Go check further.

            match &data.terminator().kind {
                TerminatorKind::Call { func, .. } => {
                    let mut span =
                        span.unwrap_or_else(|| data.terminator().source_info.span.into());
                    let callee_ty = func.ty(body, self.tcx);
                    let callee_ty = instance.subst_mir_and_normalize_erasing_regions(
                        self.tcx,
                        param_env,
                        ty::EarlyBinder::bind(callee_ty),
                    );
                    if let ty::FnDef(def_id, substs) = *callee_ty.kind() {
                        if let Some(v) = self.preemption_count_annotation(def_id).expectation {
                            if !span.has_primary_spans() {
                                span = self.def_span(def_id).into();
                            }

                            diag.span_note(
                                span,
                                format!(
                                    "which may call this function with preemption count {}",
                                    expected
                                ),
                            );
                            diag.note(format!("but the callee expects preemption count {}", v));
                            return Ok(());
                        } else {
                            let callee_instance =
                                ty::Instance::resolve(self.tcx, param_env, def_id, substs)
                                    .unwrap()
                                    .ok_or(Error::TooGeneric)?;

                            if !span.has_primary_spans() {
                                span = self.def_span(callee_instance.def_id()).into();
                            }

                            self.call_stack.borrow_mut().push(UseSite {
                                instance: param_env.and(instance),
                                kind: UseSiteKind::Call(span.primary_span().unwrap_or(DUMMY_SP)),
                            });
                            let result = self.report_instance_expectation_error(
                                param_env,
                                callee_instance,
                                call_expected,
                                span,
                                diag,
                            );
                            self.call_stack.borrow_mut().pop();
                            result?
                        }
                    } else {
                        diag.span_note(
                            span,
                            format!(
                                "which performs indirect function call with preemption count {}",
                                expected
                            ),
                        );
                        diag.note(format!(
                            "but indirect function calls are assumed to expect {}",
                            crate::atomic_context::INDIRECT_DEFAULT.1
                        ));
                        return Ok(());
                    }
                }
                TerminatorKind::Drop { place, .. } => {
                    let span = span.unwrap_or_else(|| {
                        let mut multispan =
                            MultiSpan::from_span(data.terminator().source_info.span);
                        multispan.push_span_label(
                            body.local_decls[place.local].source_info.span,
                            "value being dropped is here",
                        );
                        multispan
                    });
                    let ty = place.ty(body, self.tcx).ty;
                    let ty = instance.subst_mir_and_normalize_erasing_regions(
                        self.tcx,
                        param_env,
                        ty::EarlyBinder::bind(ty),
                    );

                    self.call_stack.borrow_mut().push(UseSite {
                        instance: param_env.and(instance),
                        kind: UseSiteKind::Drop {
                            drop_span: data.terminator().source_info.span,
                            place_span: body.local_decls[place.local].source_info.span,
                        },
                    });

                    let result = self.report_drop_expectation_error(
                        param_env,
                        ty,
                        call_expected,
                        span,
                        diag,
                    );
                    self.call_stack.borrow_mut().pop();
                    result?;
                }
                _ => (),
            };

            return Ok(());
        }

        unreachable!()
    }

    // Expectation error reporting is similar to expectation inference, but the direction is reverted.
    // For inference, we first determine the range of preemption count of the callee, and then combine
    // all call-sites to determine the preemption count requirement of the outer function. For reporting,
    // we have a pre-determined expectation, and then we need to recurse into the callees to find a violation.
    //
    // Must only be called on instances that actually are errors.
    pub fn report_instance_expectation_error<G: EmissionGuarantee>(
        &self,
        param_env: ParamEnv<'tcx>,
        instance: Instance<'tcx>,
        expected: ExpectationRange,
        span: MultiSpan,
        diag: &mut rustc_errors::DiagnosticBuilder<'_, G>,
    ) -> Result<(), Error> {
        // let expectation = cx.instance_expectation(param_env.and(instance))?;

        match instance.def {
            // No Rust built-in intrinsics will mess with preemption count.
            ty::InstanceDef::Intrinsic(_) => unreachable!(),
            // Empty drop glue, then it definitely won't mess with preemption count.
            ty::InstanceDef::DropGlue(_, None) => unreachable!(),
            ty::InstanceDef::DropGlue(_, Some(ty)) => {
                return self.report_drop_expectation_error(param_env, ty, expected, span, diag);
            }
            // Checked by indirect checks
            ty::InstanceDef::Virtual(def_id, _) => {
                let exp = self
                    .preemption_count_annotation(def_id)
                    .expectation
                    .unwrap_or(crate::atomic_context::VCALL_DEFAULT.1);
                diag.span_note(
                    span,
                    format!(
                        "which may call this dynamic dispatch with preemption count {}",
                        expected
                    ),
                );
                diag.note(format!(
                    "but this dynamic dispatch expects preemption count {}",
                    exp
                ));
                return Ok(());
            }
            _ => (),
        }

        if self.is_foreign_item(instance.def_id()) {
            let exp = self
                .ffi_property(instance)
                .unwrap_or(crate::atomic_context::FFI_USE_DEFAULT)
                .1;
            diag.span_note(
                span,
                format!(
                    "which may perform this FFI call with preemption count {}",
                    expected
                ),
            );
            diag.note(format!("but the callee expects preemption count {}", exp));
            return Ok(());
        }

        // Only check locally codegenned instances.
        if !crate::monomorphize_collector::should_codegen_locally(self.tcx, &instance) {
            let expectation = self.instance_expectation(param_env.and(instance))?;
            diag.span_note(
                span,
                format!(
                    "which may call this function with preemption count {}",
                    expected
                ),
            );
            diag.note(format!(
                "but this function expects preemption count {}",
                expectation
            ));
            return Ok(());
        }

        diag.span_note(
            span,
            format!(
                "which may call this function with preemption count {}",
                expected
            ),
        );

        let body = self.analysis_instance_mir(instance.def);
        self.report_body_expectation_error(param_env, instance, body, expected, None, diag)
    }

    pub fn report_drop_expectation_error<G: EmissionGuarantee>(
        &self,
        param_env: ParamEnv<'tcx>,
        ty: Ty<'tcx>,
        expected: ExpectationRange,
        span: MultiSpan,
        diag: &mut rustc_errors::DiagnosticBuilder<'_, G>,
    ) -> Result<(), Error> {
        // If the type doesn't need drop, then there is trivially no expectation.
        assert!(ty.needs_drop(self.tcx, param_env));

        match ty.kind() {
            ty::Closure(_, substs) => {
                return self.report_drop_expectation_error(
                    param_env,
                    substs.as_closure().tupled_upvars_ty(),
                    expected,
                    span,
                    diag,
                );
            }

            // Generator drops are non-trivial, use the generated drop shims instead.
            ty::Generator(..) => (),

            ty::Tuple(_list) => (),

            ty::Adt(def, substs) if def.is_box() => {
                let exp = self.drop_expectation(param_env.and(substs.type_at(0)))?;
                if !exp.contains_range(expected) {
                    return self.report_drop_expectation_error(
                        param_env,
                        substs.type_at(0),
                        expected,
                        span,
                        diag,
                    );
                }
                let adj = self.drop_adjustment(param_env.and(substs.type_at(0)))?;

                let drop_trait = self.require_lang_item(LangItem::Drop, None);
                let drop_fn = self.associated_item_def_ids(drop_trait)[0];
                let box_free = ty::Instance::resolve(
                    self.tcx,
                    param_env,
                    drop_fn,
                    self.mk_substs(&[ty.into()]),
                )
                .unwrap()
                .unwrap();
                return self.report_instance_expectation_error(
                    param_env,
                    box_free,
                    expected + AdjustmentBounds::single_value(adj),
                    span,
                    diag,
                );
            }

            ty::Adt(def, _) => {
                if let Some(exp) = self.drop_preemption_count_annotation(def.did()).expectation {
                    diag.span_note(
                        span,
                        format!("which may drop here with preemption count {}", expected),
                    );
                    diag.note(format!("but this drop expects preemption count {}", exp));
                    return Ok(());
                }
            }

            ty::Dynamic(pred, ..) => {
                let exp = pred
                    .principal_def_id()
                    .and_then(|principal_trait| {
                        self.drop_preemption_count_annotation(principal_trait)
                            .expectation
                    })
                    .unwrap_or(crate::atomic_context::VDROP_DEFAULT.1);
                diag.span_note(
                    span,
                    format!("which may drop here with preemption count {}", expected),
                );
                diag.note(format!("but this drop expects preemption count {}", exp));
                return Ok(());
            }

            ty::Array(elem_ty, size) => {
                let param_and_elem_ty = param_env.and(*elem_ty);
                let elem_exp = self.drop_expectation(param_and_elem_ty)?;
                if !elem_exp.contains_range(expected) {
                    return self
                        .report_drop_expectation_error(param_env, *elem_ty, expected, span, diag);
                }

                let elem_adj = self.drop_adjustment(param_and_elem_ty)?;
                let size = size
                    .try_eval_target_usize(self.tcx, param_env)
                    .ok_or(Error::TooGeneric)?;
                let Ok(size) = i32::try_from(size) else {
                    return Ok(());
                };
                let Some(last_adj) = (size - 1).checked_mul(elem_adj) else {
                    return Ok(());
                };
                let last_adj_bound = AdjustmentBounds::single_value(last_adj);
                return self.report_drop_expectation_error(
                    param_env,
                    *elem_ty,
                    expected + last_adj_bound,
                    span,
                    diag,
                );
            }

            ty::Slice(elem_ty) => {
                return self
                    .report_drop_expectation_error(param_env, *elem_ty, expected, span, diag);
            }

            _ => unreachable!(),
        }

        diag.span_note(
            span,
            format!(
                "which may drop type `{}` with preemption count {}",
                PolyDisplay(&param_env.and(ty)),
                expected,
            ),
        );
        let span = MultiSpan::new();

        // Do not call `resolve_drop_in_place` because we need param_env.
        let drop_in_place = self.require_lang_item(LangItem::DropInPlace, None);
        let substs = self.mk_substs(&[ty.into()]);
        let instance = ty::Instance::resolve(self.tcx, param_env, drop_in_place, substs)
            .unwrap()
            .unwrap();

        let mir = crate::mir::drop_shim::build_drop_shim(self, instance.def_id(), param_env, ty);
        return self.report_body_expectation_error(
            param_env,
            instance,
            &mir,
            expected,
            Some(span),
            diag,
        );
    }

    pub fn do_infer_expectation(
        &self,
        param_env: ParamEnv<'tcx>,
        instance: Instance<'tcx>,
        body: &Body<'tcx>,
    ) -> Result<ExpectationRange, Error> {
        if false {
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

        let mut expectation_infer = ExpectationRange::top();
        for (b, data) in rustc_middle::mir::traversal::reachable(body) {
            if data.is_cleanup {
                continue;
            }

            let expectation = match &data.terminator().kind {
                TerminatorKind::Call { func, .. } => {
                    let callee_ty = func.ty(body, self.tcx);
                    let callee_ty = instance.subst_mir_and_normalize_erasing_regions(
                        self.tcx,
                        param_env,
                        ty::EarlyBinder::bind(callee_ty),
                    );
                    if let ty::FnDef(def_id, substs) = *callee_ty.kind() {
                        if let Some(v) = self.preemption_count_annotation(def_id).expectation {
                            // Fast path, no need to resolve the instance.
                            // This also avoids `TooGeneric` when def_id is an trait method.
                            v
                        } else {
                            let callee_instance =
                                ty::Instance::resolve(self.tcx, param_env, def_id, substs)
                                    .unwrap()
                                    .ok_or(Error::TooGeneric)?;
                            self.call_stack.borrow_mut().push(UseSite {
                                instance: param_env.and(instance),
                                kind: UseSiteKind::Call(data.terminator().source_info.span),
                            });
                            let result = self.instance_expectation(param_env.and(callee_instance));
                            self.call_stack.borrow_mut().pop();
                            result?
                        }
                    } else {
                        crate::atomic_context::INDIRECT_DEFAULT.1
                    }
                }
                TerminatorKind::Drop { place, .. } => {
                    let ty = place.ty(body, self.tcx).ty;
                    let ty = instance.subst_mir_and_normalize_erasing_regions(
                        self.tcx,
                        param_env,
                        ty::EarlyBinder::bind(ty),
                    );

                    self.call_stack.borrow_mut().push(UseSite {
                        instance: param_env.and(instance),
                        kind: UseSiteKind::Drop {
                            drop_span: data.terminator().source_info.span,
                            place_span: body.local_decls[place.local].source_info.span,
                        },
                    });
                    let result = self.drop_expectation(param_env.and(ty));
                    self.call_stack.borrow_mut().pop();
                    result?
                }
                _ => continue,
            };

            // Special case for no expectation at all. No need to check adjustment here.
            if expectation == ExpectationRange::top() {
                continue;
            }

            analysis_result.seek_to_block_start(b);
            let adjustment = analysis_result.get().into_result()?;

            // We need to find a range that for all possible values in `adj`, it will end up in a value
            // that lands inside `expectation`.
            //
            // For example, if adjustment is `0..`, and range is `0..1`, then the range we want is `0..0`,
            // i.e. an empty range, because no matter what preemption count we start with, if we apply an
            // adjustment >0, then it will be outside the range.
            let mut expected = expectation - adjustment;
            expected.meet(&expectation_infer);
            if expected.is_empty() {
                // This function will cause the entry state to be in an unsatisfiable condition.
                // Generate an error.
                let (kind, drop_span) = match data.terminator().kind {
                    TerminatorKind::Drop { place, .. } => {
                        ("drop", Some(body.local_decls[place.local].source_info.span))
                    }
                    _ => ("call", None),
                };
                let span = data.terminator().source_info.span;
                let mut diag = self.tcx.sess.struct_span_err(
                    span,
                    format!(
                        "this {kind} expects the preemption count to be {}",
                        expectation
                    ),
                );

                if let Some(span) = drop_span {
                    diag.span_label(span, "the value being dropped is declared here");
                }

                diag.note(format!(
                    "but the possible preemption count at this point is {}",
                    expectation_infer + adjustment
                ));

                // Stop processing other calls in this function to avoid generating too many errors.
                return Err(Error::Error(self.emit_with_use_site_info(diag)));
            }

            expectation_infer = expected;
        }

        Ok(expectation_infer)
    }

    pub fn infer_expectation(
        &self,
        param_env: ParamEnv<'tcx>,
        instance: Instance<'tcx>,
        body: &Body<'tcx>,
    ) -> Result<ExpectationRange, Error> {
        if !self
            .recursion_limit()
            .value_within_limit(self.call_stack.borrow().len())
        {
            self.emit_with_use_site_info(self.sess.struct_fatal(format!(
                "reached the recursion limit while checking expectation for `{}`",
                PolyDisplay(&param_env.and(instance))
            )));
        }

        rustc_data_structures::stack::ensure_sufficient_stack(|| {
            self.do_infer_expectation(param_env, instance, body)
        })
    }
}

memoize!(
    #[instrument(skip(cx), fields(poly_ty = %PolyDisplay(&poly_ty)), ret)]
    pub fn drop_expectation<'tcx>(
        cx: &AnalysisCtxt<'tcx>,
        poly_ty: ParamEnvAnd<'tcx, Ty<'tcx>>,
    ) -> Result<ExpectationRange, Error> {
        let (param_env, ty) = poly_ty.into_parts();

        // If the type doesn't need drop, then there is trivially no expectation.
        if !ty.needs_drop(cx.tcx, param_env) {
            return Ok(ExpectationRange::top());
        }

        match ty.kind() {
            ty::Closure(_, substs) => {
                return cx.drop_expectation(param_env.and(substs.as_closure().tupled_upvars_ty()));
            }

            // Generator drops are non-trivial, use the generated drop shims instead.
            ty::Generator(..) => (),

            ty::Tuple(_list) => (),

            ty::Adt(def, substs) if def.is_box() => {
                let exp = cx.drop_expectation(param_env.and(substs.type_at(0)))?;
                let drop_trait = cx.require_lang_item(LangItem::Drop, None);
                let drop_fn = cx.associated_item_def_ids(drop_trait)[0];
                let box_free =
                    ty::Instance::resolve(cx.tcx, param_env, drop_fn, cx.mk_substs(&[ty.into()]))
                        .unwrap()
                        .unwrap();
                let box_free_exp = cx.instance_expectation(param_env.and(box_free))?;

                // Usuaully freeing the box shouldn't have any instance expectations, so short circuit here.
                if box_free_exp == ExpectationRange::top() {
                    return Ok(exp);
                }

                let adj = cx.drop_adjustment(param_env.and(substs.type_at(0)))?;
                let adj_bound = AdjustmentBounds::single_value(adj);

                let mut expected = box_free_exp - adj_bound;
                expected.meet(&exp);
                if expected.is_empty() {
                    let mut diag = cx.sess.struct_err(format!(
                        "freeing the box expects the preemption count to be {}",
                        box_free_exp
                    ));
                    diag.note(format!(
                        "but the possible preemption count after dropping the content is {}",
                        exp + adj_bound
                    ));
                    diag.note(format!("content being dropped is `{}`", substs.type_at(0)));
                    return Err(Error::Error(cx.emit_with_use_site_info(diag)));
                }

                return Ok(expected);
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
                    match cx.drop_expectation(poly_poly_ty) {
                        Err(Error::TooGeneric) => (),
                        expectation => return expectation,
                    }
                }

                // If that fails, we try to use the substs.
                // Fallthrough to the MIR drop shim based logic.

                if let Some(exp) = cx.drop_preemption_count_annotation(def.did()).expectation {
                    info!("expectation {} from annotation", exp);
                    return Ok(exp);
                }
            }

            ty::Dynamic(pred, ..) => {
                if let Some(principal_trait) = pred.principal_def_id() {
                    if let Some(exp) = cx
                        .drop_preemption_count_annotation(principal_trait)
                        .expectation
                    {
                        return Ok(exp);
                    }
                }
                return Ok(crate::atomic_context::VDROP_DEFAULT.1);
            }

            ty::Array(elem_ty, size) => {
                let size = size
                    .try_eval_target_usize(cx.tcx, param_env)
                    .ok_or(Error::TooGeneric);
                if size == Ok(0) {
                    return Ok(ExpectationRange::top());
                }

                // Special case for no expectation at all. No need to check adjustment here.
                let param_and_elem_ty = param_env.and(*elem_ty);
                let elem_exp = cx.drop_expectation(param_and_elem_ty)?;
                if elem_exp == ExpectationRange::top() {
                    return Ok(ExpectationRange::top());
                }

                let elem_adj = cx.drop_adjustment(param_and_elem_ty)?;
                if elem_adj == 0 {
                    return Ok(elem_exp);
                }

                // If any error happens here, it'll happen in adjustment calculation too, so just return
                // to avoid duplicate errors.
                let Ok(size) = i32::try_from(size?) else {
                    return Ok(ExpectationRange::top());
                };
                let Some(last_adj) = (size - 1).checked_mul(elem_adj) else {
                    return Ok(ExpectationRange::top());
                };

                let last_adj_bound = AdjustmentBounds::single_value(last_adj);

                let mut expected = elem_exp - last_adj_bound;
                expected.meet(&elem_exp);
                if expected.is_empty() {
                    let mut diag = cx.sess.struct_err(format!(
                        "dropping element of array expects the preemption count to be {}",
                        elem_exp
                    ));
                    diag.note(format!(
                        "but the possible preemption count when dropping the last element is {}",
                        elem_exp + last_adj_bound
                    ));
                    diag.note(format!("array being dropped is `{}`", ty));
                    return Err(Error::Error(cx.emit_with_use_site_info(diag)));
                }

                return Ok(expected);
            }

            ty::Slice(elem_ty) => {
                // We can assume adjustment here is 0 otherwise the adjustment calculation
                // logic would have complained.
                return cx.drop_expectation(param_env.and(*elem_ty));
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
                return Ok(ExpectationRange::top());
            } else {
                // If we are handling generic functions, then defer decision to monomorphization time.
                return Err(Error::TooGeneric);
            }
        }

        let mir = crate::mir::drop_shim::build_drop_shim(cx, instance.def_id(), param_env, ty);
        let result = cx.infer_expectation(param_env, instance, &mir);

        // Recursion encountered.
        if let Some(&recur) = cx.query_cache::<drop_expectation>().borrow().get(&poly_ty) {
            match (result, recur) {
                (_, Err(Error::Error(_))) => bug!("recursive callee errors"),
                // Error already reported.
                (Err(Error::Error(_)), _) => (),
                (Err(_), Err(_)) => (),
                (Ok(a), Ok(b)) if a == b => (),
                (Ok(_), Err(_)) => bug!("recursive callee too generic but caller is not"),
                (Err(_), Ok(_)) => bug!("monormorphic caller too generic"),
                (Ok(exp), Ok(_)) => {
                    let mut diag = cx.sess.struct_span_err(
                        ty.ty_adt_def()
                            .map(|x| cx.def_span(x.did()))
                            .unwrap_or_else(|| cx.def_span(instance.def_id())),
                        "dropping this type causes recursion while also has preemption count expectation",
                    );
                    diag.note(format!("expectation inferred is {}", exp));
                    diag.note(format!("type being dropped is `{}`", ty));
                    diag.emit();
                }
            }
        }

        // if instance.def_id().is_local() && param_env.caller_bounds().is_empty() {
        //     cx.sql_store::<drop_adjustment>(poly_instance, result);
        // }

        result
    }
);

memoize!(
    #[instrument(skip(cx), fields(poly_ty = %PolyDisplay(&poly_ty)), ret)]
    pub fn drop_expectation_check<'tcx>(
        cx: &AnalysisCtxt<'tcx>,
        poly_ty: ParamEnvAnd<'tcx, Ty<'tcx>>,
    ) -> Result<(), Error> {
        let expectation = cx.drop_expectation(poly_ty)?;
        let (param_env, ty) = poly_ty.into_parts();

        // If the type doesn't need drop, then there is trivially no expectation.
        if !ty.needs_drop(cx.tcx, param_env) {
            return Ok(());
        }

        let annotation;
        match ty.kind() {
            // These types are always inferred
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
                    match cx.drop_expectation_check(poly_poly_ty) {
                        Err(Error::TooGeneric) => (),
                        result => return result,
                    }
                }

                // If that fails, we try to use the substs.
                // Fallthrough to the MIR drop shim based logic.

                annotation = cx.drop_preemption_count_annotation(def.did());
                if let Some(exp) = annotation.expectation {
                    assert!(exp == expectation);
                }
            }

            _ => return Err(Error::TooGeneric),
        }

        // If expectation is inferred or the type is annotated as unchecked,
        // then we don't need to do any further checks.
        if annotation.expectation.is_none() || annotation.unchecked {
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
        let expectation_infer = cx.infer_expectation(param_env, instance, &mir)?;
        // Check if the inferred expectation matches the annotation.
        if !expectation_infer.contains_range(expectation) {
            let mut diag = cx.sess.struct_span_err(
                cx.def_span(instance.def_id()),
                format!(
                    "type annotated to have drop preemption count expectation of {}",
                    expectation
                ),
            );
            diag.note(format!(
                "but the expectation inferred is {expectation_infer}"
            ));
            diag.emit();
        }

        Ok(())
    }
);

memoize!(
    #[instrument(skip(cx), fields(poly_instance = %PolyDisplay(&poly_instance)), ret)]
    pub fn instance_expectation<'tcx>(
        cx: &AnalysisCtxt<'tcx>,
        poly_instance: ParamEnvAnd<'tcx, Instance<'tcx>>,
    ) -> Result<ExpectationRange, Error> {
        let (param_env, instance) = poly_instance.into_parts();
        match instance.def {
            // No Rust built-in intrinsics will mess with preemption count.
            ty::InstanceDef::Intrinsic(_) => return Ok(ExpectationRange::top()),
            // Empty drop glue, then it definitely won't mess with preemption count.
            ty::InstanceDef::DropGlue(_, None) => return Ok(ExpectationRange::top()),
            ty::InstanceDef::DropGlue(_, Some(ty)) => {
                return cx.drop_expectation(param_env.and(ty))
            }
            ty::InstanceDef::Virtual(def_id, _) => {
                if let Some(exp) = cx.preemption_count_annotation(def_id).expectation {
                    return Ok(exp);
                }

                return Ok(crate::atomic_context::VCALL_DEFAULT.1);
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
                match cx.instance_expectation(poly_poly_instance) {
                    Err(Error::TooGeneric) => (),
                    expectation => return expectation,
                }
            }
        }

        if cx.is_foreign_item(instance.def_id()) {
            return Ok(cx
                .ffi_property(instance)
                .unwrap_or(crate::atomic_context::FFI_USE_DEFAULT)
                .1);
        }

        if !crate::monomorphize_collector::should_codegen_locally(cx.tcx, &instance) {
            if let Some(p) = cx.sql_load::<instance_expectation>(poly_instance) {
                return p;
            }

            // If we cannot load it, use annotation (e.g. libcore).
            return Ok(cx
                .preemption_count_annotation(instance.def_id())
                .expectation
                .unwrap_or(ExpectationRange::top()));
        }

        // Use annotation if available.
        if let Some(exp) = cx
            .preemption_count_annotation(instance.def_id())
            .expectation
        {
            info!("expectation {} from annotation", exp);
            return Ok(exp);
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
                return Ok(ExpectationRange::top());
            } else {
                // If we are handling generic functions, then defer decision to monomorphization time.
                return Err(Error::TooGeneric);
            }
        }

        let mir = cx.analysis_instance_mir(instance.def);
        let result = cx.infer_expectation(param_env, instance, mir);

        // Recursion encountered.
        if let Some(recur) = cx
            .query_cache::<instance_expectation>()
            .borrow()
            .get(&poly_instance)
        {
            match (result, recur) {
                (_, Err(Error::Error(_))) => bug!("recursive callee errors"),
                // Error already reported.
                (Err(Error::Error(_)), _) => (),
                (Err(_), Err(_)) => (),
                (Ok(a), Ok(b)) if a == *b => (),
                (Ok(_), Err(_)) => bug!("recursive callee too generic but caller is not"),
                (Err(_), Ok(_)) => bug!("monormorphic caller too generic"),
                (Ok(exp), Ok(_)) => {
                    let mut diag = cx.sess.struct_span_err(
                        cx.def_span(instance.def_id()),
                        "this function is recursive but preemption count expectation is not 0..",
                    );
                    diag.note(format!("expectation is inferred to be {}", exp));
                    if !generic {
                        diag.note(format!(
                            "instance being checked is `{}`",
                            PolyDisplay(&poly_instance)
                        ));
                    }
                    diag.help(format!(
                        "try annotate the function with `#[redpen::preempt_count(expect = {exp})]`"
                    ));
                    diag.emit();
                }
            }
        }

        if instance.def_id().is_local() && (generic || param_env.caller_bounds().is_empty()) {
            cx.sql_store::<instance_expectation>(poly_instance, result);
        }

        if cx.should_report_preempt_count(instance.def_id()) {
            let mut diag = cx.sess.diagnostic().struct_note_without_error(format!(
                "reporting preemption count for instance `{}`",
                PolyDisplay(&poly_instance)
            ));
            diag.set_span(cx.def_span(instance.def_id()));
            if let Ok(property) = result {
                diag.note(format!("expectation is inferred to be {}", property));
            } else {
                diag.note("expectation inference failed because this function is too generic");
            }
            diag.emit();
        }

        result
    }
);

impl crate::ctxt::PersistentQuery for instance_expectation {
    type LocalKey<'tcx> = Instance<'tcx>;

    fn into_crate_and_local<'tcx>(key: Self::Key<'tcx>) -> (CrateNum, Self::LocalKey<'tcx>) {
        let instance = key.value;
        (instance.def_id().krate, instance)
    }
}

memoize!(
    #[instrument(skip(cx), fields(poly_instance = %PolyDisplay(&poly_instance)), ret)]
    pub fn instance_expectation_check<'tcx>(
        cx: &AnalysisCtxt<'tcx>,
        poly_instance: ParamEnvAnd<'tcx, Instance<'tcx>>,
    ) -> Result<(), Error> {
        let expectation = cx.instance_expectation(poly_instance)?;
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
                return cx.drop_expectation_check(param_env.and(ty))
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
                match cx.instance_expectation_check(poly_poly_instance) {
                    Err(Error::TooGeneric) => (),
                    result => return result,
                }
            }
        }

        // We need to perform the following checks:
        // * If there is an annotation, then `instance_expectation` will just use that annotation.
        //   We need to make sure that the annotation is correct.
        // * If trait impl method has annotation, then we need to check that whatever we infer/annotate from
        //   `instance_expectation` matches that one.
        // * If the method is callable from FFI, then we also need to check it matches our FFI expectation.

        let annotation = cx.preemption_count_annotation(instance.def_id());
        if let Some(exp) = annotation.expectation {
            assert!(exp == expectation);
        }

        let body = if annotation.expectation.is_none() || !annotation.unchecked {
            Some(cx.analysis_instance_mir(instance.def))
        } else {
            None
        };

        if annotation.expectation.is_some() && !annotation.unchecked {
            let mir = body.unwrap();
            let expectation_infer = cx.infer_expectation(param_env, instance, mir)?;
            // Check if the inferred expectation matches the annotation.
            if !expectation_infer.contains_range(expectation) {
                let mut diag = cx.sess.struct_span_err(
                    cx.def_span(instance.def_id()),
                    format!(
                        "function annotated to have preemption count expectation of {}",
                        expectation
                    ),
                );
                diag.note(format!(
                    "but the expectation inferred is {expectation_infer}"
                ));
                cx.report_body_expectation_error(
                    param_env,
                    instance,
                    mir,
                    expectation,
                    None,
                    &mut diag,
                )
                .unwrap();
                diag.emit();
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
                if let Some(ancestor_exp) = cx.preemption_count_annotation(ancestor_item.def_id).expectation {
                    if !expectation.contains_range(ancestor_exp) {
                        let mut diag = cx.sess.struct_span_err(
                            cx.def_span(instance.def_id()),
                            format!("trait method annotated to have preemption count expectation of {ancestor_exp}"),
                        );
                        diag.note(format!("but the expectation of this implementing function is {expectation}"));
                        diag.span_note(cx.def_span(ancestor_item.def_id), "the trait method is defined here");
                        if let Some(body) = body {
                            cx.report_body_expectation_error(
                                param_env,
                                instance,
                                body,
                                ancestor_exp,
                                None,
                                &mut diag,
                            )
                            .unwrap();
                        }
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

            // Check using the intersection -- the FFI property is allowed to be more restrictive.
            if !expectation.contains_range(ffi_property.1) {
                let mut diag = cx.sess.struct_span_err(
                    cx.def_span(instance.def_id()),
                    format!(
                        "extern function `{}` must have preemption count expectation {}",
                        cx.def_path_str(instance.def_id()),
                        ffi_property.1,
                    ),
                );
                diag.note(format!(
                    "preemption count expectation inferred is {expectation}",
                ));
                if let Some(body) = body {
                    cx.report_body_expectation_error(
                        param_env,
                        instance,
                        body,
                        ffi_property.1,
                        None,
                        &mut diag,
                    )
                    .unwrap();
                }
                diag.emit();
            }
        }

        Ok(())
    }
);
