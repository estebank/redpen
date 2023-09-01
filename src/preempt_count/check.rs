use super::*;
use crate::ctxt::AnalysisCtxt;
use rustc_hir::def_id::DefId;
use rustc_hir::{Constness, LangItem};
use rustc_infer::traits::util::PredicateSet;
use rustc_middle::mir::interpret::{AllocId, ConstValue, ErrorHandled, GlobalAlloc, Scalar};
use rustc_middle::mir::{self, visit::Visitor as MirVisitor, Body, Location};
use rustc_middle::ty::adjustment::PointerCoercion;
use rustc_middle::ty::{
    self, GenericParamDefKind, Instance, InternalSubsts, ParamEnv, ParamEnvAnd, ToPredicate, Ty,
    TyCtxt, TypeFoldable, TypeVisitableExt,
};

struct MirNeighborVisitor<'mir, 'tcx, 'cx> {
    cx: &'cx AnalysisCtxt<'tcx>,
    body: &'mir Body<'tcx>,
    param_env: ParamEnv<'tcx>,
    instance: Instance<'tcx>,
    result: Result<(), Error>,
}

impl<'mir, 'tcx, 'cx> MirNeighborVisitor<'mir, 'tcx, 'cx> {
    fn monomorphize<T: TypeFoldable<TyCtxt<'tcx>> + Clone>(&self, v: T) -> T {
        self.instance.subst_mir_and_normalize_erasing_regions(
            self.cx.tcx,
            self.param_env,
            ty::EarlyBinder::bind(v),
        )
    }

    fn check_vtable_unsizing(
        &mut self,
        source_ty: Ty<'tcx>,
        target_ty: Ty<'tcx>,
        span: Span,
    ) -> Result<(), Error> {
        let ty::Dynamic(ref source_trait_ref, ..) = source_ty.kind() else {
            bug!()
        };
        let ty::Dynamic(ref target_trait_ref, ..) = target_ty.kind() else {
            bug!()
        };

        let source_annotation = source_trait_ref
            .principal()
            .map(|x| self.cx.drop_preemption_count_annotation(x.def_id()))
            .unwrap_or_default();
        let target_annotation = target_trait_ref
            .principal()
            .map(|x| self.cx.drop_preemption_count_annotation(x.def_id()))
            .unwrap_or_default();

        let source_adjustment = source_annotation
            .adjustment
            .unwrap_or(crate::atomic_context::VDROP_DEFAULT.0);
        let target_adjustment = target_annotation
            .adjustment
            .unwrap_or(crate::atomic_context::VDROP_DEFAULT.0);
        let source_expectation = source_annotation
            .expectation
            .unwrap_or(crate::atomic_context::VDROP_DEFAULT.1);
        let target_expectation = target_annotation
            .expectation
            .unwrap_or(crate::atomic_context::VDROP_DEFAULT.1);

        if source_adjustment != target_adjustment
            || !source_expectation.contains_range(target_expectation)
        {
            let mut diag = self.cx.tcx.sess.struct_span_err(
                span,
                "casting between traits with incompatible preemption count properties",
            );
            diag.help(format!(
                "adjustment of `{}` is {} and expectation is {}",
                source_ty, source_adjustment, source_expectation
            ));
            diag.help(format!(
                "while the expected adjustment of `{}` is {} and the expectation is {}",
                target_ty, target_adjustment, target_expectation
            ));
            self.cx.emit_with_use_site_info(diag);
            return Ok(());
        }

        Ok(())
    }

    fn check_vtable_construction(
        &mut self,
        ty: Ty<'tcx>,
        trait_ref: Option<ty::PolyExistentialTraitRef<'tcx>>,
        span: Span,
    ) -> Result<(), Error> {
        self.cx.call_stack.borrow_mut().push(UseSite {
            instance: self.param_env.and(self.instance),
            kind: UseSiteKind::Vtable(span),
        });
        let result = self
            .cx
            .vtable_construction_check_indirect(self.param_env.and((ty, trait_ref)));
        self.cx.call_stack.borrow_mut().pop();
        result
    }

    fn check_fn_pointer_cast(&mut self, instance: Instance<'tcx>, span: Span) -> Result<(), Error> {
        self.cx.call_stack.borrow_mut().push(UseSite {
            instance: self.param_env.and(self.instance),
            kind: UseSiteKind::PointerCoercion(span),
        });
        let result = self
            .cx
            .function_pointer_cast_check_indirect(self.param_env.and(instance));
        self.cx.call_stack.borrow_mut().pop();
        result
    }

    fn check_rvalue(
        &mut self,
        rvalue: &mir::Rvalue<'tcx>,
        location: Location,
    ) -> Result<(), Error> {
        let span = self.body.source_info(location).span;

        match *rvalue {
            mir::Rvalue::Cast(
                mir::CastKind::PointerCoercion(PointerCoercion::Unsize),
                ref operand,
                target_ty,
            )
            | mir::Rvalue::Cast(mir::CastKind::DynStar, ref operand, target_ty) => {
                let target_ty = self.monomorphize(target_ty);
                let source_ty = operand.ty(self.body, self.cx.tcx);
                let source_ty = self.monomorphize(source_ty);
                let (source_ty, target_ty) =
                    crate::monomorphize_collector::find_vtable_types_for_unsizing(
                        self.cx.tcx.at(span),
                        self.param_env,
                        source_ty,
                        target_ty,
                    );
                if let ty::Dynamic(ref trait_ty, ..) = target_ty.kind() {
                    if let ty::Dynamic(..) = source_ty.kind() {
                        // This is trait upcasting.
                        self.check_vtable_unsizing(source_ty, target_ty, span)?;
                    } else {
                        // This is unsizing of a concrete type to a trait object.
                        self.check_vtable_construction(source_ty, trait_ty.principal(), span)?;
                    }
                }
            }
            mir::Rvalue::Cast(
                mir::CastKind::PointerCoercion(PointerCoercion::ReifyFnPointer),
                ref operand,
                _,
            ) => {
                let fn_ty = operand.ty(self.body, self.cx.tcx);
                let fn_ty = self.monomorphize(fn_ty);
                if let ty::FnDef(def_id, substs) = *fn_ty.kind() {
                    let instance =
                        ty::Instance::resolve(self.cx.tcx, self.param_env, def_id, substs)
                            .unwrap()
                            .ok_or(Error::TooGeneric)?;
                    self.check_fn_pointer_cast(instance, span)?;
                }
            }
            mir::Rvalue::Cast(
                mir::CastKind::PointerCoercion(PointerCoercion::ClosureFnPointer(_)),
                ref operand,
                _,
            ) => {
                let source_ty = operand.ty(self.body, self.cx.tcx);
                let source_ty = self.monomorphize(source_ty);
                match *source_ty.kind() {
                    ty::Closure(def_id, substs) => {
                        let instance = Instance::resolve_closure(
                            self.cx.tcx,
                            def_id,
                            substs,
                            ty::ClosureKind::FnOnce,
                        )
                        .ok_or(Error::TooGeneric)?;
                        self.check_fn_pointer_cast(instance, span)?;
                    }
                    _ => bug!(),
                }
            }
            mir::Rvalue::ThreadLocalRef(def_id) => {
                assert!(self.cx.is_thread_local_static(def_id));
                self.check_static(def_id)?;
            }
            _ => (),
        }

        Ok(())
    }

    fn check_alloc(&mut self, alloc_id: AllocId, span: Span) -> Result<(), Error> {
        match self.cx.global_alloc(alloc_id) {
            GlobalAlloc::Static(def_id) => {
                assert!(!self.cx.is_thread_local_static(def_id));
                self.check_static(def_id)?;
            }
            GlobalAlloc::Memory(alloc) => {
                for inner in alloc.inner().provenance().provenances() {
                    rustc_data_structures::stack::ensure_sufficient_stack(|| {
                        self.check_alloc(inner, span)
                    })?;
                }
            }
            GlobalAlloc::Function(fn_instance) => {
                self.check_fn_pointer_cast(fn_instance, span)?;
            }
            GlobalAlloc::VTable(ty, trait_ref) => {
                self.check_vtable_construction(ty, trait_ref, span)?;
            }
        }

        Ok(())
    }

    fn check_const(&mut self, value: ConstValue, span: Span) -> Result<(), Error> {
        match value {
            ConstValue::Scalar(Scalar::Ptr(ptr, _size)) => {
                self.check_alloc(ptr.provenance, span)?;
            }
            ConstValue::Slice {
                data: alloc,
                start: _,
                end: _,
            }
            | ConstValue::ByRef { alloc, .. } => {
                for id in alloc.inner().provenance().provenances() {
                    self.check_alloc(id, span)?;
                }
            }
            _ => {}
        }
        Ok(())
    }

    fn check_terminator(
        &mut self,
        terminator: &mir::Terminator<'tcx>,
        location: Location,
    ) -> Result<(), Error> {
        let span = self.body.source_info(location).span;

        let tcx = self.cx.tcx;
        match terminator.kind {
            mir::TerminatorKind::Call { ref func, .. } => {
                let callee_ty = func.ty(self.body, tcx);
                let callee_ty = self.monomorphize(callee_ty);

                if let ty::FnDef(def_id, substs) = *callee_ty.kind() {
                    let instance =
                        ty::Instance::resolve(self.cx.tcx, self.param_env, def_id, substs)
                            .unwrap()
                            .ok_or(Error::TooGeneric)?;
                    self.cx.call_stack.borrow_mut().push(UseSite {
                        instance: self.param_env.and(self.instance),
                        kind: UseSiteKind::Call(span),
                    });
                    let result = self.cx.instance_check(self.param_env.and(instance));
                    self.cx.call_stack.borrow_mut().pop();
                    result?
                }
            }
            mir::TerminatorKind::Drop { ref place, .. } => {
                let ty = place.ty(self.body, self.cx.tcx).ty;
                let ty = self.monomorphize(ty);
                self.cx.call_stack.borrow_mut().push(UseSite {
                    instance: self.param_env.and(self.instance),
                    kind: UseSiteKind::Drop {
                        drop_span: span,
                        place_span: self.body.local_decls[place.local].source_info.span,
                    },
                });
                let result = self.cx.drop_check(self.param_env.and(ty));
                self.cx.call_stack.borrow_mut().pop();
                result?
            }
            mir::TerminatorKind::InlineAsm { ref operands, .. } => {
                for op in operands {
                    match *op {
                        mir::InlineAsmOperand::SymFn { ref value } => {
                            let fn_ty = self.monomorphize(value.literal.ty());
                            if let ty::FnDef(def_id, substs) = *fn_ty.kind() {
                                let instance = ty::Instance::resolve(
                                    self.cx.tcx,
                                    self.param_env,
                                    def_id,
                                    substs,
                                )
                                .unwrap()
                                .ok_or(Error::TooGeneric)?;
                                self.check_fn_pointer_cast(instance, span)?;
                            }
                        }
                        mir::InlineAsmOperand::SymStatic { def_id } => {
                            self.check_static(def_id)?;
                        }
                        _ => {}
                    }
                }
            }
            mir::TerminatorKind::Assert { .. }
            | mir::TerminatorKind::Terminate { .. }
            | mir::TerminatorKind::Goto { .. }
            | mir::TerminatorKind::SwitchInt { .. }
            | mir::TerminatorKind::Resume
            | mir::TerminatorKind::Return
            | mir::TerminatorKind::Unreachable => {}
            mir::TerminatorKind::GeneratorDrop
            | mir::TerminatorKind::Yield { .. }
            | mir::TerminatorKind::FalseEdge { .. }
            | mir::TerminatorKind::FalseUnwind { .. } => bug!(),
        }

        Ok(())
    }

    fn check_static(&mut self, def_id: DefId) -> Result<(), Error> {
        if !crate::monomorphize_collector::should_codegen_locally(
            self.cx.tcx,
            &Instance::mono(self.cx.tcx, def_id),
        ) {
            return Ok(());
        }

        let span = self.cx.def_span(def_id);
        if let Ok(alloc) = self.cx.eval_static_initializer(def_id) {
            for id in alloc.inner().provenance().provenances() {
                self.check_alloc(id, span)?;
            }
        }
        Ok(())
    }
}

impl<'mir, 'tcx, 'cx> MirVisitor<'tcx> for MirNeighborVisitor<'mir, 'tcx, 'cx> {
    fn visit_rvalue(&mut self, rvalue: &mir::Rvalue<'tcx>, location: Location) {
        if self.result.is_err() {
            return;
        }

        self.result = self.check_rvalue(rvalue, location);

        if self.result.is_err() {
            return;
        }

        self.super_rvalue(rvalue, location);
    }

    fn visit_constant(&mut self, constant: &mir::Constant<'tcx>, location: Location) {
        if self.result.is_err() {
            return;
        }

        let literal = self.monomorphize(constant.literal);
        let val = match literal {
            mir::ConstantKind::Val(val, _) => Ok(val),
            mir::ConstantKind::Ty(ct) => match ct.kind() {
                ty::ConstKind::Value(val) => Ok(self.cx.valtree_to_const_val((ct.ty(), val))),
                ty::ConstKind::Unevaluated(ct) => Err(ct.expand()),
                _ => return,
            },
            mir::ConstantKind::Unevaluated(uv, _) => Err(uv),
        };
        let val = match val {
            Ok(val) => val,
            Err(uv) => {
                let param_env = ty::ParamEnv::reveal_all();
                match self.cx.const_eval_resolve(param_env, uv, None) {
                    // The `monomorphize` call should have evaluated that constant already.
                    Ok(val) => val,
                    Err(ErrorHandled::Reported(_)) => return,
                    Err(ErrorHandled::TooGeneric) => {
                        self.result = Err(Error::TooGeneric);
                        return;
                    }
                }
            }
        };

        self.result = self.check_const(val, self.body.source_info(location).span);
    }

    fn visit_terminator(&mut self, terminator: &mir::Terminator<'tcx>, location: Location) {
        if self.result.is_err() {
            return;
        }

        self.result = self.check_terminator(terminator, location);

        if self.result.is_err() {
            return;
        }

        self.super_terminator(terminator, location);
    }

    fn visit_local(
        &mut self,
        _place_local: mir::Local,
        _context: mir::visit::PlaceContext,
        _location: Location,
    ) {
    }
}

impl<'tcx> AnalysisCtxt<'tcx> {
    pub fn do_indirect_check(
        &self,
        param_env: ParamEnv<'tcx>,
        instance: Instance<'tcx>,
        body: &Body<'tcx>,
    ) -> Result<(), Error> {
        let mut visitor = MirNeighborVisitor {
            cx: self,
            param_env,
            instance,
            body,
            result: Ok(()),
        };
        visitor.visit_body(&body);
        visitor.result
    }

    pub fn indirect_check(
        &self,
        param_env: ParamEnv<'tcx>,
        instance: Instance<'tcx>,
        body: &Body<'tcx>,
    ) -> Result<(), Error> {
        if !self
            .recursion_limit()
            .value_within_limit(self.call_stack.borrow().len())
        {
            self.emit_with_use_site_info(self.sess.struct_fatal(format!(
                "reached the recursion limit while checking indirect calls for `{}`",
                PolyDisplay(&param_env.and(instance))
            )));
        }

        rustc_data_structures::stack::ensure_sufficient_stack(|| {
            self.do_indirect_check(param_env, instance, body)
        })
    }
}

memoize!(
    // Make this a query so that the same function is only reported once even if converted to pointers
    // in multiple sites.
    #[instrument(skip(cx), fields(poly_instance = %PolyDisplay(&poly_instance)), ret)]
    fn function_pointer_cast_check_indirect<'tcx>(
        cx: &AnalysisCtxt<'tcx>,
        poly_instance: ParamEnvAnd<'tcx, Instance<'tcx>>,
    ) -> Result<(), Error> {
        cx.instance_check(poly_instance)?;

        let adj = cx.instance_adjustment(poly_instance)?;
        let exp = cx.instance_expectation(poly_instance)?;

        if adj != crate::atomic_context::INDIRECT_DEFAULT.0
            || !exp.contains_range(crate::atomic_context::INDIRECT_DEFAULT.1)
        {
            let mut diag = cx.sess.struct_warn(
                "converting this function to pointer may result in preemption count rule violation",
            );
            diag.help(format!(
                "`{}` is being converted to a pointer",
                PolyDisplay(&poly_instance)
            ));
            diag.help(format!(
                "adjustment of this function is inferred to be {} and expectation is inferred to be {}",
                adj, exp
            ));
            diag.help(format!(
                "while the adjustment for function pointers is assumed to be {} and the expectation be {}",
                crate::atomic_context::INDIRECT_DEFAULT.0,
                crate::atomic_context::INDIRECT_DEFAULT.1
            ));
            cx.emit_with_use_site_info(diag);
        }

        Ok(())
    }
);

memoize!(
    // Make this a query so that the same function is only reported once even if converted to pointers
    // in multiple sites.
    #[instrument(
        skip(cx, poly_ty_trait_ref),
        fields(
            poly_ty = %PolyDisplay(&poly_ty_trait_ref.param_env.and(poly_ty_trait_ref.value.0)),
            trait_ref = ?poly_ty_trait_ref.value.1
        ),
        ret
    )]
    fn vtable_construction_check_indirect<'tcx>(
        cx: &AnalysisCtxt<'tcx>,
        poly_ty_trait_ref: ParamEnvAnd<'tcx, (Ty<'tcx>, Option<ty::PolyExistentialTraitRef<'tcx>>)>,
    ) -> Result<(), Error> {
        let (param_env, (ty, trait_ref)) = poly_ty_trait_ref.into_parts();

        let mut diag = None;
        if let Some(principal) = trait_ref {
            let poly_trait_ref = principal.with_self_ty(cx.tcx, ty);
            assert!(!poly_trait_ref.has_escaping_bound_vars());

            let mut visited = PredicateSet::new(cx.tcx);
            let predicate = poly_trait_ref.without_const().to_predicate(cx.tcx);
            let mut stack: Vec<ty::PolyTraitRef<'tcx>> = vec![poly_trait_ref];
            visited.insert(predicate);

            while let Some(trait_ref) = stack.pop() {
                let super_traits = cx
                    .super_predicates_of(trait_ref.def_id())
                    .predicates
                    .into_iter()
                    .filter_map(|(pred, _)| {
                        pred.subst_supertrait(cx.tcx, &trait_ref).as_trait_clause()
                    });
                for supertrait in super_traits {
                    if visited.insert(supertrait.to_predicate(cx.tcx)) {
                        let supertrait = supertrait.map_bound(|t| t.trait_ref);
                        stack.push(supertrait);
                    }
                }

                for &entry in cx.own_existential_vtable_entries(trait_ref.def_id()) {
                    let substs = trait_ref.map_bound(|trait_ref| {
                        InternalSubsts::for_item(cx.tcx, entry, |param, _| match param.kind {
                            GenericParamDefKind::Lifetime => cx.tcx.lifetimes.re_erased.into(),
                            GenericParamDefKind::Type { .. }
                            | GenericParamDefKind::Const { .. } => {
                                trait_ref.substs[param.index as usize]
                            }
                        })
                    });
                    let substs = cx.normalize_erasing_late_bound_regions(param_env, substs);

                    let predicates = cx.predicates_of(entry).instantiate_own(cx.tcx, substs);
                    if rustc_trait_selection::traits::impossible_predicates(
                        cx.tcx,
                        predicates.map(|(predicate, _)| predicate).collect(),
                    ) {
                        continue;
                    }

                    let instance = ty::Instance::resolve(cx.tcx, param_env, entry, substs)
                        .unwrap()
                        .ok_or(Error::TooGeneric)?;
                    let poly_instance = param_env.and(instance);
                    cx.instance_check(poly_instance)?;

                    // Find the `DefId` of the trait method.
                    let trait_item = if let Some(impl_) = cx.impl_of_method(instance.def_id()) {
                        cx.associated_items(impl_)
                            .in_definition_order()
                            .find(|x| x.def_id == instance.def_id())
                            .unwrap()
                            .trait_item_def_id
                            .unwrap()
                    } else {
                        // `impl_of_method` returns `None` if this instance is from the default impl of a trait method.
                        instance.def_id()
                    };

                    let expected_adjustment = cx
                        .preemption_count_annotation(trait_item)
                        .adjustment
                        .unwrap_or(crate::atomic_context::VCALL_DEFAULT.0);
                    let expected_expectation = cx
                        .preemption_count_annotation(trait_item)
                        .expectation
                        .unwrap_or(crate::atomic_context::VCALL_DEFAULT.1);

                    let adj = cx.instance_adjustment(poly_instance)?;
                    let exp = cx.instance_expectation(poly_instance)?;

                    if adj != expected_adjustment || !exp.contains_range(expected_expectation) {
                        let diag = diag.get_or_insert_with(|| {
                            cx
                                .sess
                                .struct_warn("constructing this vtable may result in preemption count rule violation")
                        });
                        diag.help(format!(
                            "`{}` is constructed as part of `dyn {}`",
                            PolyDisplay(&poly_instance),
                            cx.def_path_str(principal.def_id())
                        ));
                        diag.help(format!(
                            "adjustment is inferred to be {} and expectation is inferred to be {}",
                            adj, exp
                        ));
                        diag.help(format!(
                            "while the expected adjustment for vtable is {} and the expectation is {}",
                            expected_adjustment, expected_expectation
                        ));
                    }
                }
            }
        }

        // Check destructor
        let poly_ty = param_env.and(ty);

        let drop_annotation = trait_ref
            .map(|x| cx.drop_preemption_count_annotation(x.def_id()))
            .unwrap_or_default();
        let expected_adjustment = drop_annotation
            .adjustment
            .unwrap_or(crate::atomic_context::VDROP_DEFAULT.0);
        let expected_expectation = drop_annotation
            .expectation
            .unwrap_or(crate::atomic_context::VDROP_DEFAULT.1);

        let adj = cx.drop_adjustment(poly_ty)?;
        let exp = cx.drop_expectation(poly_ty)?;
        if adj != expected_adjustment || !exp.contains_range(expected_expectation) {
            let diag = diag.get_or_insert_with(|| {
                cx.sess.struct_warn(
                    "constructing this vtable may result in preemption count rule violation",
                )
            });
            diag.help(format!(
                "drop glue of `{}` is constructed as part of `dyn {}`",
                PolyDisplay(&poly_ty),
                trait_ref
                    .map(|x| cx.def_path_str(x.def_id()))
                    .unwrap_or_default()
            ));
            diag.help(format!(
                "adjustment is inferred to be {} and expectation is inferred to be {}",
                adj, exp
            ));
            diag.help(format!(
                "while the expected adjustment for vtable is {} and the expectation is {}",
                expected_adjustment, expected_expectation
            ));
        }

        if let Some(diag) = diag {
            cx.emit_with_use_site_info(diag);
        }

        Ok(())
    }
);

memoize!(
    #[instrument(skip(cx), fields(poly_ty = %PolyDisplay(&poly_ty)), ret)]
    fn drop_check<'tcx>(
        cx: &AnalysisCtxt<'tcx>,
        poly_ty: ParamEnvAnd<'tcx, Ty<'tcx>>,
    ) -> Result<(), Error> {
        cx.drop_adjustment_check(poly_ty)?;
        cx.drop_expectation_check(poly_ty)?;

        let (param_env, ty) = poly_ty.into_parts();

        // If the type doesn't need drop, then it trivially refers to nothing.
        if !ty.needs_drop(cx.tcx, param_env) {
            return Ok(());
        }

        match ty.kind() {
            ty::Closure(_, substs) => {
                return cx.drop_check(param_env.and(substs.as_closure().tupled_upvars_ty()));
            }

            // Generator drops are non-trivial, use the generated drop shims instead.
            ty::Generator(..) => (),

            ty::Tuple(list) => {
                for ty in list.iter() {
                    cx.drop_check(param_env.and(ty))?;
                }
                return Ok(());
            }

            ty::Adt(def, substs) if def.is_box() => {
                cx.drop_check(param_env.and(substs.type_at(0)))?;
                let drop_trait = cx.require_lang_item(LangItem::Drop, None);
                let drop_fn = cx.associated_item_def_ids(drop_trait)[0];
                let box_free =
                    ty::Instance::resolve(cx.tcx, param_env, drop_fn, cx.mk_substs(&[ty.into()]))
                        .unwrap()
                        .unwrap();
                cx.instance_check(param_env.and(box_free))?;
                return Ok(());
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
                    match cx.drop_check(poly_poly_ty) {
                        Err(Error::TooGeneric) => (),
                        v => return v,
                    }
                }

                // If that fails, we try to use the substs.
                // Fallthrough to the MIR drop shim based logic.
            }

            ty::Dynamic(..) => return Ok(()),

            // Array and slice drops only refer to respective element destructor.
            ty::Array(elem_ty, _) | ty::Slice(elem_ty) => {
                return cx.drop_check(param_env.and(*elem_ty));
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
            return Ok(());
        }

        let mir = crate::mir::drop_shim::build_drop_shim(cx, instance.def_id(), param_env, ty);
        let result = cx.indirect_check(param_env, instance, &mir);

        result
    }
);

memoize!(
    #[instrument(skip(cx), fields(poly_instance = %PolyDisplay(&poly_instance)), ret)]
    pub fn instance_check<'tcx>(
        cx: &AnalysisCtxt<'tcx>,
        poly_instance: ParamEnvAnd<'tcx, Instance<'tcx>>,
    ) -> Result<(), Error> {
        let (param_env, instance) = poly_instance.into_parts();
        if !crate::monomorphize_collector::should_codegen_locally(cx.tcx, &instance) {
            return Ok(());
        }

        cx.instance_adjustment_check(poly_instance)?;
        cx.instance_expectation_check(poly_instance)?;

        match instance.def {
            // Rust built-in intrinsics does not refer to anything else.
            ty::InstanceDef::Intrinsic(_) => return Ok(()),
            // Empty drop glue, then it is a no-op.
            ty::InstanceDef::DropGlue(_, None) => return Ok(()),
            ty::InstanceDef::DropGlue(_, Some(ty)) => return cx.drop_check(param_env.and(ty)),
            // Can't check further here. Will be checked at vtable generation site.
            ty::InstanceDef::Virtual(_, _) => return Ok(()),
            _ => (),
        }

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
                match cx.instance_check(poly_poly_instance) {
                    Err(Error::TooGeneric) => (),
                    expectation => return expectation,
                }
            }
        }

        // Foreign functions will not directly refer to Rust items
        if cx.is_foreign_item(instance.def_id()) {
            return Ok(());
        }

        if cx
            .call_stack
            .borrow()
            .iter()
            .rev()
            .any(|x| x.instance == poly_instance)
        {
            // Recursion encountered.
            return Ok(());
        }

        let mir = cx.analysis_instance_mir(instance.def);
        let result = cx.indirect_check(param_env, instance, mir);

        result
    }
);
