use rustc_middle::mir::{BasicBlock, Body, TerminatorKind};
use rustc_middle::ty::{self, Instance, ParamEnv};
use rustc_mir_dataflow::JoinSemiLattice;
use rustc_mir_dataflow::{fmt::DebugWithContext, Analysis, AnalysisDomain};

use super::*;
use crate::ctxt::AnalysisCtxt;

/// Bounds of adjustments.
///
/// Note that the semilattice join operation is not a normal range join. If we encounter code like this
/// ```ignore
/// while foo() {
///    enter_atomic();
/// }
/// ```
/// then the bounds will be `0..inf`, and the dataflow analysis will never converge because we are changing
/// the upper bound one at a time.
///
/// To ensure convergence, we does not use `max(a.hi, b.hi)` when joining `a` and `b`. But instead,
/// if `a.hi` and `b.hi` are different but both positive, we immediately relax the bound to unbounded.
/// Similar relaxing is performed when `a.lo` and `b.lo` are different but both negative.
/// We still do normal max/min otherwise, e.g. joining `1..5` and `2..5` gives `1..5`, because usually
/// the preemption count adjustment is close to zero.
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct AdjustmentBounds {
    /// Lower bound of the adjustment, inclusive.
    pub lo: Option<i32>,
    /// Upper bound of the adjustment, exclusive.
    pub hi: Option<i32>,
}

impl AdjustmentBounds {
    pub fn is_empty(&self) -> bool {
        self.lo == Some(0) && self.hi == Some(0)
    }

    pub fn unbounded() -> Self {
        AdjustmentBounds { lo: None, hi: None }
    }

    pub fn offset(&self, offset: i32) -> Self {
        AdjustmentBounds {
            lo: self.lo.map(|x| x + offset),
            hi: self.hi.map(|x| x + offset),
        }
    }

    pub fn is_single_value(&self) -> Option<i32> {
        match *self {
            AdjustmentBounds {
                lo: Some(x),
                hi: Some(y),
            } if x + 1 == y => Some(x),
            _ => None,
        }
    }

    pub fn single_value(v: i32) -> Self {
        Self {
            lo: Some(v),
            hi: Some(v + 1),
        }
    }
}

impl Default for AdjustmentBounds {
    fn default() -> Self {
        Self {
            lo: Some(0),
            hi: Some(0),
        }
    }
}

impl std::fmt::Debug for AdjustmentBounds {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match (self.lo, self.hi) {
            (Some(x), Some(y)) if x + 1 == y => write!(f, "{}", x),
            (Some(x), Some(y)) => write!(f, "{}..{}", x, y),
            (Some(x), None) => write!(f, "{}..", x),
            (None, Some(y)) => write!(f, "..{}", y),
            (None, None) => write!(f, ".."),
        }
    }
}

impl JoinSemiLattice for AdjustmentBounds {
    fn join(&mut self, other: &Self) -> bool {
        if other.is_empty() {
            return false;
        }

        if self.is_empty() {
            *self = *other;
            return true;
        }

        let mut changed = false;
        match (self.lo, other.lo) {
            // Already unbounded, no change needed
            (None, _) => (),
            // Same bound, no change needed
            (Some(a), Some(b)) if a == b => (),
            // Both bounded, but with different bounds (and both negative). To ensure convergence, relax to unbounded.
            (Some(a), Some(b)) if a < 0 && b < 0 => {
                self.lo = None;
                changed = true;
            }
            // Already have lower bound
            (Some(a), Some(b)) if a < b => (),
            // Adjust bound
            _ => {
                self.lo = other.lo;
                changed = true;
            }
        }

        match (self.hi, other.hi) {
            // Already unbounded, no change needed
            (None, _) => (),
            // Same bound, no change needed
            (Some(a), Some(b)) if a == b => (),
            // Both bounded, but with different bounds (and both positive). To ensure convergence, relax to unbounded.
            (Some(a), Some(b)) if a > 0 && b > 0 => {
                self.hi = None;
                changed = true;
            }
            // Already have upper bound
            (Some(a), Some(b)) if a > b => (),
            // Adjust bound
            _ => {
                self.hi = other.hi;
                changed = true;
            }
        }
        changed
    }
}

/// Bounds of adjustments or error.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum AdjustmentBoundsOrError {
    Bounds(AdjustmentBounds),
    Error(Error),
}

impl AdjustmentBoundsOrError {
    #[track_caller]
    pub fn unwrap(self) -> AdjustmentBounds {
        match self {
            AdjustmentBoundsOrError::Bounds(b) => b,
            _ => unreachable!(),
        }
    }

    pub fn into_result(self) -> Result<AdjustmentBounds, Error> {
        match self {
            AdjustmentBoundsOrError::Bounds(b) => Ok(b),
            AdjustmentBoundsOrError::Error(e) => Err(e),
        }
    }
}

impl Default for AdjustmentBoundsOrError {
    fn default() -> Self {
        Self::Bounds(Default::default())
    }
}

impl JoinSemiLattice for AdjustmentBoundsOrError {
    fn join(&mut self, other: &Self) -> bool {
        match (self, other) {
            (AdjustmentBoundsOrError::Error(Error::Error(_)), _) => false,
            (this, AdjustmentBoundsOrError::Error(Error::Error(e))) => {
                *this = AdjustmentBoundsOrError::Error(Error::Error(*e));
                true
            }
            (AdjustmentBoundsOrError::Error(Error::TooGeneric), _) => false,
            (this, AdjustmentBoundsOrError::Error(Error::TooGeneric)) => {
                *this = AdjustmentBoundsOrError::Error(Error::TooGeneric);
                true
            }
            (AdjustmentBoundsOrError::Bounds(a), AdjustmentBoundsOrError::Bounds(b)) => a.join(b),
        }
    }
}

pub struct AdjustmentComputation<'mir, 'tcx, 'checker> {
    pub checker: &'checker AnalysisCtxt<'tcx>,
    pub body: &'mir Body<'tcx>,
    pub param_env: ParamEnv<'tcx>,
    pub instance: Instance<'tcx>,
}

impl DebugWithContext<AdjustmentComputation<'_, '_, '_>> for AdjustmentBoundsOrError {}

impl<'tcx> AnalysisDomain<'tcx> for AdjustmentComputation<'_, 'tcx, '_> {
    // The number here indicates the offset in relation to the function's entry point.
    type Domain = AdjustmentBoundsOrError;

    const NAME: &'static str = "atomic context";

    fn bottom_value(&self, _body: &Body<'tcx>) -> Self::Domain {
        Default::default()
    }

    fn initialize_start_block(&self, _body: &Body<'tcx>, state: &mut Self::Domain) {
        *state = AdjustmentBoundsOrError::Bounds(AdjustmentBounds {
            lo: Some(0),
            hi: Some(1),
        });
    }
}

impl<'tcx> Analysis<'tcx> for AdjustmentComputation<'_, 'tcx, '_> {
    fn apply_statement_effect(
        &mut self,
        _state: &mut Self::Domain,
        _statement: &rustc_middle::mir::Statement<'tcx>,
        _location: rustc_middle::mir::Location,
    ) {
    }

    fn apply_terminator_effect(
        &mut self,
        state: &mut Self::Domain,
        terminator: &rustc_middle::mir::Terminator<'tcx>,
        location: rustc_middle::mir::Location,
    ) {
        // Skip all unwinding paths.
        if self.body.basic_blocks[location.block].is_cleanup {
            return;
        }

        let AdjustmentBoundsOrError::Bounds(bounds) = state else {
            return;
        };

        let adjustment = match &terminator.kind {
            TerminatorKind::Call { func, .. } => {
                let callee_ty = func.ty(self.body, self.checker.tcx);
                let callee_ty = self.instance.subst_mir_and_normalize_erasing_regions(
                    self.checker.tcx,
                    self.param_env,
                    ty::EarlyBinder::bind(callee_ty),
                );
                if let ty::FnDef(def_id, substs) = *callee_ty.kind() {
                    if let Some(v) = self.checker.preemption_count_annotation(def_id).adjustment {
                        // Fast path, no need to resolve the instance.
                        // This also avoids `TooGeneric` when def_id is an trait method.
                        Ok(v)
                    } else {
                        match ty::Instance::resolve(
                            self.checker.tcx,
                            self.param_env,
                            def_id,
                            substs,
                        )
                        .unwrap()
                        {
                            Some(instance) => {
                                self.checker.call_stack.borrow_mut().push(UseSite {
                                    instance: self.param_env.and(self.instance),
                                    kind: UseSiteKind::Call(terminator.source_info.span),
                                });
                                let result = self
                                    .checker
                                    .instance_adjustment(self.param_env.and(instance));
                                self.checker.call_stack.borrow_mut().pop();
                                result
                            }
                            None => Err(Error::TooGeneric),
                        }
                    }
                } else {
                    Ok(crate::atomic_context::INDIRECT_DEFAULT.0)
                }
            }
            TerminatorKind::Drop { place, .. } => {
                let ty = place.ty(self.body, self.checker.tcx).ty;
                let ty = self.instance.subst_mir_and_normalize_erasing_regions(
                    self.checker.tcx,
                    self.param_env,
                    ty::EarlyBinder::bind(ty),
                );

                self.checker.call_stack.borrow_mut().push(UseSite {
                    instance: self.param_env.and(self.instance),
                    kind: UseSiteKind::Drop {
                        drop_span: terminator.source_info.span,
                        place_span: self.body.local_decls[place.local].source_info.span,
                    },
                });
                let result = self.checker.drop_adjustment(self.param_env.and(ty));
                self.checker.call_stack.borrow_mut().pop();
                result
            }
            _ => return,
        };

        let adjustment = match adjustment {
            Ok(v) => v,
            Err(e) => {
                // Too generic, need to bail out and retry after monomorphization.
                *state = AdjustmentBoundsOrError::Error(e);
                return;
            }
        };

        *bounds = bounds.offset(adjustment);
    }

    fn apply_call_return_effect(
        &mut self,
        _state: &mut Self::Domain,
        _block: BasicBlock,
        _return_places: rustc_mir_dataflow::CallReturnPlaces<'_, 'tcx>,
    ) {
    }
}
