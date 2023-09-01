// From rustc_mir_transform/src/shim.rs
// Adopted to support polymorphic drop shims

use rustc_hir::def_id::DefId;
use rustc_index::{Idx, IndexVec};
use rustc_middle::mir::patch::MirPatch;
use rustc_middle::mir::*;
use rustc_middle::ty::{self, EarlyBinder, ParamEnv, Ty, TyCtxt};
use rustc_mir_dataflow::elaborate_drops::{self, *};
use rustc_span::Span;
use rustc_target::abi::{FieldIdx, VariantIdx};
use std::{fmt, iter};

use crate::ctxt::AnalysisCtxt;

fn local_decls_for_sig<'tcx>(
    sig: &ty::FnSig<'tcx>,
    span: Span,
) -> IndexVec<Local, LocalDecl<'tcx>> {
    iter::once(LocalDecl::new(sig.output(), span))
        .chain(
            sig.inputs()
                .iter()
                .map(|ity| LocalDecl::new(*ity, span).immutable()),
        )
        .collect()
}

#[instrument(skip(cx))]
pub fn build_drop_shim<'tcx>(
    cx: &AnalysisCtxt<'tcx>,
    def_id: DefId,
    param_env: ParamEnv<'tcx>,
    ty: Ty<'tcx>,
) -> Body<'tcx> {
    if let ty::Generator(gen_def_id, substs, _) = ty.kind() {
        let body = cx.analysis_mir(*gen_def_id).generator_drop().unwrap();
        let body = EarlyBinder::bind(body.clone()).subst(cx.tcx, substs);
        return body;
    }

    let substs = cx.mk_substs(&[ty.into()]);
    let sig = cx.fn_sig(def_id).subst(cx.tcx, substs);
    let sig = cx.erase_late_bound_regions(sig);
    let span = cx.def_span(def_id);

    let source_info = SourceInfo::outermost(span);

    let return_block = BasicBlock::new(1);
    let mut blocks = IndexVec::with_capacity(2);
    let block = |blocks: &mut IndexVec<_, _>, kind| {
        blocks.push(BasicBlockData {
            statements: vec![],
            terminator: Some(Terminator { source_info, kind }),
            is_cleanup: false,
        })
    };
    block(
        &mut blocks,
        TerminatorKind::Goto {
            target: return_block,
        },
    );
    block(&mut blocks, TerminatorKind::Return);

    let source = MirSource::from_instance(ty::InstanceDef::DropGlue(def_id, Some(ty)));
    let mut body = new_body(
        source,
        blocks,
        local_decls_for_sig(&sig, span),
        sig.inputs().len(),
        span,
    );

    // The first argument (index 0), but add 1 for the return value.
    let dropee_ptr = Place::from(Local::new(1 + 0));
    let patch = {
        let mut elaborator = DropShimElaborator {
            body: &body,
            patch: MirPatch::new(&body),
            tcx: cx.tcx,
            param_env,
        };
        let dropee = cx.mk_place_deref(dropee_ptr);
        let resume_block = elaborator.patch.resume_block();
        elaborate_drops::elaborate_drop(
            &mut elaborator,
            source_info,
            dropee,
            (),
            return_block,
            elaborate_drops::Unwind::To(resume_block),
            START_BLOCK,
        );
        elaborator.patch
    };
    patch.apply(&mut body);
    body
}

fn new_body<'tcx>(
    source: MirSource<'tcx>,
    basic_blocks: IndexVec<BasicBlock, BasicBlockData<'tcx>>,
    local_decls: IndexVec<Local, LocalDecl<'tcx>>,
    arg_count: usize,
    span: Span,
) -> Body<'tcx> {
    Body::new(
        source,
        basic_blocks,
        IndexVec::from_elem_n(
            SourceScopeData {
                span,
                parent_scope: None,
                inlined: None,
                inlined_parent_scope: None,
                local_data: ClearCrossCrate::Clear,
            },
            1,
        ),
        local_decls,
        IndexVec::new(),
        arg_count,
        vec![],
        span,
        None,
        // FIXME(compiler-errors): is this correct?
        None,
    )
}

pub struct DropShimElaborator<'a, 'tcx> {
    pub body: &'a Body<'tcx>,
    pub patch: MirPatch<'tcx>,
    pub tcx: TyCtxt<'tcx>,
    pub param_env: ty::ParamEnv<'tcx>,
}

impl fmt::Debug for DropShimElaborator<'_, '_> {
    fn fmt(&self, _f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        Ok(())
    }
}

impl<'a, 'tcx> DropElaborator<'a, 'tcx> for DropShimElaborator<'a, 'tcx> {
    type Path = ();

    fn patch(&mut self) -> &mut MirPatch<'tcx> {
        &mut self.patch
    }
    fn body(&self) -> &'a Body<'tcx> {
        self.body
    }
    fn tcx(&self) -> TyCtxt<'tcx> {
        self.tcx
    }
    fn param_env(&self) -> ty::ParamEnv<'tcx> {
        self.param_env
    }

    fn drop_style(&self, _path: Self::Path, mode: DropFlagMode) -> DropStyle {
        match mode {
            DropFlagMode::Shallow => {
                // Drops for the contained fields are "shallow" and "static" - they will simply call
                // the field's own drop glue.
                DropStyle::Static
            }
            DropFlagMode::Deep => {
                // The top-level drop is "deep" and "open" - it will be elaborated to a drop ladder
                // dropping each field contained in the value.
                DropStyle::Open
            }
        }
    }

    fn get_drop_flag(&mut self, _path: Self::Path) -> Option<Operand<'tcx>> {
        None
    }

    fn clear_drop_flag(&mut self, _location: Location, _path: Self::Path, _mode: DropFlagMode) {}

    fn field_subpath(&self, _path: Self::Path, _field: FieldIdx) -> Option<Self::Path> {
        None
    }
    fn deref_subpath(&self, _path: Self::Path) -> Option<Self::Path> {
        None
    }
    fn downcast_subpath(&self, _path: Self::Path, _variant: VariantIdx) -> Option<Self::Path> {
        Some(())
    }
    fn array_subpath(&self, _path: Self::Path, _index: u64, _size: u64) -> Option<Self::Path> {
        None
    }
}
