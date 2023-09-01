use rustc_hir::def::DefKind;
use rustc_hir::def_id::{CrateNum, DefId, DefIndex};
use rustc_hir::definitions::DefPathData;
use rustc_span::sym;

use crate::attribute::PreemptionCount;
use crate::ctxt::AnalysisCtxt;

impl<'tcx> AnalysisCtxt<'tcx> {
    fn preemption_count_annotation_fallback(&self, def_id: DefId) -> PreemptionCount {
        match self.crate_name(def_id.krate).as_str() {
            // Happens in a test environment where build-std is not enabled.
            "core" | "alloc" | "std" => (),
            _ => {
                warn!(
                    "Unable to retrieve preemption count annotation of non-local function {:?}",
                    def_id
                );
            }
        }
        Default::default()
    }

    fn core_out_of_band_annotation(&self, def_id: DefId) -> PreemptionCount {
        if self.def_kind(def_id) == DefKind::AssocFn &&
            let Some(impl_) = self.impl_of_method(def_id)
        {
            let self_ty = self.type_of(impl_);
            let Some(fn_name) = self.def_path(def_id).data.last().copied() else {
                return Default::default();
            };
            let DefPathData::ValueNs(fn_name) = fn_name.data else {
                return Default::default();
            };

            if let Some(adt_def) = self_ty.skip_binder().ty_adt_def() &&
                let data = self.def_path(adt_def.did()).data &&
                data.len() == 3 &&
                let DefPathData::TypeNs(task) = data[0].data &&
                task == *crate::symbol::task &&
                let DefPathData::TypeNs(wake) = data[1].data &&
                wake == *crate::symbol::wake &&
                let DefPathData::TypeNs(waker) = data[2].data &&
                waker == *crate::symbol::Waker
            {
                if fn_name == sym::clone
                    || fn_name == *crate::symbol::wake
                    || fn_name == *crate::symbol::wake_by_ref
                {
                    return PreemptionCount {
                        adjustment: Some(0),
                        expectation: Some(super::ExpectationRange::top()),
                        unchecked: true,
                    };
                }
            }

            return Default::default();
        }

        let data = self.def_path(def_id).data;

        if data.len() == 3 &&
            let DefPathData::TypeNs(any) = data[0].data &&
            any == sym::any &&
            let DefPathData::TypeNs(any_trait) = data[1].data &&
            any_trait == sym::Any &&
            let DefPathData::ValueNs(_any_fn) = data[2].data
        {
            // This is a `core::any::Any::_` function.
            return PreemptionCount {
                adjustment: Some(0),
                expectation: Some(super::ExpectationRange::top()),
                unchecked: false,
            };
        }

        if data.len() == 3 &&
            let DefPathData::TypeNs(error) = data[0].data &&
            error == *crate::symbol::error &&
            let DefPathData::TypeNs(error_trait) = data[1].data &&
            error_trait == sym::Error &&
            let DefPathData::ValueNs(_any_fn) = data[2].data
        {
            // This is a `core::error::Error::_` function.
            return PreemptionCount {
                adjustment: Some(0),
                expectation: Some(super::ExpectationRange::top()),
                unchecked: false,
            };
        }

        if data.len() == 3 &&
            let DefPathData::TypeNs(fmt) = data[0].data &&
            fmt == sym::fmt &&
            let DefPathData::TypeNs(_fmt_trait) = data[1].data &&
            let DefPathData::ValueNs(fmt_fn) = data[2].data &&
            fmt_fn == sym::fmt
        {
            // This is a `core::fmt::Trait::fmt` function.
            return PreemptionCount {
                adjustment: Some(0),
                expectation: Some(super::ExpectationRange::top()),
                unchecked: false,
            };
        }
        if data.len() == 3 &&
            let DefPathData::TypeNs(fmt) = data[0].data &&
            fmt == sym::fmt &&
            let DefPathData::TypeNs(write) = data[1].data &&
            write == *crate::symbol::Write &&
            let DefPathData::ValueNs(_write_fn) = data[2].data
        {
            // This is a `core::fmt::Write::write_{str, char, fmt}` function.
            return PreemptionCount {
                adjustment: Some(0),
                expectation: Some(super::ExpectationRange::top()),
                unchecked: false,
            };
        }
        if data.len() == 2 &&
            let DefPathData::TypeNs(fmt) = data[0].data &&
            fmt == sym::fmt &&
            let DefPathData::ValueNs(write) = data[1].data &&
            write == *crate::symbol::write
        {
            // This is `core::fmt::write` function, which uses function pointers internally.
            return PreemptionCount {
                adjustment: Some(0),
                expectation: Some(super::ExpectationRange::top()),
                unchecked: true,
            };
        }

        Default::default()
    }
}

memoize!(
    pub fn preemption_count_annotation<'tcx>(
        cx: &AnalysisCtxt<'tcx>,
        def_id: DefId,
    ) -> PreemptionCount {
        if cx.crate_name(def_id.krate) == sym::core {
            return cx.core_out_of_band_annotation(def_id);
        }

        let Some(local_def_id) = def_id.as_local() else {
            if let Some(v) = cx.sql_load::<preemption_count_annotation>(def_id) {
                return v;
            }
            return cx.preemption_count_annotation_fallback(def_id);
        };

        let hir_id = cx.hir().local_def_id_to_hir_id(local_def_id);
        for attr in cx.redpen_attributes(hir_id).iter() {
            match attr {
                crate::attribute::RedpenAttribute::PreemptionCount(pc) => {
                    return *pc;
                }
                _ => (),
            }
        }

        Default::default()
    }
);

impl crate::ctxt::PersistentQuery for preemption_count_annotation {
    type LocalKey<'tcx> = DefIndex;

    fn into_crate_and_local<'tcx>(key: Self::Key<'tcx>) -> (CrateNum, Self::LocalKey<'tcx>) {
        (key.krate, key.index)
    }
}

memoize!(
    pub fn drop_preemption_count_annotation<'tcx>(
        cx: &AnalysisCtxt<'tcx>,
        def_id: DefId,
    ) -> PreemptionCount {
        let Some(local_def_id) = def_id.as_local() else {
            if let Some(v) = cx.sql_load::<drop_preemption_count_annotation>(def_id) {
                return v;
            }
            return cx.preemption_count_annotation_fallback(def_id);
        };

        let hir_id = cx.hir().local_def_id_to_hir_id(local_def_id);
        for attr in cx.redpen_attributes(hir_id).iter() {
            match attr {
                crate::attribute::RedpenAttribute::DropPreemptionCount(pc) => {
                    return *pc;
                }
                _ => (),
            }
        }

        Default::default()
    }
);

impl crate::ctxt::PersistentQuery for drop_preemption_count_annotation {
    type LocalKey<'tcx> = DefIndex;

    fn into_crate_and_local<'tcx>(key: Self::Key<'tcx>) -> (CrateNum, Self::LocalKey<'tcx>) {
        (key.krate, key.index)
    }
}

memoize!(
    pub fn should_report_preempt_count<'tcx>(cx: &AnalysisCtxt<'tcx>, def_id: DefId) -> bool {
        let Some(local_def_id) = def_id.as_local() else {
            return false;
        };

        let hir_id = cx.hir().local_def_id_to_hir_id(local_def_id);
        for attr in cx.redpen_attributes(hir_id).iter() {
            match attr {
                crate::attribute::RedpenAttribute::ReportPreeptionCount => return true,
                _ => (),
            }
        }

        false
    }
);

memoize!(
    pub fn should_dump_mir<'tcx>(cx: &AnalysisCtxt<'tcx>, def_id: DefId) -> bool {
        let Some(local_def_id) = def_id.as_local() else {
            return false;
        };

        let hir_id = cx.hir().local_def_id_to_hir_id(local_def_id);
        for attr in cx.redpen_attributes(hir_id).iter() {
            match attr {
                crate::attribute::RedpenAttribute::DumpMir => return true,
                _ => (),
            }
        }

        false
    }
);
