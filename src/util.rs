use rustc_hir::def_id::DefId;
use rustc_lint::LateContext;
use rustc_middle::ty::TypeVisitableExt;

pub fn fn_has_unsatisfiable_preds(cx: &LateContext<'_>, did: DefId) -> bool {
    use rustc_trait_selection::traits;
    let predicates = cx
        .tcx
        .predicates_of(did)
        .predicates
        .iter()
        .filter_map(|(p, _)| if p.is_global() { Some(*p) } else { None });
    traits::impossible_predicates(
        cx.tcx,
        traits::elaborate(cx.tcx, predicates).collect::<Vec<_>>(),
    )
}
