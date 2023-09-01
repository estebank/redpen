use std::collections::HashMap;

use rustc_hir as hir;
use rustc_lint::{LateContext, LateLintPass};
use rustc_middle::ty::{self, TyCtxt};
use rustc_session::{declare_tool_lint, impl_lint_pass};

pub struct Disallow<'tcx> {
    tcx: TyCtxt<'tcx>,
}

impl<'tcx> Disallow<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self { tcx }
    }
}

declare_tool_lint! {
    pub redpen::DISALLOW,
    Deny,
    "Reject specific instantiations of type parameter"
}

impl_lint_pass!(Disallow<'_> => [DISALLOW]);

impl<'tcx> LateLintPass<'tcx> for Disallow<'tcx> {
    /// Find all explicitly spelled out types and look for type parameter restrictions in them.
    fn check_path(
        &mut self,
        cx: &LateContext<'tcx>,
        path: &hir::Path<'tcx>,
        path_hir_id: hir::HirId,
    ) {
        for segment in path.segments {
            let hir::def::Res::Def(
                hir::def::DefKind::Struct
                | hir::def::DefKind::Enum
                | hir::def::DefKind::AssocTy
                | hir::def::DefKind::Union
                | hir::def::DefKind::TyAlias { .. },
                def_id,
            ) = segment.res
            else {
                continue;
            };
            let Some(did) = def_id.as_local() else {
                continue;
            };
            let Some(hir_id) = self.tcx.opt_local_def_id_to_hir_id(did) else {
                continue;
            };
            let Some(node) = self.tcx.hir().find(hir_id) else {
                return;
            };
            let Some(generics) = node.generics() else {
                return;
            };
            let generics: HashMap<String, usize> = generics
                .params
                .iter()
                .enumerate()
                .map(|(i, param)| (param.name.ident().to_string(), i))
                .collect();
            let Some(args) = segment.args else {
                return;
            };

            for attr in cx.tcx.hir().attrs(hir_id) {
                if let Some(crate::attribute::RedpenAttribute::Disallow(disallowed)) =
                    crate::attribute::parse_redpen_attribute(cx.tcx, hir_id, attr)
                {
                    for (param, types) in &disallowed {
                        let Some(&pos) = generics.get(param) else {
                            continue;
                        };
                        let Some(hir::GenericArg::Type(hir::Ty {
                            kind: hir::TyKind::Path(path),
                            ..
                        })) = args.args.get(pos)
                        else {
                            continue;
                        };
                        let hir::QPath::Resolved(None, path) = path else {
                            continue;
                        };
                        let hir::def::Res::Def(_, arg_def_id) = path.res else {
                            continue;
                        };
                        let name = self.tcx.def_path_str(arg_def_id).to_string();
                        if types.contains(&name) {
                            self.tcx.struct_span_lint_hir(
                                DISALLOW,
                                path_hir_id,
                                path.span,
                                format!(
                                    "type parameter `{param}` in `{}` can't be `{name}`",
                                    self.tcx.item_name(def_id).to_string(),
                                ),
                                |diag| diag,
                            );
                        }
                    }
                    continue;
                }
            }
        }
    }

    /// Look for every expression of a type that has parameter restrictions.
    fn check_expr(&mut self, cx: &LateContext<'tcx>, expr: &'tcx hir::Expr<'tcx>) {
        if let hir::ExprKind::Block(..) = expr.kind {
            // Avoid duplicated errors.
            return;
        }
        let Some(ty) = cx.typeck_results().expr_ty_adjusted_opt(expr) else {
            return;
        };
        let ty::Adt(def, ty_params) = ty.kind() else {
            return;
        };
        let def_id = def.did();
        let Some(did) = def_id.as_local() else {
            return;
        };
        let Some(hir_id) = self.tcx.opt_local_def_id_to_hir_id(did) else {
            return;
        };
        let Some(node) = self.tcx.hir().find(hir_id) else {
            return;
        };
        let Some(generics) = node.generics() else {
            return;
        };
        let generics: HashMap<String, usize> = generics
            .params
            .iter()
            .enumerate()
            .map(|(i, param)| (param.name.ident().to_string(), i))
            .collect();
        for attr in cx.tcx.hir().attrs(hir_id) {
            if let Some(crate::attribute::RedpenAttribute::Disallow(disallowed)) =
                crate::attribute::parse_redpen_attribute(cx.tcx, hir_id, attr)
            {
                for (param, types) in &disallowed {
                    let Some(&pos) = generics.get(param) else {
                        continue;
                    };
                    let Some(ty_param) = ty_params.get(pos) else {
                        continue;
                    };
                    if types.contains(&ty_param.to_string()) {
                        self.tcx.struct_span_lint_hir(
                            DISALLOW,
                            hir_id,
                            expr.span,
                            format!(
                                "type parameter `{param}` in `{}` can't be `{ty_param}`",
                                self.tcx.item_name(def_id)
                            ),
                            |diag| {
                                diag.span_label(
                                    expr.span,
                                    format!("this expression is of type `{ty}`"),
                                );
                                diag
                            },
                        );
                    }
                }
                continue;
            };
        }
    }
}
