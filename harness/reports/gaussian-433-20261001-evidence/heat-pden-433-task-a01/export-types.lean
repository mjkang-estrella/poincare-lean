import Poincare.Global.HeatKernelPDEn
import Lean
set_option pp.fullNames true
set_option pp.funBinderTypes true
set_option pp.piBinderTypes true
set_option pp.universes true
set_option pp.numericTypes true
set_option pp.coercions true
open Lean Elab Command Meta in
run_cmd liftTermElabM do
  for name in #[``Poincare.keeps, ``Poincare.hasFDerivAt_neg_norm_sq_div, ``Poincare.hasFDerivAt_exp_neg_norm_sq_div, ``Poincare.iteratedFDeriv_two_exp_neg_norm_sq_div_apply, ``Poincare.sum_sq_inner_stdOrthonormalBasis, ``Poincare.laplacian_exp_neg_norm_sq_div, ``Poincare.heatKernel_heatEquation_laplacian] do
    let info ← getConstInfo name
    let t ← ppExpr info.type
    let item := Json.mkObj [("name",toJson name.toString),("universes",toJson (info.levelParams.map Name.toString)),("lean_type",toJson (t.pretty 10000))]
    logInfo m!"DECL_JSON:{item.compress}"
