import Poincare.Global.HeatKernelPDE
import Lean
set_option pp.fullNames true
set_option pp.funBinderTypes true
set_option pp.piBinderTypes true
set_option pp.universes true
set_option pp.numericTypes true
set_option pp.coercions true
open Lean Elab Command Meta in
run_cmd liftTermElabM do
  for name in #[``Poincare.hasDerivAt_heatKernel_time, ``Poincare.deriv_heatKernel_time, ``Poincare.heatKernelReal, ``Poincare.heatKernel_real_eq, ``Poincare.heatKernelReal_heatEquation, ``Poincare.heatKernel_real_heatEquation, ``Poincare.heatKernel_real_heatEquation_laplacian] do
    let info ← getConstInfo name
    let t ← ppExpr info.type
    let item := Json.mkObj [("name",toJson name.toString),("universes",toJson (info.levelParams.map Name.toString)),("lean_type",toJson (t.pretty 10000))]
    logInfo m!"DECL_JSON:{item.compress}"
