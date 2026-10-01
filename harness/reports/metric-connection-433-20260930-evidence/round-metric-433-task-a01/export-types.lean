import Poincare.Global.RoundSphereMetric
import Lean
set_option pp.fullNames true
set_option pp.funBinderTypes true
set_option pp.piBinderTypes true
set_option pp.universes true
set_option pp.numericTypes true
set_option pp.coercions true
open Lean Elab Command Meta in
run_cmd liftTermElabM do
  for name in #[``Poincare.RoundSphere3, ``Poincare.RoundSphereAmbient4, ``Poincare.RoundSphereModel3, ``Poincare.roundSphereMetric3_inclusionDeriv, ``Poincare.roundSphereMetric3_inner, ``Poincare.roundSphereMetric3_inner_apply, ``Poincare.roundSphereMetric3_inner_mfderiv_eq, ``Poincare.roundSphereMetric3_inner_symm, ``Poincare.roundSphereMetric3_inner_pos, ``Poincare.roundSphereMetric3_inner_isVonNBounded, ``Poincare.roundSphereMetric3_modelInner, ``Poincare.roundSphereMetric3_modelInner_eq, ``Poincare.roundSphereMetric3_modelInner_contDiff, ``Poincare.roundSphereMetric3_inner_contMDiff, ``Poincare.roundSphereMetric3, ``Poincare.roundSphereMetric3_inner_eq] do
    let info ← getConstInfo name
    let t ← ppExpr info.type
    let item := Json.mkObj [("name",toJson name.toString),("universes",toJson (info.levelParams.map Name.toString)),("lean_type",toJson (t.pretty 10000))]
    logInfo m!"DECL_JSON:{item.compress}"
