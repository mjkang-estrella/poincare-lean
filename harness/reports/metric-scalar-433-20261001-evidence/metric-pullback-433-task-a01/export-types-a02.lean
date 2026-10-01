import Poincare.Global.SmoothInitialMetricLocalPullback
import Lean
set_option pp.fullNames true
set_option pp.funBinderTypes true
set_option pp.piBinderTypes true
set_option pp.universes true
set_option pp.numericTypes true
set_option pp.coercions true
open Lean Elab Command Meta in
run_cmd liftTermElabM do
  for name in #[``Poincare.SmoothInitialMetricLocalPullback.localEuclideanInner_symm, ``Poincare.SmoothInitialMetricLocalPullback.localEuclideanInner_pos, ``Poincare.SmoothInitialMetricLocalPullback.localEuclideanInner_coordinates, ``Poincare.SmoothInitialMetricLocalPullback.localEuclideanInner_contMDiffOn] do
    let info ← getConstInfo name
    let t ← ppExpr info.type
    let item := Json.mkObj [("name",toJson name.toString),("universes",toJson (info.levelParams.map Name.toString)),("lean_type",toJson (t.pretty 10000))]
    logInfo m!"DECL_JSON:{item.compress}"
