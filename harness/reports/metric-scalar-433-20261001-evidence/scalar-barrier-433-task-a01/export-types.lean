import Poincare.Global.ScalarCurvatureBarrier
import Lean
set_option pp.fullNames true
set_option pp.funBinderTypes true
set_option pp.piBinderTypes true
set_option pp.universes true
set_option pp.numericTypes true
set_option pp.coercions true
open Lean Elab Command Meta in
run_cmd liftTermElabM do
  for name in #[``Poincare.hasDerivWithinAt_neg_inv, ``Poincare.negative_reciprocal_growth_bound, ``Poincare.riccati_monotoneOn, ``Poincare.negative_reciprocal_initial_bound, ``Poincare.lower_bound_of_negative_reciprocal_bound, ``Poincare.riccati_lower_barrier_of_negative, ``Poincare.riccati_lower_barrier, ``Poincare.three_dimensional_scalar_curvature_lower_barrier_of_negative, ``Poincare.three_dimensional_scalar_curvature_lower_barrier, ``Poincare.segmented_negative_reciprocal_growth_bound, ``Poincare.segmented_riccati_lower_barrier_of_negative, ``Poincare.three_dimensional_scalar_curvature_segmented_lower_barrier_of_negative, ``Poincare.segmented_riccati_pointwise_lower_barrier_of_negative, ``Poincare.segmented_riccati_pointwise_lower_barrier, ``Poincare.three_dimensional_scalar_curvature_segmented_pointwise_lower_barrier_of_negative, ``Poincare.three_dimensional_scalar_curvature_segmented_pointwise_lower_barrier] do
    let info ← getConstInfo name
    let t ← ppExpr info.type
    let item := Json.mkObj [("name",toJson name.toString),("universes",toJson (info.levelParams.map Name.toString)),("lean_type",toJson (t.pretty 10000))]
    logInfo m!"DECL_JSON:{item.compress}"
