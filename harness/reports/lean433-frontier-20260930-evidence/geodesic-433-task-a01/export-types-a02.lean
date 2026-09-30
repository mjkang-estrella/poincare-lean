import Poincare.Global.GeodesicChart
import Lean
set_option pp.fullNames true
set_option pp.funBinderTypes true
set_option pp.piBinderTypes true
set_option pp.universes true
set_option pp.numericTypes true
set_option pp.coercions true
open Lean Elab Command Meta in
run_cmd liftTermElabM do
  for name in #[``Poincare.geodesicFlowField, ``Poincare.geodesicFlowField_apply, ``Poincare.contDiffAt_geodesicFlowField, ``Poincare.contDiff_geodesicFlowField, ``Poincare.exists_geodesicFlowField_solution_of_contDiffAt, ``Poincare.exists_geodesicFlowField_solution, ``Poincare.exists_geodesicFlowField_solution_of_contDiff, ``Poincare.geodesicFlowField_eventuallyEq_of_lipschitz, ``Poincare.geodesicFlowField_eventuallyEq_of_contDiffAt, ``Poincare.geodesic_position_hasDerivAt, ``Poincare.geodesic_velocity_hasDerivAt, ``Poincare.geodesic_components_hasDerivAt] do
    let info ← getConstInfo name
    let t ← ppExpr info.type
    let item := Json.mkObj [("name",toJson name.toString),("universes",toJson (info.levelParams.map Name.toString)),("lean_type",toJson (t.pretty 10000))]
    logInfo m!"DECL_JSON:{item.compress}"
