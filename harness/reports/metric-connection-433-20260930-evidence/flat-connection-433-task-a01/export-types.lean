import Poincare.FlatModelConnection
import Lean
set_option pp.fullNames true
set_option pp.funBinderTypes true
set_option pp.piBinderTypes true
set_option pp.universes true
set_option pp.numericTypes true
set_option pp.coercions true
open Lean Elab Command Meta in
run_cmd liftTermElabM do
  for name in #[``mdiffAt_vectorSpace_iff_differentiableAt, ``flatCovariantDerivative, ``flatCovariantDerivative_apply, ``mlieBracket_vectorSpace_eq, ``flatCovariantDerivative_curvatureOp_eq_zero, ``flatCovariantDerivative_torsion_eq_zero, ``flatCovariantDerivative_inner_compatible, ``flatCovariantDerivative_eq, ``mdiffAt_vectorSpace_iff_differentiableAt_eq, ``flatCovariantDerivative_apply_eq, ``flatCovariantDerivative_curvatureOp_eq_zero_eq, ``flatCovariantDerivative_torsion_eq_zero_eq, ``flatCovariantDerivative_inner_compatible_eq] do
    let info ← getConstInfo name
    let t ← ppExpr info.type
    let item := Json.mkObj [("name",toJson name.toString),("universes",toJson (info.levelParams.map Name.toString)),("lean_type",toJson (t.pretty 10000))]
    logInfo m!"DECL_JSON:{item.compress}"
