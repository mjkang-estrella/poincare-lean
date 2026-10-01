import Poincare.Global.RoundSphereChart
import Lean
set_option pp.fullNames true
set_option pp.funBinderTypes true
set_option pp.piBinderTypes true
set_option pp.universes true
set_option pp.numericTypes true
set_option pp.coercions true
open Lean Elab Command Meta in
run_cmd liftTermElabM do
  for name in #[``Poincare.stereoInvFunAuxConformalFactor, ``Poincare.stereoInvFunAuxFDeriv, ``Poincare.stereoInvFunAuxFDeriv_apply, ``Poincare.hasFDerivAt_stereoInvFunAuxFDeriv, ``Poincare.fderiv_stereoInvFunAux, ``Poincare.fderiv_stereoInvFunAux_comp_subtype, ``Poincare.inner_stereoInvFunAuxFDeriv_of_mem_orthogonal, ``Poincare.inner_fderiv_stereoInvFunAux_comp_subtype] do
    let info ← getConstInfo name
    let t ← ppExpr info.type
    let item := Json.mkObj [("name", toJson name.toString), ("universes", toJson (info.levelParams.map Name.toString)), ("lean_type", toJson (t.pretty 10000)), ("is_prop", toJson (← isProp info.type)), ("is_theorem", toJson info.isTheorem)]
    logInfo m!"DECL_JSON:{item.compress}"
