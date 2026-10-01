import Poincare.FlatModelConnection
import Lean
set_option pp.fullNames true
set_option pp.funBinderTypes true
set_option pp.piBinderTypes true
set_option pp.universes true
set_option pp.numericTypes true
set_option pp.coercions true
set_option pp.notation false
set_option pp.explicit true
open Lean Elab Command Meta in
run_cmd liftTermElabM do
  let info ← getConstInfo ``mdiffAt_vectorSpace_iff_differentiableAt
  let t ← ppExpr info.type
  logInfo m!"DECL_JSON:{(Json.mkObj [("name",toJson info.name.toString),("universes",toJson (info.levelParams.map Name.toString)),("lean_type",toJson (t.pretty 10000))]).compress}"
