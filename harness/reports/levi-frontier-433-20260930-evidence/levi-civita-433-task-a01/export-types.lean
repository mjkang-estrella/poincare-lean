import Poincare.LeviCivitaUniqueness
import Lean
set_option pp.fullNames true
set_option pp.funBinderTypes true
set_option pp.piBinderTypes true
set_option pp.universes true
set_option pp.numericTypes true
set_option pp.coercions true
set_option pp.notation false
open Lean Elab Command Meta in
run_cmd liftTermElabM do
  for name in #[``CovariantDerivative.MetricCompatibleAt, ``CovariantDerivative.TorsionFreeAt, ``CovariantDerivative.leviCivita_unique_at, ``CovariantDerivative.leviCivita_unique_at_values, ``CovariantDerivative.koszul_formula, ``CovariantDerivative.metricCompatibleAt_eq, ``CovariantDerivative.torsionFreeAt_eq, ``CovariantDerivative.leviCivita_unique_at_eq, ``CovariantDerivative.leviCivita_unique_at_values_eq, ``CovariantDerivative.koszul_formula_eq] do
    let info ← getConstInfo name
    let t ← ppExpr info.type
    let item := Json.mkObj [("name",toJson name.toString),("universes",toJson (info.levelParams.map Name.toString)),("lean_type",toJson (t.pretty 10000))]
    logInfo m!"DECL_JSON:{item.compress}"
