import Poincare.ChartIdentification
import Lean
set_option pp.fullNames true
set_option pp.funBinderTypes true
set_option pp.piBinderTypes true
set_option pp.universes true
set_option pp.numericTypes true
set_option pp.coercions true
set_option pp.notation false
set_option pp.proofs true
set_option maxRecDepth 10000
open Lean Elab Command Meta in
run_cmd liftTermElabM do
  for name in #[``mlieBracket_apply_chart, ``mpullbackWithin_extChartAt_symm_self, ``extDerivFun_apply_chart, ``extDerivFun_apply_fixed_chart, ``isLocallyConstant_of_extDerivFun_eq_zero, ``extDerivFun_apply_mlieBracket_chart, ``mpullback_extChartAt_symm_apply, ``extDerivFun_section_eventually_chart, ``extDerivFun_extDerivFun_chart, ``extDerivFun_apply_mlieBracket, ``mlieBracket_apply_chart_eq, ``mpullbackWithin_extChartAt_symm_self_eq, ``extDerivFun_apply_chart_eq, ``extDerivFun_apply_fixed_chart_eq, ``isLocallyConstant_of_extDerivFun_eq_zero_eq, ``extDerivFun_apply_mlieBracket_chart_eq, ``mpullback_extChartAt_symm_apply_eq, ``extDerivFun_section_eventually_chart_eq, ``extDerivFun_extDerivFun_chart_eq, ``extDerivFun_apply_mlieBracket_eq] do
    let info ← getConstInfo name
    unless ← isProp info.type do
      throwError "expected original theorem type to be Prop: {name}"
    let t ← ppExpr info.type
    let item := Json.mkObj [("name",toJson name.toString),("universes",toJson (info.levelParams.map Name.toString)),("lean_type",toJson (t.pretty 100000)),("kernel_type_repr",toJson (reprStr info.type)),("expected_prop",toJson true)]
    logInfo m!"DECL_JSON:{item.compress}"
