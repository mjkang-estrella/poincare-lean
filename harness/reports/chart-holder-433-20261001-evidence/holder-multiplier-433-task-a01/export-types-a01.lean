import Poincare.Global.ParabolicHolderMultiplier
import Lean
set_option pp.fullNames true
set_option pp.funBinderTypes true
set_option pp.piBinderTypes true
set_option pp.universes true
set_option pp.numericTypes true
set_option pp.explicit true
set_option pp.coercions true
set_option maxHeartbeats 0
open Lean Elab Command Meta in
run_cmd liftTermElabM do
  let env ← getEnv
  let mut names : Array Name := #[]
  for (name, _) in env.constants.toList do
    if !isPrivateName name then
      if let some idx := env.getModuleIdxFor? name then
        if env.header.moduleNames[idx]! == `Poincare.Global.ParabolicHolderMultiplier then
          names := names.push name
  names := names.qsort (fun a b => a.toString < b.toString)
  for name in names do
    let info ← getConstInfo name
    let t ← ppExpr info.type
    let item := Json.mkObj [("name",toJson name.toString),("universes",toJson (info.levelParams.map Name.toString)),("lean_type",toJson (t.pretty 100000)),("type_expr",toJson (reprStr info.type)),("unsafe",toJson info.isUnsafe),("partial",toJson info.isPartial)]
    logInfo m!"DECL_JSON:{item.compress}"
  logInfo m!"PUBLIC_DECLARATION_COUNT:{names.size}"
