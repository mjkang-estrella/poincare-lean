import Poincare.Global.ParabolicHolderMultiplier
import Lean
set_option pp.fullNames true
set_option pp.funBinderTypes true
set_option pp.piBinderTypes true
set_option pp.universes true
set_option pp.numericTypes true
set_option pp.coercions false
set_option pp.proofs true
set_option pp.deepTerms true
set_option maxHeartbeats 8000000
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
  logInfo m!"PUBLIC_NAMES_JSON:{toJson (names.map Name.toString)}"
  for name in names do
    let info ← getConstInfo name
    let t ← ppExpr info.type
    let item := Json.mkObj [("name",toJson name.toString),("universes",toJson (info.levelParams.map Name.toString)),("lean_type",toJson (t.pretty 100000)),("unsafe",toJson info.isUnsafe),("partial",toJson info.isPartial),("is_proposition",toJson (← isProp info.type)),("is_theorem",toJson info.isTheorem)]
    logInfo m!"DECL_JSON:{item.compress}"
  logInfo m!"PUBLIC_DECLARATION_COUNT:{names.size}"
