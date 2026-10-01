import Lean
import Poincare.FlatModelConnection
open Lean Elab Command Meta
open scoped Manifold ContDiff
set_option autoImplicit false
universe u_1 u_2
run_cmd liftTermElabM do
  let info ← getConstInfo "flatCovariantDerivative".toName
  let levels : List Level := [Level.param "u_1".toName, Level.param "u_2".toName]
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "(𝕜 : Type u_1) → [inst : NontriviallyNormedField.{u_1} 𝕜] → (E : Type u_2) → [inst_1 : NormedAddCommGroup.{u_2} E] → [inst_2 : NormedSpace.{u_1, u_2} 𝕜 E] → CovariantDerivative.{u_1, u_2, u_2, u_2, u_2, u_2} (modelWithCornersSelf.{u_1, u_2} 𝕜 E) E (TangentSpace.{u_2, u_1, u_2, u_2} (modelWithCornersSelf.{u_1, u_2} 𝕜 E))" with
    | .ok parsedType => pure parsedType
    | .error error => throwError error
  let expected ← Term.elabType parsedType
  Term.synthesizeSyntheticMVarsNoPostponing
  let expected ← instantiateMVars expected
  if expected.hasMVar || expected.hasLevelMVar then
    throwError "unresolved metavariables in frozen type for {info.name}"
  let actual := info.type.instantiateLevelParams info.levelParams levels
  unless ← isDefEq actual expected do
    throwError "frozen type mismatch for {info.name}: actual {actual}, expected {expected}"
  logInfo "FROZEN_CONTRACT_OK: flatCovariantDerivative"
