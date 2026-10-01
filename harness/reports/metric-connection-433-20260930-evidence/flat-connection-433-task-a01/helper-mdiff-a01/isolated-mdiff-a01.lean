import Lean
import Poincare.FlatModelConnection
open Lean Elab Command Meta
open scoped Manifold ContDiff
set_option autoImplicit false
universe u_1 u_2
run_cmd liftTermElabM do
  let info ← getConstInfo "mdiffAt_vectorSpace_iff_differentiableAt".toName
  let levels : List Level := [Level.param "u_1".toName, Level.param "u_2".toName]
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "∀ {𝕜 : Type u_1} [NontriviallyNormedField 𝕜] {E : Type u_2} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {σ : ∀ x : E, TangentSpace 𝓘(𝕜, E) x} {x : E}, MDifferentiableAt 𝓘(𝕜, E) (𝓘(𝕜, E).prod 𝓘(𝕜, E)) (fun y : E => (Bundle.TotalSpace.mk' E y (σ y) : Bundle.TotalSpace E (fun y : E => TangentSpace 𝓘(𝕜, E) y))) x ↔ DifferentiableAt 𝕜 σ x" with
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
  logInfo "FROZEN_CONTRACT_OK: mdiffAt_vectorSpace_iff_differentiableAt"
