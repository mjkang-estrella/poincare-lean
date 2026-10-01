import Lean
import Poincare.Global.VerifiedSmoothability
open Lean Elab Command Meta
set_option autoImplicit false
run_cmd do
  let name := "Poincare.existsSmoothabilitySmoothManifoldStatement".toName
  let _ ← getConstInfo name
  let environment := (← getEnv).setExporting false
  let mut pending : List Name := [name]
  let mut seen : NameSet := {}
  while !pending.isEmpty do
    let current := pending.head!
    pending := pending.tail!
    if !seen.contains current then
      seen := seen.insert current
      let some info := environment.find? current |
        throwError "missing dependency {current} in {name}"
      if info.isUnsafe || info.isPartial then
        throwError "unsafe or partial declaration {current} in {name}"
      pending := info.getUsedConstantsAsSet.toList ++ pending
      match info with
      | .recInfo value =>
        for rule in value.rules do
          pending := rule.rhs.getUsedConstants.toList ++ pending
      | .inductInfo value => pending := value.ctors ++ pending
      | _ => pure ()
  let allowed : List Name := ["propext".toName, "Classical.choice".toName, "Quot.sound".toName]
  let footprint ← collectAxioms name
  for dependency in footprint do
    unless allowed.contains dependency do
      throwError "forbidden axiom {dependency} in {name}"
  logInfo "AXIOM_CONTRACT_OK: Poincare.existsSmoothabilitySmoothManifoldStatement"
open scoped Manifold
universe u
run_cmd liftTermElabM do
  let info ← getConstInfo "Poincare.existsSmoothabilitySmoothManifoldStatement".toName
  let levels : List Level := [Level.param "u".toName]
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "∀ (M : Type u) [TopologicalSpace M] [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [SimplyConnectedSpace M] [CompactSpace M], ∃ C : ChartedSpace (EuclideanSpace ℝ (Fin 3)) M, letI := C; IsManifold (𝓡 3) ((⊤ : ENat) : WithTop ENat) M" with
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
  logInfo "FROZEN_CONTRACT_OK: Poincare.existsSmoothabilitySmoothManifoldStatement"

example : Poincare.ExistsSmoothabilitySmoothManifoldStatement.{u} := Poincare.existsSmoothabilitySmoothManifoldStatement
