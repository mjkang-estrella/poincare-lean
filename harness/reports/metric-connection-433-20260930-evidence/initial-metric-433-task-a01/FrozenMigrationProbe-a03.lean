import Lean
import Poincare.Global.SmoothInitialMetricDefinitions
open Lean Elab Command Meta
set_option autoImplicit false
run_cmd do
  let name := "Poincare.SmoothInitialMetricDefinitions.positiveSymmetricBilinearForms".toName
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
  logInfo "AXIOM_CONTRACT_OK: Poincare.SmoothInitialMetricDefinitions.positiveSymmetricBilinearForms"
run_cmd do
  let name := "Poincare.SmoothInitialMetricDefinitions.localEuclideanInner".toName
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
  logInfo "AXIOM_CONTRACT_OK: Poincare.SmoothInitialMetricDefinitions.localEuclideanInner"
run_cmd do
  let name := "Poincare.SmoothInitialMetricDefinitions.localEuclideanInner_apply".toName
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
  logInfo "AXIOM_CONTRACT_OK: Poincare.SmoothInitialMetricDefinitions.localEuclideanInner_apply"
universe v u
run_cmd liftTermElabM do
  let info ← getConstInfo "Poincare.SmoothInitialMetricDefinitions.positiveSymmetricBilinearForms".toName
  let levels : List Level := [Level.param "v".toName]
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "(V : Type v) → [inst : NormedAddCommGroup.{v} V] → [inst_1 : NormedSpace.{0, v} Real V] → Set.{v} (ContinuousLinearMap.{0, 0, v, v} (RingHom.id.{0} Real) V (ContinuousLinearMap.{0, 0, v, 0} (RingHom.id.{0} Real) V Real))" with
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
  logInfo "FROZEN_CONTRACT_OK: Poincare.SmoothInitialMetricDefinitions.positiveSymmetricBilinearForms"
run_cmd liftTermElabM do
  let info ← getConstInfo "Poincare.SmoothInitialMetricDefinitions.localEuclideanInner".toName
  let levels : List Level := [Level.param "u".toName]
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "{M : Type u} → [inst : TopologicalSpace.{u} M] → [inst_1 : ChartedSpace.{0, u} (Poincare.ClosedSmoothModel (3 : Nat)) M] → [IsManifold.{0, 0, 0, u} (Poincare.closedSmoothModelWithCorners (3 : Nat)) (((⊤ : ENat) : WithTop ENat)) M] → M → (x : M) → ContinuousLinearMap.{0, 0, 0, 0} (RingHom.id.{0} Real) (TangentSpace.{0, 0, 0, u} (Poincare.closedSmoothModelWithCorners (3 : Nat)) x) (ContinuousLinearMap.{0, 0, 0, 0} (RingHom.id.{0} Real) (TangentSpace.{0, 0, 0, u} (Poincare.closedSmoothModelWithCorners (3 : Nat)) x) Real)" with
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
  logInfo "FROZEN_CONTRACT_OK: Poincare.SmoothInitialMetricDefinitions.localEuclideanInner"
run_cmd liftTermElabM do
  let info ← getConstInfo "Poincare.SmoothInitialMetricDefinitions.localEuclideanInner_apply".toName
  let levels : List Level := [Level.param "u".toName]
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "∀ {M : Type u} [inst : TopologicalSpace.{u} M] [inst_1 : ChartedSpace.{0, u} (Poincare.ClosedSmoothModel (3 : Nat)) M] [inst_2 : IsManifold.{0, 0, 0, u} (Poincare.closedSmoothModelWithCorners (3 : Nat)) (((⊤ : ENat) : WithTop ENat)) M] (p x : M) (a b : TangentSpace.{0, 0, 0, u} (Poincare.closedSmoothModelWithCorners (3 : Nat)) x), Eq.{1} (((Poincare.SmoothInitialMetricDefinitions.localEuclideanInner.{u} p x) a) b) (Inner.inner.{0, 0} Real ((Bundle.Trivialization.continuousLinearMapAt.{0, u, 0, 0} Real (FiberBundle.trivializationAt.{u, 0, 0} (Poincare.ClosedSmoothModel (3 : Nat)) (TangentSpace.{0, 0, 0, u} (Poincare.closedSmoothModelWithCorners (3 : Nat))) p) x) a) ((Bundle.Trivialization.continuousLinearMapAt.{0, u, 0, 0} Real (FiberBundle.trivializationAt.{u, 0, 0} (Poincare.ClosedSmoothModel (3 : Nat)) (TangentSpace.{0, 0, 0, u} (Poincare.closedSmoothModelWithCorners (3 : Nat))) p) x) b))" with
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
  logInfo "FROZEN_CONTRACT_OK: Poincare.SmoothInitialMetricDefinitions.localEuclideanInner_apply"
