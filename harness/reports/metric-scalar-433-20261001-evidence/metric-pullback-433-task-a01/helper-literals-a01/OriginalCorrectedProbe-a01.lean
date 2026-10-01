import Lean
import Poincare.Global.SmoothInitialMetricLocalPullback
open Lean Elab Command Meta
set_option autoImplicit false
run_cmd do
  let name := "Poincare.SmoothInitialMetricLocalPullback.localEuclideanInner_symm".toName
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
  logInfo "AXIOM_CONTRACT_OK: Poincare.SmoothInitialMetricLocalPullback.localEuclideanInner_symm"
run_cmd do
  let name := "Poincare.SmoothInitialMetricLocalPullback.localEuclideanInner_pos".toName
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
  logInfo "AXIOM_CONTRACT_OK: Poincare.SmoothInitialMetricLocalPullback.localEuclideanInner_pos"
run_cmd do
  let name := "Poincare.SmoothInitialMetricLocalPullback.localEuclideanInner_coordinates".toName
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
  logInfo "AXIOM_CONTRACT_OK: Poincare.SmoothInitialMetricLocalPullback.localEuclideanInner_coordinates"
run_cmd do
  let name := "Poincare.SmoothInitialMetricLocalPullback.localEuclideanInner_contMDiffOn".toName
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
  logInfo "AXIOM_CONTRACT_OK: Poincare.SmoothInitialMetricLocalPullback.localEuclideanInner_contMDiffOn"
universe u
run_cmd liftTermElabM do
  let info ← getConstInfo "Poincare.SmoothInitialMetricLocalPullback.localEuclideanInner_symm".toName
  let levels : List Level := [Level.param "u".toName]
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "∀ {M : Type u} [inst : TopologicalSpace.{u} M] [inst_1 : ChartedSpace.{0, u} (Poincare.ClosedSmoothModel (3 : Nat)) M] [inst_2 : IsManifold.{0, 0, 0, u} (Poincare.closedSmoothModelWithCorners (3 : Nat)) (((⊤ : ENat) : WithTop ENat)) M] (p x : M) (v w : TangentSpace.{0, 0, 0, u} (Poincare.closedSmoothModelWithCorners (3 : Nat)) x), Eq.{1} (((Poincare.SmoothInitialMetricDefinitions.localEuclideanInner.{u} p x) v) w) (((Poincare.SmoothInitialMetricDefinitions.localEuclideanInner.{u} p x) w) v)" with
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
  logInfo "FROZEN_CONTRACT_OK: Poincare.SmoothInitialMetricLocalPullback.localEuclideanInner_symm"
run_cmd liftTermElabM do
  let info ← getConstInfo "Poincare.SmoothInitialMetricLocalPullback.localEuclideanInner_pos".toName
  let levels : List Level := [Level.param "u".toName]
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "∀ {M : Type u} [inst : TopologicalSpace.{u} M] [inst_1 : ChartedSpace.{0, u} (Poincare.ClosedSmoothModel (3 : Nat)) M] [inst_2 : IsManifold.{0, 0, 0, u} (Poincare.closedSmoothModelWithCorners (3 : Nat)) (((⊤ : ENat) : WithTop ENat)) M] (p x : M), Membership.mem.{u, u} (Bundle.Trivialization.baseSet.{u, 0, u} (FiberBundle.trivializationAt.{u, 0, 0} (Poincare.ClosedSmoothModel (3 : Nat)) (TangentSpace.{0, 0, 0, u} (Poincare.closedSmoothModelWithCorners (3 : Nat))) p)) x → ∀ (v : TangentSpace.{0, 0, 0, u} (Poincare.closedSmoothModelWithCorners (3 : Nat)) x), Ne.{1} v (0 : TangentSpace.{0, 0, 0, u} (Poincare.closedSmoothModelWithCorners (3 : Nat)) x) → LT.lt.{0} (0 : Real) (((Poincare.SmoothInitialMetricDefinitions.localEuclideanInner.{u} p x) v) v)" with
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
  logInfo "FROZEN_CONTRACT_OK: Poincare.SmoothInitialMetricLocalPullback.localEuclideanInner_pos"
run_cmd liftTermElabM do
  let info ← getConstInfo "Poincare.SmoothInitialMetricLocalPullback.localEuclideanInner_coordinates".toName
  let levels : List Level := [Level.param "u".toName]
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "∀ {M : Type u} [inst : TopologicalSpace.{u} M] [inst_1 : ChartedSpace.{0, u} (Poincare.ClosedSmoothModel (3 : Nat)) M] [inst_2 : IsManifold.{0, 0, 0, u} (Poincare.closedSmoothModelWithCorners (3 : Nat)) (((⊤ : ENat) : WithTop ENat)) M] (p x : M),\n  Membership.mem.{u, u} (Bundle.Trivialization.baseSet.{u, 0, u} (FiberBundle.trivializationAt.{u, 0, 0} (Poincare.ClosedSmoothModel (3 : Nat)) (TangentSpace.{0, 0, 0, u} (Poincare.closedSmoothModelWithCorners (3 : Nat))) p)) x →\n    let e := FiberBundle.trivializationAt.{u, 0, 0} (Poincare.ClosedSmoothModel (3 : Nat)) (TangentSpace.{0, 0, 0, u} (Poincare.closedSmoothModelWithCorners (3 : Nat))) p;\n    let eR := FiberBundle.trivializationAt.{u, 0, 0} Real (fun (x : M) => Real) p;\n    Eq.{1} ((Bundle.Trivialization.continuousLinearMap.{0, 0, u, 0, 0, 0, 0} (RingHom.id.{0} Real) e (Bundle.Trivialization.continuousLinearMap.{0, 0, u, 0, 0, 0, 0} (RingHom.id.{0} Real) e eR)) (Bundle.TotalSpace.mk' (Poincare.ClosedSmoothModel (3 : Nat) →L[ℝ] Poincare.ClosedSmoothModel (3 : Nat) →L[ℝ] ℝ) x (Poincare.SmoothInitialMetricDefinitions.localEuclideanInner.{u} p x) : Bundle.TotalSpace (Poincare.ClosedSmoothModel (3 : Nat) →L[ℝ] Poincare.ClosedSmoothModel (3 : Nat) →L[ℝ] ℝ) (fun y : M => TangentSpace Poincare.closedSmoothModelWithCorners (3 : Nat) y →L[ℝ] TangentSpace Poincare.closedSmoothModelWithCorners (3 : Nat) y →L[ℝ] ℝ))).2 (innerSL.{0, 0} Real (E := Poincare.ClosedSmoothModel (3 : Nat)))" with
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
  logInfo "FROZEN_CONTRACT_OK: Poincare.SmoothInitialMetricLocalPullback.localEuclideanInner_coordinates"
run_cmd liftTermElabM do
  let info ← getConstInfo "Poincare.SmoothInitialMetricLocalPullback.localEuclideanInner_contMDiffOn".toName
  let levels : List Level := [Level.param "u".toName]
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "∀ {M : Type u} [inst : TopologicalSpace.{u} M] [inst_1 : ChartedSpace.{0, u} (Poincare.ClosedSmoothModel (3 : Nat)) M] [inst_2 : IsManifold.{0, 0, 0, u} (Poincare.closedSmoothModelWithCorners (3 : Nat)) (((⊤ : ENat) : WithTop ENat)) M] (p : M), ContMDiffOn.{0, 0, 0, u, 0, 0, u} (Poincare.closedSmoothModelWithCorners (3 : Nat)) (ModelWithCorners.prod.{0, 0, 0, 0, 0} (Poincare.closedSmoothModelWithCorners (3 : Nat)) (modelWithCornersSelf.{0, 0} Real (ContinuousLinearMap.{0, 0, 0, 0} (RingHom.id.{0} Real) (Poincare.ClosedSmoothModel (3 : Nat)) (ContinuousLinearMap.{0, 0, 0, 0} (RingHom.id.{0} Real) (Poincare.ClosedSmoothModel (3 : Nat)) Real)))) (((⊤ : ENat) : WithTop ENat)) (fun (x : M) => (Bundle.TotalSpace.mk' (Poincare.ClosedSmoothModel (3 : Nat) →L[ℝ] Poincare.ClosedSmoothModel (3 : Nat) →L[ℝ] ℝ) x (Poincare.SmoothInitialMetricDefinitions.localEuclideanInner.{u} p x) : Bundle.TotalSpace (Poincare.ClosedSmoothModel (3 : Nat) →L[ℝ] Poincare.ClosedSmoothModel (3 : Nat) →L[ℝ] ℝ) (fun y : M => TangentSpace Poincare.closedSmoothModelWithCorners (3 : Nat) y →L[ℝ] TangentSpace Poincare.closedSmoothModelWithCorners (3 : Nat) y →L[ℝ] ℝ))) (Bundle.Trivialization.baseSet.{u, 0, u} (FiberBundle.trivializationAt.{u, 0, 0} (Poincare.ClosedSmoothModel (3 : Nat)) (TangentSpace.{0, 0, 0, u} (Poincare.closedSmoothModelWithCorners (3 : Nat))) p))" with
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
  logInfo "FROZEN_CONTRACT_OK: Poincare.SmoothInitialMetricLocalPullback.localEuclideanInner_contMDiffOn"
