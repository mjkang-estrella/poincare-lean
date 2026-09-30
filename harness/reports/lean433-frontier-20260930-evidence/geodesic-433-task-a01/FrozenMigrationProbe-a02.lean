import Lean
import Poincare.Global.GeodesicChart
open Lean Elab Command Meta
set_option autoImplicit false
run_cmd do
  let name := "Poincare.geodesicFlowField".toName
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
  logInfo "AXIOM_CONTRACT_OK: Poincare.geodesicFlowField"
run_cmd do
  let name := "Poincare.geodesicFlowField_apply".toName
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
  logInfo "AXIOM_CONTRACT_OK: Poincare.geodesicFlowField_apply"
run_cmd do
  let name := "Poincare.contDiffAt_geodesicFlowField".toName
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
  logInfo "AXIOM_CONTRACT_OK: Poincare.contDiffAt_geodesicFlowField"
run_cmd do
  let name := "Poincare.contDiff_geodesicFlowField".toName
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
  logInfo "AXIOM_CONTRACT_OK: Poincare.contDiff_geodesicFlowField"
run_cmd do
  let name := "Poincare.exists_geodesicFlowField_solution_of_contDiffAt".toName
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
  logInfo "AXIOM_CONTRACT_OK: Poincare.exists_geodesicFlowField_solution_of_contDiffAt"
run_cmd do
  let name := "Poincare.exists_geodesicFlowField_solution".toName
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
  logInfo "AXIOM_CONTRACT_OK: Poincare.exists_geodesicFlowField_solution"
run_cmd do
  let name := "Poincare.exists_geodesicFlowField_solution_of_contDiff".toName
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
  logInfo "AXIOM_CONTRACT_OK: Poincare.exists_geodesicFlowField_solution_of_contDiff"
run_cmd do
  let name := "Poincare.geodesicFlowField_eventuallyEq_of_lipschitz".toName
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
  logInfo "AXIOM_CONTRACT_OK: Poincare.geodesicFlowField_eventuallyEq_of_lipschitz"
run_cmd do
  let name := "Poincare.geodesicFlowField_eventuallyEq_of_contDiffAt".toName
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
  logInfo "AXIOM_CONTRACT_OK: Poincare.geodesicFlowField_eventuallyEq_of_contDiffAt"
run_cmd do
  let name := "Poincare.geodesic_position_hasDerivAt".toName
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
  logInfo "AXIOM_CONTRACT_OK: Poincare.geodesic_position_hasDerivAt"
run_cmd do
  let name := "Poincare.geodesic_velocity_hasDerivAt".toName
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
  logInfo "AXIOM_CONTRACT_OK: Poincare.geodesic_velocity_hasDerivAt"
run_cmd do
  let name := "Poincare.geodesic_components_hasDerivAt".toName
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
  logInfo "AXIOM_CONTRACT_OK: Poincare.geodesic_components_hasDerivAt"
universe u_1
run_cmd liftTermElabM do
  let info ← getConstInfo "Poincare.geodesicFlowField".toName
  let levels : List Level := [Level.param "u_1".toName]
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "{E : Type u_1} → [inst : NormedAddCommGroup.{u_1} E] → [inst_1 : NormedSpace.{0, u_1} Real E] → (E → ContinuousLinearMap.{0, 0, u_1, u_1} (RingHom.id.{0} Real) E (ContinuousLinearMap.{0, 0, u_1, u_1} (RingHom.id.{0} Real) E E)) → Prod.{u_1, u_1} E E → Prod.{u_1, u_1} E E" with
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
  logInfo "FROZEN_CONTRACT_OK: Poincare.geodesicFlowField"
run_cmd liftTermElabM do
  let info ← getConstInfo "Poincare.geodesicFlowField_apply".toName
  let levels : List Level := [Level.param "u_1".toName]
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "∀ {E : Type u_1} [inst : NormedAddCommGroup.{u_1} E] [inst_1 : NormedSpace.{0, u_1} Real E] (Γ : E → ContinuousLinearMap.{0, 0, u_1, u_1} (RingHom.id.{0} Real) E (ContinuousLinearMap.{0, 0, u_1, u_1} (RingHom.id.{0} Real) E E)) (p : Prod.{u_1, u_1} E E), Eq.{u_1 + 1} (Poincare.geodesicFlowField.{u_1} Γ p) (Prod.mk.{u_1, u_1} p.2 (Neg.neg.{u_1} (((Γ p.1) p.2) p.2)))" with
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
  logInfo "FROZEN_CONTRACT_OK: Poincare.geodesicFlowField_apply"
run_cmd liftTermElabM do
  let info ← getConstInfo "Poincare.contDiffAt_geodesicFlowField".toName
  let levels : List Level := [Level.param "u_1".toName]
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "∀ {E : Type u_1} [inst : NormedAddCommGroup.{u_1} E] [inst_1 : NormedSpace.{0, u_1} Real E] {Γ : E → ContinuousLinearMap.{0, 0, u_1, u_1} (RingHom.id.{0} Real) E (ContinuousLinearMap.{0, 0, u_1, u_1} (RingHom.id.{0} Real) E E)} {p₀ : Prod.{u_1, u_1} E E}, ContDiffAt.{0, u_1, u_1} Real (1 : WithTop.{0} ENat) Γ p₀.1 → ContDiffAt.{0, u_1, u_1} Real (1 : WithTop.{0} ENat) (Poincare.geodesicFlowField.{u_1} Γ) p₀" with
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
  logInfo "FROZEN_CONTRACT_OK: Poincare.contDiffAt_geodesicFlowField"
run_cmd liftTermElabM do
  let info ← getConstInfo "Poincare.contDiff_geodesicFlowField".toName
  let levels : List Level := [Level.param "u_1".toName]
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "∀ {E : Type u_1} [inst : NormedAddCommGroup.{u_1} E] [inst_1 : NormedSpace.{0, u_1} Real E] {Γ : E → ContinuousLinearMap.{0, 0, u_1, u_1} (RingHom.id.{0} Real) E (ContinuousLinearMap.{0, 0, u_1, u_1} (RingHom.id.{0} Real) E E)}, ContDiff.{0, u_1, u_1} Real (1 : WithTop.{0} ENat) Γ → ContDiff.{0, u_1, u_1} Real (1 : WithTop.{0} ENat) (Poincare.geodesicFlowField.{u_1} Γ)" with
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
  logInfo "FROZEN_CONTRACT_OK: Poincare.contDiff_geodesicFlowField"
run_cmd liftTermElabM do
  let info ← getConstInfo "Poincare.exists_geodesicFlowField_solution_of_contDiffAt".toName
  let levels : List Level := [Level.param "u_1".toName]
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "∀ {E : Type u_1} [inst : NormedAddCommGroup.{u_1} E] [inst_1 : NormedSpace.{0, u_1} Real E] [CompleteSpace.{u_1} E] {Γ : E → ContinuousLinearMap.{0, 0, u_1, u_1} (RingHom.id.{0} Real) E (ContinuousLinearMap.{0, 0, u_1, u_1} (RingHom.id.{0} Real) E E)} {p₀ : Prod.{u_1, u_1} E E}, ContDiffAt.{0, u_1, u_1} Real (1 : WithTop.{0} ENat) (Poincare.geodesicFlowField.{u_1} Γ) p₀ → ∃ (ε : Real), And (GT.gt.{0} ε (0 : Real)) (∃ (γ : Real → Prod.{u_1, u_1} E E), And (Eq.{u_1 + 1} (γ (0 : Real)) p₀) (∀ (t : Real), Membership.mem.{0, 0} (Set.Ioo.{0} (Neg.neg.{0} ε) ε) t → HasDerivAt.{0, u_1} γ (Poincare.geodesicFlowField.{u_1} Γ (γ t)) t))" with
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
  logInfo "FROZEN_CONTRACT_OK: Poincare.exists_geodesicFlowField_solution_of_contDiffAt"
run_cmd liftTermElabM do
  let info ← getConstInfo "Poincare.exists_geodesicFlowField_solution".toName
  let levels : List Level := [Level.param "u_1".toName]
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "∀ {E : Type u_1} [inst : NormedAddCommGroup.{u_1} E] [inst_1 : NormedSpace.{0, u_1} Real E] [CompleteSpace.{u_1} E] {Γ : E → ContinuousLinearMap.{0, 0, u_1, u_1} (RingHom.id.{0} Real) E (ContinuousLinearMap.{0, 0, u_1, u_1} (RingHom.id.{0} Real) E E)} {p₀ : Prod.{u_1, u_1} E E}, ContDiffAt.{0, u_1, u_1} Real (1 : WithTop.{0} ENat) Γ p₀.1 → ∃ (ε : Real), And (GT.gt.{0} ε (0 : Real)) (∃ (γ : Real → Prod.{u_1, u_1} E E), And (Eq.{u_1 + 1} (γ (0 : Real)) p₀) (∀ (t : Real), Membership.mem.{0, 0} (Set.Ioo.{0} (Neg.neg.{0} ε) ε) t → HasDerivAt.{0, u_1} γ (Poincare.geodesicFlowField.{u_1} Γ (γ t)) t))" with
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
  logInfo "FROZEN_CONTRACT_OK: Poincare.exists_geodesicFlowField_solution"
run_cmd liftTermElabM do
  let info ← getConstInfo "Poincare.exists_geodesicFlowField_solution_of_contDiff".toName
  let levels : List Level := [Level.param "u_1".toName]
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "∀ {E : Type u_1} [inst : NormedAddCommGroup.{u_1} E] [inst_1 : NormedSpace.{0, u_1} Real E] [CompleteSpace.{u_1} E] {Γ : E → ContinuousLinearMap.{0, 0, u_1, u_1} (RingHom.id.{0} Real) E (ContinuousLinearMap.{0, 0, u_1, u_1} (RingHom.id.{0} Real) E E)}, ContDiff.{0, u_1, u_1} Real (1 : WithTop.{0} ENat) Γ → ∀ (p₀ : Prod.{u_1, u_1} E E), ∃ (ε : Real), And (GT.gt.{0} ε (0 : Real)) (∃ (γ : Real → Prod.{u_1, u_1} E E), And (Eq.{u_1 + 1} (γ (0 : Real)) p₀) (∀ (t : Real), Membership.mem.{0, 0} (Set.Ioo.{0} (Neg.neg.{0} ε) ε) t → HasDerivAt.{0, u_1} γ (Poincare.geodesicFlowField.{u_1} Γ (γ t)) t))" with
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
  logInfo "FROZEN_CONTRACT_OK: Poincare.exists_geodesicFlowField_solution_of_contDiff"
run_cmd liftTermElabM do
  let info ← getConstInfo "Poincare.geodesicFlowField_eventuallyEq_of_lipschitz".toName
  let levels : List Level := [Level.param "u_1".toName]
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "∀ {E : Type u_1} [inst : NormedAddCommGroup.{u_1} E] [inst_1 : NormedSpace.{0, u_1} Real E] {Γ : E → ContinuousLinearMap.{0, 0, u_1, u_1} (RingHom.id.{0} Real) E (ContinuousLinearMap.{0, 0, u_1, u_1} (RingHom.id.{0} Real) E E)} {γ η : Real → Prod.{u_1, u_1} E E} {K : NNReal} {s : Real → Set.{u_1} (Prod.{u_1, u_1} E E)}, (∀ᶠ (t : Real) in nhds.{0} (0 : Real), LipschitzOnWith.{u_1, u_1} K (fun (p : Prod.{u_1, u_1} E E) => Poincare.geodesicFlowField.{u_1} Γ p) (s t)) → (∀ᶠ (t : Real) in nhds.{0} (0 : Real), And (HasDerivAt.{0, u_1} γ (Poincare.geodesicFlowField.{u_1} Γ (γ t)) t) (Membership.mem.{u_1, u_1} (s t) (γ t))) → (∀ᶠ (t : Real) in nhds.{0} (0 : Real), And (HasDerivAt.{0, u_1} η (Poincare.geodesicFlowField.{u_1} Γ (η t)) t) (Membership.mem.{u_1, u_1} (s t) (η t))) → Eq.{u_1 + 1} (γ (0 : Real)) (η (0 : Real)) → Filter.EventuallyEq.{0, u_1} (nhds.{0} (0 : Real)) γ η" with
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
  logInfo "FROZEN_CONTRACT_OK: Poincare.geodesicFlowField_eventuallyEq_of_lipschitz"
run_cmd liftTermElabM do
  let info ← getConstInfo "Poincare.geodesicFlowField_eventuallyEq_of_contDiffAt".toName
  let levels : List Level := [Level.param "u_1".toName]
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "∀ {E : Type u_1} [inst : NormedAddCommGroup.{u_1} E] [inst_1 : NormedSpace.{0, u_1} Real E] {Γ : E → ContinuousLinearMap.{0, 0, u_1, u_1} (RingHom.id.{0} Real) E (ContinuousLinearMap.{0, 0, u_1, u_1} (RingHom.id.{0} Real) E E)} {p₀ : Prod.{u_1, u_1} E E} {γ η : Real → Prod.{u_1, u_1} E E}, ContDiffAt.{0, u_1, u_1} Real (1 : WithTop.{0} ENat) (Poincare.geodesicFlowField.{u_1} Γ) p₀ → Eq.{u_1 + 1} (γ (0 : Real)) p₀ → Eq.{u_1 + 1} (η (0 : Real)) p₀ → (∀ᶠ (t : Real) in nhds.{0} (0 : Real), HasDerivAt.{0, u_1} γ (Poincare.geodesicFlowField.{u_1} Γ (γ t)) t) → (∀ᶠ (t : Real) in nhds.{0} (0 : Real), HasDerivAt.{0, u_1} η (Poincare.geodesicFlowField.{u_1} Γ (η t)) t) → Filter.EventuallyEq.{0, u_1} (nhds.{0} (0 : Real)) γ η" with
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
  logInfo "FROZEN_CONTRACT_OK: Poincare.geodesicFlowField_eventuallyEq_of_contDiffAt"
run_cmd liftTermElabM do
  let info ← getConstInfo "Poincare.geodesic_position_hasDerivAt".toName
  let levels : List Level := [Level.param "u_1".toName]
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "∀ {E : Type u_1} [inst : NormedAddCommGroup.{u_1} E] [inst_1 : NormedSpace.{0, u_1} Real E] {Γ : E → ContinuousLinearMap.{0, 0, u_1, u_1} (RingHom.id.{0} Real) E (ContinuousLinearMap.{0, 0, u_1, u_1} (RingHom.id.{0} Real) E E)} {γ : Real → Prod.{u_1, u_1} E E} {t : Real}, HasDerivAt.{0, u_1} γ (Poincare.geodesicFlowField.{u_1} Γ (γ t)) t → HasDerivAt.{0, u_1} (fun (τ : Real) => (γ τ).1) (γ t).2 t" with
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
  logInfo "FROZEN_CONTRACT_OK: Poincare.geodesic_position_hasDerivAt"
run_cmd liftTermElabM do
  let info ← getConstInfo "Poincare.geodesic_velocity_hasDerivAt".toName
  let levels : List Level := [Level.param "u_1".toName]
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "∀ {E : Type u_1} [inst : NormedAddCommGroup.{u_1} E] [inst_1 : NormedSpace.{0, u_1} Real E] {Γ : E → ContinuousLinearMap.{0, 0, u_1, u_1} (RingHom.id.{0} Real) E (ContinuousLinearMap.{0, 0, u_1, u_1} (RingHom.id.{0} Real) E E)} {γ : Real → Prod.{u_1, u_1} E E} {t : Real}, HasDerivAt.{0, u_1} γ (Poincare.geodesicFlowField.{u_1} Γ (γ t)) t → HasDerivAt.{0, u_1} (fun (τ : Real) => (γ τ).2) (Neg.neg.{u_1} (((Γ (γ t).1) (γ t).2) (γ t).2)) t" with
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
  logInfo "FROZEN_CONTRACT_OK: Poincare.geodesic_velocity_hasDerivAt"
run_cmd liftTermElabM do
  let info ← getConstInfo "Poincare.geodesic_components_hasDerivAt".toName
  let levels : List Level := [Level.param "u_1".toName]
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "∀ {E : Type u_1} [inst : NormedAddCommGroup.{u_1} E] [inst_1 : NormedSpace.{0, u_1} Real E] {Γ : E → ContinuousLinearMap.{0, 0, u_1, u_1} (RingHom.id.{0} Real) E (ContinuousLinearMap.{0, 0, u_1, u_1} (RingHom.id.{0} Real) E E)} {γ : Real → Prod.{u_1, u_1} E E} {I : Set.{0} Real}, (∀ (t : Real), Membership.mem.{0, 0} I t → HasDerivAt.{0, u_1} γ (Poincare.geodesicFlowField.{u_1} Γ (γ t)) t) → And (∀ (t : Real), Membership.mem.{0, 0} I t → HasDerivAt.{0, u_1} (fun (τ : Real) => (γ τ).1) (γ t).2 t) (∀ (t : Real), Membership.mem.{0, 0} I t → HasDerivAt.{0, u_1} (fun (τ : Real) => (γ τ).2) (Neg.neg.{u_1} (((Γ (γ t).1) (γ t).2) (γ t).2)) t)" with
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
  logInfo "FROZEN_CONTRACT_OK: Poincare.geodesic_components_hasDerivAt"
