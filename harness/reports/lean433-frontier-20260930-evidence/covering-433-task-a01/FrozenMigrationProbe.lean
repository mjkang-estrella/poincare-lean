import Lean
import Poincare.Global.CoveringSkeleton
open Lean Elab Command Meta
set_option autoImplicit false
run_cmd do
  let name := "Poincare.GlobalCoveringSkeleton.surjective_of_isOpen_isClosed_range".toName
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
  logInfo "AXIOM_CONTRACT_OK: Poincare.GlobalCoveringSkeleton.surjective_of_isOpen_isClosed_range"
run_cmd do
  let name := "Poincare.GlobalCoveringSkeleton.IsLocalHomeomorph.surjective_of_isClosed_range".toName
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
  logInfo "AXIOM_CONTRACT_OK: Poincare.GlobalCoveringSkeleton.IsLocalHomeomorph.surjective_of_isClosed_range"
run_cmd do
  let name := "Poincare.GlobalCoveringSkeleton.isCoveringMap_of_compact_isLocalHomeomorph".toName
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
  logInfo "AXIOM_CONTRACT_OK: Poincare.GlobalCoveringSkeleton.isCoveringMap_of_compact_isLocalHomeomorph"
run_cmd do
  let name := "Poincare.GlobalCoveringSkeleton.bijective_of_isCoveringMap_simplyConnected".toName
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
  logInfo "AXIOM_CONTRACT_OK: Poincare.GlobalCoveringSkeleton.bijective_of_isCoveringMap_simplyConnected"
run_cmd do
  let name := "Poincare.GlobalCoveringSkeleton.isHomeomorph_of_isCoveringMap_simplyConnected".toName
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
  logInfo "AXIOM_CONTRACT_OK: Poincare.GlobalCoveringSkeleton.isHomeomorph_of_isCoveringMap_simplyConnected"
run_cmd do
  let name := "Poincare.GlobalCoveringSkeleton.homeomorphOfIsCoveringMapSimplyConnected".toName
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
  logInfo "AXIOM_CONTRACT_OK: Poincare.GlobalCoveringSkeleton.homeomorphOfIsCoveringMapSimplyConnected"
universe u v
run_cmd liftTermElabM do
  let info ← getConstInfo "Poincare.GlobalCoveringSkeleton.surjective_of_isOpen_isClosed_range".toName
  let levels : List Level := [Level.param "u".toName, Level.param "v".toName]
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "∀ {E : Type u} {X : Type v} [inst : TopologicalSpace.{v} X] {p : E → X} [@PreconnectedSpace.{v} X inst] [Nonempty.{u + 1} E], @IsOpen.{v} X inst (@Set.range.{v, u + 1} X E p) → @IsClosed.{v} X inst (@Set.range.{v, u + 1} X E p) → @Function.Surjective.{u + 1, v + 1} E X p" with
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
  logInfo "FROZEN_CONTRACT_OK: Poincare.GlobalCoveringSkeleton.surjective_of_isOpen_isClosed_range"
run_cmd liftTermElabM do
  let info ← getConstInfo "Poincare.GlobalCoveringSkeleton.IsLocalHomeomorph.surjective_of_isClosed_range".toName
  let levels : List Level := [Level.param "u".toName, Level.param "v".toName]
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "∀ {E : Type u} {X : Type v} [inst : TopologicalSpace.{u} E] [inst_1 : TopologicalSpace.{v} X] {p : E → X} [@PreconnectedSpace.{v} X inst_1] [Nonempty.{u + 1} E], @IsLocalHomeomorph.{u, v} E X inst inst_1 p → @IsClosed.{v} X inst_1 (@Set.range.{v, u + 1} X E p) → @Function.Surjective.{u + 1, v + 1} E X p" with
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
  logInfo "FROZEN_CONTRACT_OK: Poincare.GlobalCoveringSkeleton.IsLocalHomeomorph.surjective_of_isClosed_range"
run_cmd liftTermElabM do
  let info ← getConstInfo "Poincare.GlobalCoveringSkeleton.isCoveringMap_of_compact_isLocalHomeomorph".toName
  let levels : List Level := [Level.param "u".toName, Level.param "v".toName]
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "∀ {E : Type u} {X : Type v} [inst : TopologicalSpace.{u} E] [inst_1 : TopologicalSpace.{v} X] {p : E → X} [@T2Space.{u} E inst] [@T2Space.{v} X inst_1] [@CompactSpace.{u} E inst], @IsLocalHomeomorph.{u, v} E X inst inst_1 p → @IsCoveringMap.{u, v} E X inst inst_1 p" with
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
  logInfo "FROZEN_CONTRACT_OK: Poincare.GlobalCoveringSkeleton.isCoveringMap_of_compact_isLocalHomeomorph"
run_cmd liftTermElabM do
  let info ← getConstInfo "Poincare.GlobalCoveringSkeleton.bijective_of_isCoveringMap_simplyConnected".toName
  let levels : List Level := [Level.param "u".toName, Level.param "v".toName]
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "∀ {E : Type u} {X : Type v} [inst : TopologicalSpace.{u} E] [inst_1 : TopologicalSpace.{v} X] {p : E → X} [@ConnectedSpace.{u} E inst] [@SimplyConnectedSpace.{v} X inst_1] [@LocallyPathConnectedSpace.{v} X inst_1], @IsCoveringMap.{u, v} E X inst inst_1 p → @Function.Bijective.{u + 1, v + 1} E X p" with
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
  logInfo "FROZEN_CONTRACT_OK: Poincare.GlobalCoveringSkeleton.bijective_of_isCoveringMap_simplyConnected"
run_cmd liftTermElabM do
  let info ← getConstInfo "Poincare.GlobalCoveringSkeleton.isHomeomorph_of_isCoveringMap_simplyConnected".toName
  let levels : List Level := [Level.param "u".toName, Level.param "v".toName]
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "∀ {E : Type u} {X : Type v} [inst : TopologicalSpace.{u} E] [inst_1 : TopologicalSpace.{v} X] {p : E → X} [@ConnectedSpace.{u} E inst] [@SimplyConnectedSpace.{v} X inst_1] [@LocallyPathConnectedSpace.{v} X inst_1], @IsCoveringMap.{u, v} E X inst inst_1 p → @IsHomeomorph.{u, v} E X inst inst_1 p" with
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
  logInfo "FROZEN_CONTRACT_OK: Poincare.GlobalCoveringSkeleton.isHomeomorph_of_isCoveringMap_simplyConnected"
run_cmd liftTermElabM do
  let info ← getConstInfo "Poincare.GlobalCoveringSkeleton.homeomorphOfIsCoveringMapSimplyConnected".toName
  let levels : List Level := [Level.param "u".toName, Level.param "v".toName]
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "{E : Type u} → {X : Type v} → [inst : TopologicalSpace.{u} E] → [inst_1 : TopologicalSpace.{v} X] → {p : E → X} → [@ConnectedSpace.{u} E inst] → [@SimplyConnectedSpace.{v} X inst_1] → [@LocallyPathConnectedSpace.{v} X inst_1] → @IsCoveringMap.{u, v} E X inst inst_1 p → @Homeomorph.{u, v} E X inst inst_1" with
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
  logInfo "FROZEN_CONTRACT_OK: Poincare.GlobalCoveringSkeleton.homeomorphOfIsCoveringMapSimplyConnected"
