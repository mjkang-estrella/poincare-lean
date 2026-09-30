import Lean
import Poincare.Global.ParabolicHolderSpace
open Lean Elab Command Meta
set_option autoImplicit false
run_cmd do
  let name := "Poincare.ParabolicHolder.isClosed_holderSubmodule".toName
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
  logInfo "AXIOM_CONTRACT_OK: Poincare.ParabolicHolder.isClosed_holderSubmodule"
run_cmd do
  let name := "Poincare.ParabolicHolder.instCompleteSpace".toName
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
  logInfo "AXIOM_CONTRACT_OK: Poincare.ParabolicHolder.instCompleteSpace"
run_cmd do
  let name := "Poincare.ParabolicHolder.norm_eq".toName
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
  logInfo "AXIOM_CONTRACT_OK: Poincare.ParabolicHolder.norm_eq"
universe u_1 u_2
run_cmd liftTermElabM do
  let info ← getConstInfo "Poincare.ParabolicHolder.isClosed_holderSubmodule".toName
  let levels : List Level := [Level.param "u_1".toName, Level.param "u_2".toName]
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "∀ {E : Type u_1} {F : Type u_2} [inst : NormedAddCommGroup.{u_1} E] [inst_1 : NormedAddCommGroup.{u_2} F] [inst_2 : NormedSpace.{0, u_2} Real F] {α T : Real}, IsClosed.{max u_1 u_2} ↑(Poincare.ParabolicHolder.holderSubmodule.{u_1, u_2} α T)" with
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
  logInfo "FROZEN_CONTRACT_OK: Poincare.ParabolicHolder.isClosed_holderSubmodule"
run_cmd liftTermElabM do
  let info ← getConstInfo "Poincare.ParabolicHolder.instCompleteSpace".toName
  let levels : List Level := [Level.param "u_1".toName, Level.param "u_2".toName]
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "∀ {E : Type u_1} {F : Type u_2} [inst : NormedAddCommGroup.{u_1} E] [inst_1 : NormedAddCommGroup.{u_2} F] [inst_2 : NormedSpace.{0, u_2} Real F] {α T : Real} [CompleteSpace.{u_2} F], CompleteSpace.{max u_2 u_1} (Poincare.ParabolicHolder.Y.{u_1, u_2} α T F)" with
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
  logInfo "FROZEN_CONTRACT_OK: Poincare.ParabolicHolder.instCompleteSpace"
run_cmd liftTermElabM do
  let info ← getConstInfo "Poincare.ParabolicHolder.norm_eq".toName
  let levels : List Level := [Level.param "u_1".toName, Level.param "u_2".toName]
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "∀ {E : Type u_1} {F : Type u_2} [inst : NormedAddCommGroup.{u_1} E] [inst_1 : NormedAddCommGroup.{u_2} F] [inst_2 : NormedSpace.{0, u_2} Real F] {α T : Real} (f : Poincare.ParabolicHolder.Y.{u_1, u_2} α T F), Eq.{1} (Norm.norm.{max u_1 u_2} f) (HAdd.hAdd.{0, 0, 0} (Poincare.ParabolicHolder.supNorm.{u_1, u_2} (Poincare.ParabolicHolder.cylinder.{u_1} T) ↑(WithLp.fst.{max u_1 u_2, max u_1 u_2} ↑f)) (Poincare.ParabolicHolder.holderSeminorm.{u_1, u_2} α (Poincare.ParabolicHolder.cylinder.{u_1} T) ↑(WithLp.fst.{max u_1 u_2, max u_1 u_2} ↑f)))" with
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
  logInfo "FROZEN_CONTRACT_OK: Poincare.ParabolicHolder.norm_eq"
