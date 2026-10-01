import Lean
import Poincare.ChartIdentification
open Lean Elab Command Meta
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped Manifold
universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

run_cmd do
  let name := "mlieBracket_apply_chart".toName
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
  logInfo m!"AXIOM_SAFETY_CONTRACT_OK:{name}:{footprint}"

run_cmd do
  let name := "mpullbackWithin_extChartAt_symm_self".toName
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
  logInfo m!"AXIOM_SAFETY_CONTRACT_OK:{name}:{footprint}"

run_cmd do
  let name := "extDerivFun_apply_chart".toName
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
  logInfo m!"AXIOM_SAFETY_CONTRACT_OK:{name}:{footprint}"

run_cmd do
  let name := "extDerivFun_apply_fixed_chart".toName
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
  logInfo m!"AXIOM_SAFETY_CONTRACT_OK:{name}:{footprint}"

run_cmd do
  let name := "isLocallyConstant_of_extDerivFun_eq_zero".toName
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
  logInfo m!"AXIOM_SAFETY_CONTRACT_OK:{name}:{footprint}"

run_cmd do
  let name := "extDerivFun_apply_mlieBracket_chart".toName
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
  logInfo m!"AXIOM_SAFETY_CONTRACT_OK:{name}:{footprint}"

run_cmd do
  let name := "mpullback_extChartAt_symm_apply".toName
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
  logInfo m!"AXIOM_SAFETY_CONTRACT_OK:{name}:{footprint}"

run_cmd do
  let name := "extDerivFun_section_eventually_chart".toName
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
  logInfo m!"AXIOM_SAFETY_CONTRACT_OK:{name}:{footprint}"

run_cmd do
  let name := "extDerivFun_extDerivFun_chart".toName
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
  logInfo m!"AXIOM_SAFETY_CONTRACT_OK:{name}:{footprint}"

run_cmd do
  let name := "extDerivFun_apply_mlieBracket".toName
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
  logInfo m!"AXIOM_SAFETY_CONTRACT_OK:{name}:{footprint}"

run_cmd do
  let name := "mlieBracket_apply_chart_eq".toName
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
  logInfo m!"AXIOM_SAFETY_CONTRACT_OK:{name}:{footprint}"

run_cmd do
  let name := "mpullbackWithin_extChartAt_symm_self_eq".toName
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
  logInfo m!"AXIOM_SAFETY_CONTRACT_OK:{name}:{footprint}"

run_cmd do
  let name := "extDerivFun_apply_chart_eq".toName
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
  logInfo m!"AXIOM_SAFETY_CONTRACT_OK:{name}:{footprint}"

run_cmd do
  let name := "extDerivFun_apply_fixed_chart_eq".toName
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
  logInfo m!"AXIOM_SAFETY_CONTRACT_OK:{name}:{footprint}"

run_cmd do
  let name := "isLocallyConstant_of_extDerivFun_eq_zero_eq".toName
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
  logInfo m!"AXIOM_SAFETY_CONTRACT_OK:{name}:{footprint}"

run_cmd do
  let name := "extDerivFun_apply_mlieBracket_chart_eq".toName
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
  logInfo m!"AXIOM_SAFETY_CONTRACT_OK:{name}:{footprint}"

run_cmd do
  let name := "mpullback_extChartAt_symm_apply_eq".toName
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
  logInfo m!"AXIOM_SAFETY_CONTRACT_OK:{name}:{footprint}"

run_cmd do
  let name := "extDerivFun_section_eventually_chart_eq".toName
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
  logInfo m!"AXIOM_SAFETY_CONTRACT_OK:{name}:{footprint}"

run_cmd do
  let name := "extDerivFun_extDerivFun_chart_eq".toName
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
  logInfo m!"AXIOM_SAFETY_CONTRACT_OK:{name}:{footprint}"

run_cmd do
  let name := "extDerivFun_apply_mlieBracket_eq".toName
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
  logInfo m!"AXIOM_SAFETY_CONTRACT_OK:{name}:{footprint}"

run_cmd liftTermElabM do
  let info ← getConstInfo "mlieBracket_apply_chart".toName
  let levels : List Level := [Level.param "u_1".toName, Level.param "u_2".toName, Level.param "u_3".toName, Level.param "u_4".toName]
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField.{u_1} 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup.{u_2} E] [inst_2 : NormedSpace.{u_1, u_2} 𝕜 E] {H : Type u_3} [inst_3 : TopologicalSpace.{u_3} H] {I : ModelWithCorners.{u_1, u_2, u_3} 𝕜 E H} {M : Type u_4} [inst_4 : TopologicalSpace.{u_4} M] [inst_5 : ChartedSpace.{u_3, u_4} H M] [IsManifold.{u_1, u_2, u_3, u_4} I (1 : WithTop.{0} ENat) M] (X Y : (y : M) → TangentSpace.{u_2, u_1, u_3, u_4} I y) (x : M), Eq.{u_2 + 1} (VectorField.mlieBracket.{u_1, u_3, u_2, u_4} I X Y x) (VectorField.lieBracketWithin.{u_1, u_2} 𝕜 (VectorField.mpullbackWithin.{u_1, u_2, u_2, u_2, u_3, u_2, u_4} (modelWithCornersSelf.{u_1, u_2} 𝕜 E) I (↑(PartialEquiv.symm.{u_4, u_2} (extChartAt.{u_1, u_2, u_4, u_3} I x))) X (Set.range.{u_2, u_3 + 1} ↑I)) (VectorField.mpullbackWithin.{u_1, u_2, u_2, u_2, u_3, u_2, u_4} (modelWithCornersSelf.{u_1, u_2} 𝕜 E) I (↑(PartialEquiv.symm.{u_4, u_2} (extChartAt.{u_1, u_2, u_4, u_3} I x))) Y (Set.range.{u_2, u_3 + 1} ↑I)) (Set.range.{u_2, u_3 + 1} ↑I) (↑(extChartAt.{u_1, u_2, u_4, u_3} I x) x))" with
    | .ok parsedType => pure parsedType
    | .error error => throwError error
  let expected ← Term.elabType parsedType
  Term.synthesizeSyntheticMVarsNoPostponing
  let expected ← instantiateMVars expected
  if expected.hasMVar || expected.hasLevelMVar then
    throwError "unresolved metavariables in frozen type for {info.name}"
  unless ← isProp expected do
    throwError "expected frozen theorem type is not Prop for {info.name}"
  let actual := info.type.instantiateLevelParams info.levelParams levels
  unless ← isProp actual do
    throwError "actual theorem type is not Prop for {info.name}"
  unless ← isDefEq actual expected do
    throwError "frozen type mismatch for {info.name}: actual {actual}, expected {expected}"
  logInfo m!"RIGID_PROP_"∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField.{u_1} 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup.{u_2} E] [inst_2 : NormedSpace.{u_1, u_2} 𝕜 E] {H : Type u_3} [inst_3 : TopologicalSpace.{u_3} H] {I : ModelWithCorners.{u_1, u_2, u_3} 𝕜 E H} {M : Type u_4} [inst_4 : TopologicalSpace.{u_4} M] [inst_5 : ChartedSpace.{u_3, u_4} H M] [IsManifold.{u_1, u_2, u_3, u_4} I (1 : WithTop.{0} ENat) M] (X Y : (y : M) → TangentSpace.{u_2, u_1, u_3, u_4} I y) (x : M), Eq.{u_2 + 1} (VectorField.mlieBracket.{u_1, u_3, u_2, u_4} I X Y x) (VectorField.lieBracketWithin.{u_1, u_2} 𝕜 (VectorField.mpullbackWithin.{u_1, u_2, u_2, u_2, u_3, u_2, u_4} (modelWithCornersSelf.{u_1, u_2} 𝕜 E) I (↑(PartialEquiv.symm.{u_4, u_2} (extChartAt.{u_1, u_2, u_4, u_3} I x))) X (Set.range.{u_2, u_3 + 1} ↑I)) (VectorField.mpullbackWithin.{u_1, u_2, u_2, u_2, u_3, u_2, u_4} (modelWithCornersSelf.{u_1, u_2} 𝕜 E) I (↑(PartialEquiv.symm.{u_4, u_2} (extChartAt.{u_1, u_2, u_4, u_3} I x))) Y (Set.range.{u_2, u_3 + 1} ↑I)) (Set.range.{u_2, u_3 + 1} ↑I) (↑(extChartAt.{u_1, u_2, u_4, u_3} I x) x))"_CONTRACT_OK:{info.name}:{info.levelParams}"

run_cmd liftTermElabM do
  let info ← getConstInfo "mpullbackWithin_extChartAt_symm_self".toName
  let levels : List Level := [Level.param "u_1".toName, Level.param "u_2".toName, Level.param "u_3".toName, Level.param "u_4".toName]
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField.{u_1} 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup.{u_2} E] [inst_2 : NormedSpace.{u_1, u_2} 𝕜 E] {H : Type u_3} [inst_3 : TopologicalSpace.{u_3} H] {I : ModelWithCorners.{u_1, u_2, u_3} 𝕜 E H} {M : Type u_4} [inst_4 : TopologicalSpace.{u_4} M] [inst_5 : ChartedSpace.{u_3, u_4} H M] [IsManifold.{u_1, u_2, u_3, u_4} I (1 : WithTop.{0} ENat) M] (X : (y : M) → TangentSpace.{u_2, u_1, u_3, u_4} I y) (x : M), Eq.{u_2 + 1} (VectorField.mpullbackWithin.{u_1, u_2, u_2, u_2, u_3, u_2, u_4} (modelWithCornersSelf.{u_1, u_2} 𝕜 E) I (↑(PartialEquiv.symm.{u_4, u_2} (extChartAt.{u_1, u_2, u_4, u_3} I x))) X (Set.range.{u_2, u_3 + 1} ↑I) (↑(extChartAt.{u_1, u_2, u_4, u_3} I x) x)) (X x)" with
    | .ok parsedType => pure parsedType
    | .error error => throwError error
  let expected ← Term.elabType parsedType
  Term.synthesizeSyntheticMVarsNoPostponing
  let expected ← instantiateMVars expected
  if expected.hasMVar || expected.hasLevelMVar then
    throwError "unresolved metavariables in frozen type for {info.name}"
  unless ← isProp expected do
    throwError "expected frozen theorem type is not Prop for {info.name}"
  let actual := info.type.instantiateLevelParams info.levelParams levels
  unless ← isProp actual do
    throwError "actual theorem type is not Prop for {info.name}"
  unless ← isDefEq actual expected do
    throwError "frozen type mismatch for {info.name}: actual {actual}, expected {expected}"
  logInfo m!"RIGID_PROP_"∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField.{u_1} 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup.{u_2} E] [inst_2 : NormedSpace.{u_1, u_2} 𝕜 E] {H : Type u_3} [inst_3 : TopologicalSpace.{u_3} H] {I : ModelWithCorners.{u_1, u_2, u_3} 𝕜 E H} {M : Type u_4} [inst_4 : TopologicalSpace.{u_4} M] [inst_5 : ChartedSpace.{u_3, u_4} H M] [IsManifold.{u_1, u_2, u_3, u_4} I (1 : WithTop.{0} ENat) M] (X : (y : M) → TangentSpace.{u_2, u_1, u_3, u_4} I y) (x : M), Eq.{u_2 + 1} (VectorField.mpullbackWithin.{u_1, u_2, u_2, u_2, u_3, u_2, u_4} (modelWithCornersSelf.{u_1, u_2} 𝕜 E) I (↑(PartialEquiv.symm.{u_4, u_2} (extChartAt.{u_1, u_2, u_4, u_3} I x))) X (Set.range.{u_2, u_3 + 1} ↑I) (↑(extChartAt.{u_1, u_2, u_4, u_3} I x) x)) (X x)"_CONTRACT_OK:{info.name}:{info.levelParams}"

run_cmd liftTermElabM do
  let info ← getConstInfo "extDerivFun_apply_chart".toName
  let levels : List Level := [Level.param "u_1".toName, Level.param "u_2".toName, Level.param "u_3".toName, Level.param "u_4".toName]
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField.{u_1} 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup.{u_2} E] [inst_2 : NormedSpace.{u_1, u_2} 𝕜 E] {H : Type u_3} [inst_3 : TopologicalSpace.{u_3} H] {I : ModelWithCorners.{u_1, u_2, u_3} 𝕜 E H} {M : Type u_4} [inst_4 : TopologicalSpace.{u_4} M] [inst_5 : ChartedSpace.{u_3, u_4} H M] [ModelWithCorners.Boundaryless.{u_1, u_2, u_3} I] {f : M → 𝕜} {x : M}, MDifferentiableAt.{u_1, u_2, u_3, u_4, u_1, u_1, u_1} I (modelWithCornersSelf.{u_1, u_1} 𝕜 𝕜) f x → ∀ (v : TangentSpace.{u_2, u_1, u_3, u_4} I x), Eq.{u_1 + 1} (((fun (g : M → 𝕜) (z : M) => (NormedSpace.fromTangentSpace (g z)).toContinuousLinearMap.comp (mfderiv I (modelWithCornersSelf 𝕜 𝕜) g z)) f x) v) ((fderiv.{u_1, u_2, u_1} 𝕜 (Function.comp.{u_2 + 1, u_4 + 1, u_1 + 1} f ↑(PartialEquiv.symm.{u_4, u_2} (extChartAt.{u_1, u_2, u_4, u_3} I x))) (↑(extChartAt.{u_1, u_2, u_4, u_3} I x) x)) v)" with
    | .ok parsedType => pure parsedType
    | .error error => throwError error
  let expected ← Term.elabType parsedType
  Term.synthesizeSyntheticMVarsNoPostponing
  let expected ← instantiateMVars expected
  if expected.hasMVar || expected.hasLevelMVar then
    throwError "unresolved metavariables in frozen type for {info.name}"
  unless ← isProp expected do
    throwError "expected frozen theorem type is not Prop for {info.name}"
  let actual := info.type.instantiateLevelParams info.levelParams levels
  unless ← isProp actual do
    throwError "actual theorem type is not Prop for {info.name}"
  unless ← isDefEq actual expected do
    throwError "frozen type mismatch for {info.name}: actual {actual}, expected {expected}"
  logInfo m!"RIGID_PROP_"∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField.{u_1} 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup.{u_2} E] [inst_2 : NormedSpace.{u_1, u_2} 𝕜 E] {H : Type u_3} [inst_3 : TopologicalSpace.{u_3} H] {I : ModelWithCorners.{u_1, u_2, u_3} 𝕜 E H} {M : Type u_4} [inst_4 : TopologicalSpace.{u_4} M] [inst_5 : ChartedSpace.{u_3, u_4} H M] [ModelWithCorners.Boundaryless.{u_1, u_2, u_3} I] {f : M → 𝕜} {x : M}, MDifferentiableAt.{u_1, u_2, u_3, u_4, u_1, u_1, u_1} I (modelWithCornersSelf.{u_1, u_1} 𝕜 𝕜) f x → ∀ (v : TangentSpace.{u_2, u_1, u_3, u_4} I x), Eq.{u_1 + 1} (((fun (g : M → 𝕜) (z : M) => (NormedSpace.fromTangentSpace (g z)).toContinuousLinearMap.comp (mfderiv I (modelWithCornersSelf 𝕜 𝕜) g z)) f x) v) ((fderiv.{u_1, u_2, u_1} 𝕜 (Function.comp.{u_2 + 1, u_4 + 1, u_1 + 1} f ↑(PartialEquiv.symm.{u_4, u_2} (extChartAt.{u_1, u_2, u_4, u_3} I x))) (↑(extChartAt.{u_1, u_2, u_4, u_3} I x) x)) v)"_CONTRACT_OK:{info.name}:{info.levelParams}"

run_cmd liftTermElabM do
  let info ← getConstInfo "extDerivFun_apply_fixed_chart".toName
  let levels : List Level := [Level.param "u_1".toName, Level.param "u_2".toName, Level.param "u_3".toName, Level.param "u_4".toName]
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField.{u_1} 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup.{u_2} E] [inst_2 : NormedSpace.{u_1, u_2} 𝕜 E] {H : Type u_3} [inst_3 : TopologicalSpace.{u_3} H] {I : ModelWithCorners.{u_1, u_2, u_3} 𝕜 E H} {M : Type u_4} [inst_4 : TopologicalSpace.{u_4} M] [inst_5 : ChartedSpace.{u_3, u_4} H M] [IsManifold.{u_1, u_2, u_3, u_4} I (1 : WithTop.{0} ENat) M] [ModelWithCorners.Boundaryless.{u_1, u_2, u_3} I] {f : M → 𝕜} {x₀ y : M}, Membership.mem.{u_4, u_4} (PartialEquiv.source.{u_4, u_2} (extChartAt.{u_1, u_2, u_4, u_3} I x₀)) y → MDifferentiableAt.{u_1, u_2, u_3, u_4, u_1, u_1, u_1} I (modelWithCornersSelf.{u_1, u_1} 𝕜 𝕜) f y → ∀ (v : TangentSpace.{u_2, u_1, u_3, u_4} I y), Eq.{u_1 + 1} (((fun (g : M → 𝕜) (z : M) => (NormedSpace.fromTangentSpace (g z)).toContinuousLinearMap.comp (mfderiv I (modelWithCornersSelf 𝕜 𝕜) g z)) f y) v) ((fderiv.{u_1, u_2, u_1} 𝕜 (Function.comp.{u_2 + 1, u_4 + 1, u_1 + 1} f ↑(PartialEquiv.symm.{u_4, u_2} (extChartAt.{u_1, u_2, u_4, u_3} I x₀))) (↑(extChartAt.{u_1, u_2, u_4, u_3} I x₀) y)) ((mfderiv.{u_1, u_2, u_3, u_4, u_2, u_2, u_2} I (modelWithCornersSelf.{u_1, u_2} 𝕜 E) (↑(extChartAt.{u_1, u_2, u_4, u_3} I x₀)) y) v))" with
    | .ok parsedType => pure parsedType
    | .error error => throwError error
  let expected ← Term.elabType parsedType
  Term.synthesizeSyntheticMVarsNoPostponing
  let expected ← instantiateMVars expected
  if expected.hasMVar || expected.hasLevelMVar then
    throwError "unresolved metavariables in frozen type for {info.name}"
  unless ← isProp expected do
    throwError "expected frozen theorem type is not Prop for {info.name}"
  let actual := info.type.instantiateLevelParams info.levelParams levels
  unless ← isProp actual do
    throwError "actual theorem type is not Prop for {info.name}"
  unless ← isDefEq actual expected do
    throwError "frozen type mismatch for {info.name}: actual {actual}, expected {expected}"
  logInfo m!"RIGID_PROP_"∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField.{u_1} 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup.{u_2} E] [inst_2 : NormedSpace.{u_1, u_2} 𝕜 E] {H : Type u_3} [inst_3 : TopologicalSpace.{u_3} H] {I : ModelWithCorners.{u_1, u_2, u_3} 𝕜 E H} {M : Type u_4} [inst_4 : TopologicalSpace.{u_4} M] [inst_5 : ChartedSpace.{u_3, u_4} H M] [IsManifold.{u_1, u_2, u_3, u_4} I (1 : WithTop.{0} ENat) M] [ModelWithCorners.Boundaryless.{u_1, u_2, u_3} I] {f : M → 𝕜} {x₀ y : M}, Membership.mem.{u_4, u_4} (PartialEquiv.source.{u_4, u_2} (extChartAt.{u_1, u_2, u_4, u_3} I x₀)) y → MDifferentiableAt.{u_1, u_2, u_3, u_4, u_1, u_1, u_1} I (modelWithCornersSelf.{u_1, u_1} 𝕜 𝕜) f y → ∀ (v : TangentSpace.{u_2, u_1, u_3, u_4} I y), Eq.{u_1 + 1} (((fun (g : M → 𝕜) (z : M) => (NormedSpace.fromTangentSpace (g z)).toContinuousLinearMap.comp (mfderiv I (modelWithCornersSelf 𝕜 𝕜) g z)) f y) v) ((fderiv.{u_1, u_2, u_1} 𝕜 (Function.comp.{u_2 + 1, u_4 + 1, u_1 + 1} f ↑(PartialEquiv.symm.{u_4, u_2} (extChartAt.{u_1, u_2, u_4, u_3} I x₀))) (↑(extChartAt.{u_1, u_2, u_4, u_3} I x₀) y)) ((mfderiv.{u_1, u_2, u_3, u_4, u_2, u_2, u_2} I (modelWithCornersSelf.{u_1, u_2} 𝕜 E) (↑(extChartAt.{u_1, u_2, u_4, u_3} I x₀)) y) v))"_CONTRACT_OK:{info.name}:{info.levelParams}"

run_cmd liftTermElabM do
  let info ← getConstInfo "isLocallyConstant_of_extDerivFun_eq_zero".toName
  let levels : List Level := [Level.param "u_5".toName, Level.param "u_6".toName, Level.param "u_7".toName]
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "∀ {E : Type u_5} [inst : NormedAddCommGroup.{u_5} E] [inst_1 : NormedSpace.{0, u_5} Real E] {H : Type u_6} [inst_2 : TopologicalSpace.{u_6} H] {I : ModelWithCorners.{0, u_5, u_6} Real E H} {M : Type u_7} [inst_3 : TopologicalSpace.{u_7} M] [inst_4 : ChartedSpace.{u_6, u_7} H M] [IsManifold.{0, u_5, u_6, u_7} I (1 : WithTop.{0} ENat) M] [ModelWithCorners.Boundaryless.{0, u_5, u_6} I] {f : M → Real}, (∀ (x : M), MDifferentiableAt.{0, u_5, u_6, u_7, 0, 0, 0} I (modelWithCornersSelf.{0, 0} Real Real) f x) → (∀ (x : M) (w : TangentSpace.{u_5, 0, u_6, u_7} I x), Eq.{1} (((fun (g : M → Real) (z : M) => (NormedSpace.fromTangentSpace (g z)).toContinuousLinearMap.comp (mfderiv I (modelWithCornersSelf Real Real) g z)) f x) w) (0 : Real)) → IsLocallyConstant.{u_7, 0} f" with
    | .ok parsedType => pure parsedType
    | .error error => throwError error
  let expected ← Term.elabType parsedType
  Term.synthesizeSyntheticMVarsNoPostponing
  let expected ← instantiateMVars expected
  if expected.hasMVar || expected.hasLevelMVar then
    throwError "unresolved metavariables in frozen type for {info.name}"
  unless ← isProp expected do
    throwError "expected frozen theorem type is not Prop for {info.name}"
  let actual := info.type.instantiateLevelParams info.levelParams levels
  unless ← isProp actual do
    throwError "actual theorem type is not Prop for {info.name}"
  unless ← isDefEq actual expected do
    throwError "frozen type mismatch for {info.name}: actual {actual}, expected {expected}"
  logInfo m!"RIGID_PROP_"∀ {E : Type u_5} [inst : NormedAddCommGroup.{u_5} E] [inst_1 : NormedSpace.{0, u_5} Real E] {H : Type u_6} [inst_2 : TopologicalSpace.{u_6} H] {I : ModelWithCorners.{0, u_5, u_6} Real E H} {M : Type u_7} [inst_3 : TopologicalSpace.{u_7} M] [inst_4 : ChartedSpace.{u_6, u_7} H M] [IsManifold.{0, u_5, u_6, u_7} I (1 : WithTop.{0} ENat) M] [ModelWithCorners.Boundaryless.{0, u_5, u_6} I] {f : M → Real}, (∀ (x : M), MDifferentiableAt.{0, u_5, u_6, u_7, 0, 0, 0} I (modelWithCornersSelf.{0, 0} Real Real) f x) → (∀ (x : M) (w : TangentSpace.{u_5, 0, u_6, u_7} I x), Eq.{1} (((fun (g : M → Real) (z : M) => (NormedSpace.fromTangentSpace (g z)).toContinuousLinearMap.comp (mfderiv I (modelWithCornersSelf Real Real) g z)) f x) w) (0 : Real)) → IsLocallyConstant.{u_7, 0} f"_CONTRACT_OK:{info.name}:{info.levelParams}"

run_cmd liftTermElabM do
  let info ← getConstInfo "extDerivFun_apply_mlieBracket_chart".toName
  let levels : List Level := [Level.param "u_5".toName, Level.param "u_6".toName, Level.param "u_7".toName]
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "∀ {E' : Type u_5} [inst : NormedAddCommGroup.{u_5} E'] [inst_1 : NormedSpace.{0, u_5} Real E'] {H' : Type u_6} [inst_2 : TopologicalSpace.{u_6} H'] {I' : ModelWithCorners.{0, u_5, u_6} Real E' H'} {N : Type u_7} [inst_3 : TopologicalSpace.{u_7} N] [inst_4 : ChartedSpace.{u_6, u_7} H' N] [inst_5 : IsManifold.{0, u_5, u_6, u_7} I' (2 : WithTop.{0} ENat) N] [ModelWithCorners.Boundaryless.{0, u_5, u_6} I'] [CompleteSpace.{u_5} E'] {f : N → Real} {X Y : (y : N) → TangentSpace.{u_5, 0, u_6, u_7} I' y} {x : N}, ContMDiffAt.{0, u_5, u_6, u_7, 0, 0, 0} I' (modelWithCornersSelf.{0, 0} Real Real) (2 : WithTop.{0} ENat) f x → MDifferentiableAt.{0, u_5, u_6, u_7, u_5, max u_5 u_6, max u_5 u_7} I' (ModelWithCorners.prod.{0, u_5, u_6, u_5, u_5} I' (modelWithCornersSelf.{0, u_5} Real E')) (fun (y : N) => Bundle.TotalSpace.mk'.{u_7, u_5, u_5} E' y (X y)) x → MDifferentiableAt.{0, u_5, u_6, u_7, u_5, max u_5 u_6, max u_5 u_7} I' (ModelWithCorners.prod.{0, u_5, u_6, u_5, u_5} I' (modelWithCornersSelf.{0, u_5} Real E')) (fun (y : N) => Bundle.TotalSpace.mk'.{u_7, u_5, u_5} E' y (Y y)) x → Eq.{1} (((fun (g : N → Real) (z : N) => (NormedSpace.fromTangentSpace (g z)).toContinuousLinearMap.comp (mfderiv I' (modelWithCornersSelf Real Real) g z)) f x) (VectorField.mlieBracket.{0, u_6, u_5, u_7} I' X Y x)) (HSub.hSub.{0, 0, 0} ((fderiv.{0, u_5, 0} Real (fun (z : E') => (fderiv.{0, u_5, 0} Real (Function.comp.{u_5 + 1, u_7 + 1, 1} f ↑(PartialEquiv.symm.{u_7, u_5} (extChartAt.{0, u_5, u_7, u_6} I' x))) z) (VectorField.mpullback.{0, u_5, u_5, u_5, u_6, u_5, u_7} (modelWithCornersSelf.{0, u_5} Real E') I' (↑(PartialEquiv.symm.{u_7, u_5} (extChartAt.{0, u_5, u_7, u_6} I' x))) Y z)) (↑(extChartAt.{0, u_5, u_7, u_6} I' x) x)) (X x)) ((fderiv.{0, u_5, 0} Real (fun (z : E') => (fderiv.{0, u_5, 0} Real (Function.comp.{u_5 + 1, u_7 + 1, 1} f ↑(PartialEquiv.symm.{u_7, u_5} (extChartAt.{0, u_5, u_7, u_6} I' x))) z) (VectorField.mpullback.{0, u_5, u_5, u_5, u_6, u_5, u_7} (modelWithCornersSelf.{0, u_5} Real E') I' (↑(PartialEquiv.symm.{u_7, u_5} (extChartAt.{0, u_5, u_7, u_6} I' x))) X z)) (↑(extChartAt.{0, u_5, u_7, u_6} I' x) x)) (Y x)))" with
    | .ok parsedType => pure parsedType
    | .error error => throwError error
  let expected ← Term.elabType parsedType
  Term.synthesizeSyntheticMVarsNoPostponing
  let expected ← instantiateMVars expected
  if expected.hasMVar || expected.hasLevelMVar then
    throwError "unresolved metavariables in frozen type for {info.name}"
  unless ← isProp expected do
    throwError "expected frozen theorem type is not Prop for {info.name}"
  let actual := info.type.instantiateLevelParams info.levelParams levels
  unless ← isProp actual do
    throwError "actual theorem type is not Prop for {info.name}"
  unless ← isDefEq actual expected do
    throwError "frozen type mismatch for {info.name}: actual {actual}, expected {expected}"
  logInfo m!"RIGID_PROP_"∀ {E' : Type u_5} [inst : NormedAddCommGroup.{u_5} E'] [inst_1 : NormedSpace.{0, u_5} Real E'] {H' : Type u_6} [inst_2 : TopologicalSpace.{u_6} H'] {I' : ModelWithCorners.{0, u_5, u_6} Real E' H'} {N : Type u_7} [inst_3 : TopologicalSpace.{u_7} N] [inst_4 : ChartedSpace.{u_6, u_7} H' N] [inst_5 : IsManifold.{0, u_5, u_6, u_7} I' (2 : WithTop.{0} ENat) N] [ModelWithCorners.Boundaryless.{0, u_5, u_6} I'] [CompleteSpace.{u_5} E'] {f : N → Real} {X Y : (y : N) → TangentSpace.{u_5, 0, u_6, u_7} I' y} {x : N}, ContMDiffAt.{0, u_5, u_6, u_7, 0, 0, 0} I' (modelWithCornersSelf.{0, 0} Real Real) (2 : WithTop.{0} ENat) f x → MDifferentiableAt.{0, u_5, u_6, u_7, u_5, max u_5 u_6, max u_5 u_7} I' (ModelWithCorners.prod.{0, u_5, u_6, u_5, u_5} I' (modelWithCornersSelf.{0, u_5} Real E')) (fun (y : N) => Bundle.TotalSpace.mk'.{u_7, u_5, u_5} E' y (X y)) x → MDifferentiableAt.{0, u_5, u_6, u_7, u_5, max u_5 u_6, max u_5 u_7} I' (ModelWithCorners.prod.{0, u_5, u_6, u_5, u_5} I' (modelWithCornersSelf.{0, u_5} Real E')) (fun (y : N) => Bundle.TotalSpace.mk'.{u_7, u_5, u_5} E' y (Y y)) x → Eq.{1} (((fun (g : N → Real) (z : N) => (NormedSpace.fromTangentSpace (g z)).toContinuousLinearMap.comp (mfderiv I' (modelWithCornersSelf Real Real) g z)) f x) (VectorField.mlieBracket.{0, u_6, u_5, u_7} I' X Y x)) (HSub.hSub.{0, 0, 0} ((fderiv.{0, u_5, 0} Real (fun (z : E') => (fderiv.{0, u_5, 0} Real (Function.comp.{u_5 + 1, u_7 + 1, 1} f ↑(PartialEquiv.symm.{u_7, u_5} (extChartAt.{0, u_5, u_7, u_6} I' x))) z) (VectorField.mpullback.{0, u_5, u_5, u_5, u_6, u_5, u_7} (modelWithCornersSelf.{0, u_5} Real E') I' (↑(PartialEquiv.symm.{u_7, u_5} (extChartAt.{0, u_5, u_7, u_6} I' x))) Y z)) (↑(extChartAt.{0, u_5, u_7, u_6} I' x) x)) (X x)) ((fderiv.{0, u_5, 0} Real (fun (z : E') => (fderiv.{0, u_5, 0} Real (Function.comp.{u_5 + 1, u_7 + 1, 1} f ↑(PartialEquiv.symm.{u_7, u_5} (extChartAt.{0, u_5, u_7, u_6} I' x))) z) (VectorField.mpullback.{0, u_5, u_5, u_5, u_6, u_5, u_7} (modelWithCornersSelf.{0, u_5} Real E') I' (↑(PartialEquiv.symm.{u_7, u_5} (extChartAt.{0, u_5, u_7, u_6} I' x))) X z)) (↑(extChartAt.{0, u_5, u_7, u_6} I' x) x)) (Y x)))"_CONTRACT_OK:{info.name}:{info.levelParams}"

run_cmd liftTermElabM do
  let info ← getConstInfo "mpullback_extChartAt_symm_apply".toName
  let levels : List Level := [Level.param "u_5".toName, Level.param "u_6".toName, Level.param "u_7".toName]
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "∀ {E' : Type u_5} [inst : NormedAddCommGroup.{u_5} E'] [inst_1 : NormedSpace.{0, u_5} Real E'] {H' : Type u_6} [inst_2 : TopologicalSpace.{u_6} H'] {I' : ModelWithCorners.{0, u_5, u_6} Real E' H'} {N : Type u_7} [inst_3 : TopologicalSpace.{u_7} N] [inst_4 : ChartedSpace.{u_6, u_7} H' N] [IsManifold.{0, u_5, u_6, u_7} I' (2 : WithTop.{0} ENat) N] [ModelWithCorners.Boundaryless.{0, u_5, u_6} I'] [CompleteSpace.{u_5} E'] {x y : N}, Membership.mem.{u_7, u_7} (PartialEquiv.source.{u_7, u_5} (extChartAt.{0, u_5, u_7, u_6} I' x)) y → ∀ (U : (z : N) → TangentSpace.{u_5, 0, u_6, u_7} I' z), Eq.{u_5 + 1} (VectorField.mpullback.{0, u_5, u_5, u_5, u_6, u_5, u_7} (modelWithCornersSelf.{0, u_5} Real E') I' (↑(PartialEquiv.symm.{u_7, u_5} (extChartAt.{0, u_5, u_7, u_6} I' x))) U (↑(extChartAt.{0, u_5, u_7, u_6} I' x) y)) ((mfderiv.{0, u_5, u_6, u_7, u_5, u_5, u_5} I' (modelWithCornersSelf.{0, u_5} Real E') (↑(extChartAt.{0, u_5, u_7, u_6} I' x)) y) (U y))" with
    | .ok parsedType => pure parsedType
    | .error error => throwError error
  let expected ← Term.elabType parsedType
  Term.synthesizeSyntheticMVarsNoPostponing
  let expected ← instantiateMVars expected
  if expected.hasMVar || expected.hasLevelMVar then
    throwError "unresolved metavariables in frozen type for {info.name}"
  unless ← isProp expected do
    throwError "expected frozen theorem type is not Prop for {info.name}"
  let actual := info.type.instantiateLevelParams info.levelParams levels
  unless ← isProp actual do
    throwError "actual theorem type is not Prop for {info.name}"
  unless ← isDefEq actual expected do
    throwError "frozen type mismatch for {info.name}: actual {actual}, expected {expected}"
  logInfo m!"RIGID_PROP_"∀ {E' : Type u_5} [inst : NormedAddCommGroup.{u_5} E'] [inst_1 : NormedSpace.{0, u_5} Real E'] {H' : Type u_6} [inst_2 : TopologicalSpace.{u_6} H'] {I' : ModelWithCorners.{0, u_5, u_6} Real E' H'} {N : Type u_7} [inst_3 : TopologicalSpace.{u_7} N] [inst_4 : ChartedSpace.{u_6, u_7} H' N] [IsManifold.{0, u_5, u_6, u_7} I' (2 : WithTop.{0} ENat) N] [ModelWithCorners.Boundaryless.{0, u_5, u_6} I'] [CompleteSpace.{u_5} E'] {x y : N}, Membership.mem.{u_7, u_7} (PartialEquiv.source.{u_7, u_5} (extChartAt.{0, u_5, u_7, u_6} I' x)) y → ∀ (U : (z : N) → TangentSpace.{u_5, 0, u_6, u_7} I' z), Eq.{u_5 + 1} (VectorField.mpullback.{0, u_5, u_5, u_5, u_6, u_5, u_7} (modelWithCornersSelf.{0, u_5} Real E') I' (↑(PartialEquiv.symm.{u_7, u_5} (extChartAt.{0, u_5, u_7, u_6} I' x))) U (↑(extChartAt.{0, u_5, u_7, u_6} I' x) y)) ((mfderiv.{0, u_5, u_6, u_7, u_5, u_5, u_5} I' (modelWithCornersSelf.{0, u_5} Real E') (↑(extChartAt.{0, u_5, u_7, u_6} I' x)) y) (U y))"_CONTRACT_OK:{info.name}:{info.levelParams}"

run_cmd liftTermElabM do
  let info ← getConstInfo "extDerivFun_section_eventually_chart".toName
  let levels : List Level := [Level.param "u_5".toName, Level.param "u_6".toName, Level.param "u_7".toName]
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "∀ {E' : Type u_5} [inst : NormedAddCommGroup.{u_5} E'] [inst_1 : NormedSpace.{0, u_5} Real E'] {H' : Type u_6} [inst_2 : TopologicalSpace.{u_6} H'] {I' : ModelWithCorners.{0, u_5, u_6} Real E' H'} {N : Type u_7} [inst_3 : TopologicalSpace.{u_7} N] [inst_4 : ChartedSpace.{u_6, u_7} H' N] [IsManifold.{0, u_5, u_6, u_7} I' (2 : WithTop.{0} ENat) N] [ModelWithCorners.Boundaryless.{0, u_5, u_6} I'] [CompleteSpace.{u_5} E'] {f : N → Real} {x : N}, ContMDiffAt.{0, u_5, u_6, u_7, 0, 0, 0} I' (modelWithCornersSelf.{0, 0} Real Real) (2 : WithTop.{0} ENat) f x → ∀ (U : (z : N) → TangentSpace.{u_5, 0, u_6, u_7} I' z), Filter.Eventually.{u_7} (fun (y : N) => Eq.{1} (((fun (g : N → Real) (z : N) => (NormedSpace.fromTangentSpace (g z)).toContinuousLinearMap.comp (mfderiv I' (modelWithCornersSelf Real Real) g z)) f y) (U y)) ((fderiv.{0, u_5, 0} Real (Function.comp.{u_5 + 1, u_7 + 1, 1} f ↑(PartialEquiv.symm.{u_7, u_5} (extChartAt.{0, u_5, u_7, u_6} I' x))) (↑(extChartAt.{0, u_5, u_7, u_6} I' x) y)) (VectorField.mpullback.{0, u_5, u_5, u_5, u_6, u_5, u_7} (modelWithCornersSelf.{0, u_5} Real E') I' (↑(PartialEquiv.symm.{u_7, u_5} (extChartAt.{0, u_5, u_7, u_6} I' x))) U (↑(extChartAt.{0, u_5, u_7, u_6} I' x) y)))) (nhds.{u_7} x)" with
    | .ok parsedType => pure parsedType
    | .error error => throwError error
  let expected ← Term.elabType parsedType
  Term.synthesizeSyntheticMVarsNoPostponing
  let expected ← instantiateMVars expected
  if expected.hasMVar || expected.hasLevelMVar then
    throwError "unresolved metavariables in frozen type for {info.name}"
  unless ← isProp expected do
    throwError "expected frozen theorem type is not Prop for {info.name}"
  let actual := info.type.instantiateLevelParams info.levelParams levels
  unless ← isProp actual do
    throwError "actual theorem type is not Prop for {info.name}"
  unless ← isDefEq actual expected do
    throwError "frozen type mismatch for {info.name}: actual {actual}, expected {expected}"
  logInfo m!"RIGID_PROP_"∀ {E' : Type u_5} [inst : NormedAddCommGroup.{u_5} E'] [inst_1 : NormedSpace.{0, u_5} Real E'] {H' : Type u_6} [inst_2 : TopologicalSpace.{u_6} H'] {I' : ModelWithCorners.{0, u_5, u_6} Real E' H'} {N : Type u_7} [inst_3 : TopologicalSpace.{u_7} N] [inst_4 : ChartedSpace.{u_6, u_7} H' N] [IsManifold.{0, u_5, u_6, u_7} I' (2 : WithTop.{0} ENat) N] [ModelWithCorners.Boundaryless.{0, u_5, u_6} I'] [CompleteSpace.{u_5} E'] {f : N → Real} {x : N}, ContMDiffAt.{0, u_5, u_6, u_7, 0, 0, 0} I' (modelWithCornersSelf.{0, 0} Real Real) (2 : WithTop.{0} ENat) f x → ∀ (U : (z : N) → TangentSpace.{u_5, 0, u_6, u_7} I' z), Filter.Eventually.{u_7} (fun (y : N) => Eq.{1} (((fun (g : N → Real) (z : N) => (NormedSpace.fromTangentSpace (g z)).toContinuousLinearMap.comp (mfderiv I' (modelWithCornersSelf Real Real) g z)) f y) (U y)) ((fderiv.{0, u_5, 0} Real (Function.comp.{u_5 + 1, u_7 + 1, 1} f ↑(PartialEquiv.symm.{u_7, u_5} (extChartAt.{0, u_5, u_7, u_6} I' x))) (↑(extChartAt.{0, u_5, u_7, u_6} I' x) y)) (VectorField.mpullback.{0, u_5, u_5, u_5, u_6, u_5, u_7} (modelWithCornersSelf.{0, u_5} Real E') I' (↑(PartialEquiv.symm.{u_7, u_5} (extChartAt.{0, u_5, u_7, u_6} I' x))) U (↑(extChartAt.{0, u_5, u_7, u_6} I' x) y)))) (nhds.{u_7} x)"_CONTRACT_OK:{info.name}:{info.levelParams}"

run_cmd liftTermElabM do
  let info ← getConstInfo "extDerivFun_extDerivFun_chart".toName
  let levels : List Level := [Level.param "u_5".toName, Level.param "u_6".toName, Level.param "u_7".toName]
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "∀ {E' : Type u_5} [inst : NormedAddCommGroup.{u_5} E'] [inst_1 : NormedSpace.{0, u_5} Real E'] {H' : Type u_6} [inst_2 : TopologicalSpace.{u_6} H'] {I' : ModelWithCorners.{0, u_5, u_6} Real E' H'} {N : Type u_7} [inst_3 : TopologicalSpace.{u_7} N] [inst_4 : ChartedSpace.{u_6, u_7} H' N] [inst_5 : IsManifold.{0, u_5, u_6, u_7} I' (2 : WithTop.{0} ENat) N] [ModelWithCorners.Boundaryless.{0, u_5, u_6} I'] [CompleteSpace.{u_5} E'] {f : N → Real} {U : (y : N) → TangentSpace.{u_5, 0, u_6, u_7} I' y} {x : N}, ContMDiffAt.{0, u_5, u_6, u_7, 0, 0, 0} I' (modelWithCornersSelf.{0, 0} Real Real) (2 : WithTop.{0} ENat) f x → MDifferentiableAt.{0, u_5, u_6, u_7, u_5, max u_5 u_6, max u_5 u_7} I' (ModelWithCorners.prod.{0, u_5, u_6, u_5, u_5} I' (modelWithCornersSelf.{0, u_5} Real E')) (fun (y : N) => Bundle.TotalSpace.mk'.{u_7, u_5, u_5} E' y (U y)) x → ∀ (v : TangentSpace.{u_5, 0, u_6, u_7} I' x), Eq.{1} (((fun (g : N → Real) (z : N) => (NormedSpace.fromTangentSpace (g z)).toContinuousLinearMap.comp (mfderiv I' (modelWithCornersSelf Real Real) g z)) (fun (y : N) => ((fun (g : N → Real) (z : N) => (NormedSpace.fromTangentSpace (g z)).toContinuousLinearMap.comp (mfderiv I' (modelWithCornersSelf Real Real) g z)) f y) (U y)) x) v) ((fderiv.{0, u_5, 0} Real (fun (z : E') => (fderiv.{0, u_5, 0} Real (Function.comp.{u_5 + 1, u_7 + 1, 1} f ↑(PartialEquiv.symm.{u_7, u_5} (extChartAt.{0, u_5, u_7, u_6} I' x))) z) (VectorField.mpullback.{0, u_5, u_5, u_5, u_6, u_5, u_7} (modelWithCornersSelf.{0, u_5} Real E') I' (↑(PartialEquiv.symm.{u_7, u_5} (extChartAt.{0, u_5, u_7, u_6} I' x))) U z)) (↑(extChartAt.{0, u_5, u_7, u_6} I' x) x)) v)" with
    | .ok parsedType => pure parsedType
    | .error error => throwError error
  let expected ← Term.elabType parsedType
  Term.synthesizeSyntheticMVarsNoPostponing
  let expected ← instantiateMVars expected
  if expected.hasMVar || expected.hasLevelMVar then
    throwError "unresolved metavariables in frozen type for {info.name}"
  unless ← isProp expected do
    throwError "expected frozen theorem type is not Prop for {info.name}"
  let actual := info.type.instantiateLevelParams info.levelParams levels
  unless ← isProp actual do
    throwError "actual theorem type is not Prop for {info.name}"
  unless ← isDefEq actual expected do
    throwError "frozen type mismatch for {info.name}: actual {actual}, expected {expected}"
  logInfo m!"RIGID_PROP_"∀ {E' : Type u_5} [inst : NormedAddCommGroup.{u_5} E'] [inst_1 : NormedSpace.{0, u_5} Real E'] {H' : Type u_6} [inst_2 : TopologicalSpace.{u_6} H'] {I' : ModelWithCorners.{0, u_5, u_6} Real E' H'} {N : Type u_7} [inst_3 : TopologicalSpace.{u_7} N] [inst_4 : ChartedSpace.{u_6, u_7} H' N] [inst_5 : IsManifold.{0, u_5, u_6, u_7} I' (2 : WithTop.{0} ENat) N] [ModelWithCorners.Boundaryless.{0, u_5, u_6} I'] [CompleteSpace.{u_5} E'] {f : N → Real} {U : (y : N) → TangentSpace.{u_5, 0, u_6, u_7} I' y} {x : N}, ContMDiffAt.{0, u_5, u_6, u_7, 0, 0, 0} I' (modelWithCornersSelf.{0, 0} Real Real) (2 : WithTop.{0} ENat) f x → MDifferentiableAt.{0, u_5, u_6, u_7, u_5, max u_5 u_6, max u_5 u_7} I' (ModelWithCorners.prod.{0, u_5, u_6, u_5, u_5} I' (modelWithCornersSelf.{0, u_5} Real E')) (fun (y : N) => Bundle.TotalSpace.mk'.{u_7, u_5, u_5} E' y (U y)) x → ∀ (v : TangentSpace.{u_5, 0, u_6, u_7} I' x), Eq.{1} (((fun (g : N → Real) (z : N) => (NormedSpace.fromTangentSpace (g z)).toContinuousLinearMap.comp (mfderiv I' (modelWithCornersSelf Real Real) g z)) (fun (y : N) => ((fun (g : N → Real) (z : N) => (NormedSpace.fromTangentSpace (g z)).toContinuousLinearMap.comp (mfderiv I' (modelWithCornersSelf Real Real) g z)) f y) (U y)) x) v) ((fderiv.{0, u_5, 0} Real (fun (z : E') => (fderiv.{0, u_5, 0} Real (Function.comp.{u_5 + 1, u_7 + 1, 1} f ↑(PartialEquiv.symm.{u_7, u_5} (extChartAt.{0, u_5, u_7, u_6} I' x))) z) (VectorField.mpullback.{0, u_5, u_5, u_5, u_6, u_5, u_7} (modelWithCornersSelf.{0, u_5} Real E') I' (↑(PartialEquiv.symm.{u_7, u_5} (extChartAt.{0, u_5, u_7, u_6} I' x))) U z)) (↑(extChartAt.{0, u_5, u_7, u_6} I' x) x)) v)"_CONTRACT_OK:{info.name}:{info.levelParams}"

run_cmd liftTermElabM do
  let info ← getConstInfo "extDerivFun_apply_mlieBracket".toName
  let levels : List Level := [Level.param "u_5".toName, Level.param "u_6".toName, Level.param "u_7".toName]
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "∀ {E' : Type u_5} [inst : NormedAddCommGroup.{u_5} E'] [inst_1 : NormedSpace.{0, u_5} Real E'] {H' : Type u_6} [inst_2 : TopologicalSpace.{u_6} H'] {I' : ModelWithCorners.{0, u_5, u_6} Real E' H'} {N : Type u_7} [inst_3 : TopologicalSpace.{u_7} N] [inst_4 : ChartedSpace.{u_6, u_7} H' N] [inst_5 : IsManifold.{0, u_5, u_6, u_7} I' (2 : WithTop.{0} ENat) N] [ModelWithCorners.Boundaryless.{0, u_5, u_6} I'] [CompleteSpace.{u_5} E'] {f : N → Real} {X Y : (y : N) → TangentSpace.{u_5, 0, u_6, u_7} I' y} {x : N}, ContMDiffAt.{0, u_5, u_6, u_7, 0, 0, 0} I' (modelWithCornersSelf.{0, 0} Real Real) (2 : WithTop.{0} ENat) f x → MDifferentiableAt.{0, u_5, u_6, u_7, u_5, max u_5 u_6, max u_5 u_7} I' (ModelWithCorners.prod.{0, u_5, u_6, u_5, u_5} I' (modelWithCornersSelf.{0, u_5} Real E')) (fun (y : N) => Bundle.TotalSpace.mk'.{u_7, u_5, u_5} E' y (X y)) x → MDifferentiableAt.{0, u_5, u_6, u_7, u_5, max u_5 u_6, max u_5 u_7} I' (ModelWithCorners.prod.{0, u_5, u_6, u_5, u_5} I' (modelWithCornersSelf.{0, u_5} Real E')) (fun (y : N) => Bundle.TotalSpace.mk'.{u_7, u_5, u_5} E' y (Y y)) x → Eq.{1} (((fun (g : N → Real) (z : N) => (NormedSpace.fromTangentSpace (g z)).toContinuousLinearMap.comp (mfderiv I' (modelWithCornersSelf Real Real) g z)) f x) (VectorField.mlieBracket.{0, u_6, u_5, u_7} I' X Y x)) (HSub.hSub.{0, 0, 0} (((fun (g : N → Real) (z : N) => (NormedSpace.fromTangentSpace (g z)).toContinuousLinearMap.comp (mfderiv I' (modelWithCornersSelf Real Real) g z)) (fun (y : N) => ((fun (g : N → Real) (z : N) => (NormedSpace.fromTangentSpace (g z)).toContinuousLinearMap.comp (mfderiv I' (modelWithCornersSelf Real Real) g z)) f y) (Y y)) x) (X x)) (((fun (g : N → Real) (z : N) => (NormedSpace.fromTangentSpace (g z)).toContinuousLinearMap.comp (mfderiv I' (modelWithCornersSelf Real Real) g z)) (fun (y : N) => ((fun (g : N → Real) (z : N) => (NormedSpace.fromTangentSpace (g z)).toContinuousLinearMap.comp (mfderiv I' (modelWithCornersSelf Real Real) g z)) f y) (X y)) x) (Y x)))" with
    | .ok parsedType => pure parsedType
    | .error error => throwError error
  let expected ← Term.elabType parsedType
  Term.synthesizeSyntheticMVarsNoPostponing
  let expected ← instantiateMVars expected
  if expected.hasMVar || expected.hasLevelMVar then
    throwError "unresolved metavariables in frozen type for {info.name}"
  unless ← isProp expected do
    throwError "expected frozen theorem type is not Prop for {info.name}"
  let actual := info.type.instantiateLevelParams info.levelParams levels
  unless ← isProp actual do
    throwError "actual theorem type is not Prop for {info.name}"
  unless ← isDefEq actual expected do
    throwError "frozen type mismatch for {info.name}: actual {actual}, expected {expected}"
  logInfo m!"RIGID_PROP_"∀ {E' : Type u_5} [inst : NormedAddCommGroup.{u_5} E'] [inst_1 : NormedSpace.{0, u_5} Real E'] {H' : Type u_6} [inst_2 : TopologicalSpace.{u_6} H'] {I' : ModelWithCorners.{0, u_5, u_6} Real E' H'} {N : Type u_7} [inst_3 : TopologicalSpace.{u_7} N] [inst_4 : ChartedSpace.{u_6, u_7} H' N] [inst_5 : IsManifold.{0, u_5, u_6, u_7} I' (2 : WithTop.{0} ENat) N] [ModelWithCorners.Boundaryless.{0, u_5, u_6} I'] [CompleteSpace.{u_5} E'] {f : N → Real} {X Y : (y : N) → TangentSpace.{u_5, 0, u_6, u_7} I' y} {x : N}, ContMDiffAt.{0, u_5, u_6, u_7, 0, 0, 0} I' (modelWithCornersSelf.{0, 0} Real Real) (2 : WithTop.{0} ENat) f x → MDifferentiableAt.{0, u_5, u_6, u_7, u_5, max u_5 u_6, max u_5 u_7} I' (ModelWithCorners.prod.{0, u_5, u_6, u_5, u_5} I' (modelWithCornersSelf.{0, u_5} Real E')) (fun (y : N) => Bundle.TotalSpace.mk'.{u_7, u_5, u_5} E' y (X y)) x → MDifferentiableAt.{0, u_5, u_6, u_7, u_5, max u_5 u_6, max u_5 u_7} I' (ModelWithCorners.prod.{0, u_5, u_6, u_5, u_5} I' (modelWithCornersSelf.{0, u_5} Real E')) (fun (y : N) => Bundle.TotalSpace.mk'.{u_7, u_5, u_5} E' y (Y y)) x → Eq.{1} (((fun (g : N → Real) (z : N) => (NormedSpace.fromTangentSpace (g z)).toContinuousLinearMap.comp (mfderiv I' (modelWithCornersSelf Real Real) g z)) f x) (VectorField.mlieBracket.{0, u_6, u_5, u_7} I' X Y x)) (HSub.hSub.{0, 0, 0} (((fun (g : N → Real) (z : N) => (NormedSpace.fromTangentSpace (g z)).toContinuousLinearMap.comp (mfderiv I' (modelWithCornersSelf Real Real) g z)) (fun (y : N) => ((fun (g : N → Real) (z : N) => (NormedSpace.fromTangentSpace (g z)).toContinuousLinearMap.comp (mfderiv I' (modelWithCornersSelf Real Real) g z)) f y) (Y y)) x) (X x)) (((fun (g : N → Real) (z : N) => (NormedSpace.fromTangentSpace (g z)).toContinuousLinearMap.comp (mfderiv I' (modelWithCornersSelf Real Real) g z)) (fun (y : N) => ((fun (g : N → Real) (z : N) => (NormedSpace.fromTangentSpace (g z)).toContinuousLinearMap.comp (mfderiv I' (modelWithCornersSelf Real Real) g z)) f y) (X y)) x) (Y x)))"_CONTRACT_OK:{info.name}:{info.levelParams}"

run_cmd liftTermElabM do
  let info ← getConstInfo "mlieBracket_apply_chart_eq".toName
  let levels : List Level := [Level.param "u_5".toName, Level.param "u_6".toName, Level.param "u_7".toName, Level.param "u_8".toName]
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "Eq.{0} @mlieBracket_apply_chart.{u_5, u_6, u_7, u_8} @mlieBracket_apply_chart.{u_5, u_6, u_7, u_8}" with
    | .ok parsedType => pure parsedType
    | .error error => throwError error
  let expected ← Term.elabType parsedType
  Term.synthesizeSyntheticMVarsNoPostponing
  let expected ← instantiateMVars expected
  if expected.hasMVar || expected.hasLevelMVar then
    throwError "unresolved metavariables in frozen type for {info.name}"
  unless ← isProp expected do
    throwError "expected frozen theorem type is not Prop for {info.name}"
  let actual := info.type.instantiateLevelParams info.levelParams levels
  unless ← isProp actual do
    throwError "actual theorem type is not Prop for {info.name}"
  unless ← isDefEq actual expected do
    throwError "frozen type mismatch for {info.name}: actual {actual}, expected {expected}"
  logInfo m!"RIGID_PROP_"Eq.{0} @mlieBracket_apply_chart.{u_5, u_6, u_7, u_8} @mlieBracket_apply_chart.{u_5, u_6, u_7, u_8}"_CONTRACT_OK:{info.name}:{info.levelParams}"

run_cmd liftTermElabM do
  let info ← getConstInfo "mpullbackWithin_extChartAt_symm_self_eq".toName
  let levels : List Level := [Level.param "u_5".toName, Level.param "u_6".toName, Level.param "u_7".toName, Level.param "u_8".toName]
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "Eq.{0} @mpullbackWithin_extChartAt_symm_self.{u_5, u_6, u_7, u_8} @mpullbackWithin_extChartAt_symm_self.{u_5, u_6, u_7, u_8}" with
    | .ok parsedType => pure parsedType
    | .error error => throwError error
  let expected ← Term.elabType parsedType
  Term.synthesizeSyntheticMVarsNoPostponing
  let expected ← instantiateMVars expected
  if expected.hasMVar || expected.hasLevelMVar then
    throwError "unresolved metavariables in frozen type for {info.name}"
  unless ← isProp expected do
    throwError "expected frozen theorem type is not Prop for {info.name}"
  let actual := info.type.instantiateLevelParams info.levelParams levels
  unless ← isProp actual do
    throwError "actual theorem type is not Prop for {info.name}"
  unless ← isDefEq actual expected do
    throwError "frozen type mismatch for {info.name}: actual {actual}, expected {expected}"
  logInfo m!"RIGID_PROP_"Eq.{0} @mpullbackWithin_extChartAt_symm_self.{u_5, u_6, u_7, u_8} @mpullbackWithin_extChartAt_symm_self.{u_5, u_6, u_7, u_8}"_CONTRACT_OK:{info.name}:{info.levelParams}"

run_cmd liftTermElabM do
  let info ← getConstInfo "extDerivFun_apply_chart_eq".toName
  let levels : List Level := [Level.param "u_5".toName, Level.param "u_6".toName, Level.param "u_7".toName, Level.param "u_8".toName]
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "Eq.{0} @extDerivFun_apply_chart.{u_5, u_6, u_7, u_8} @extDerivFun_apply_chart.{u_5, u_6, u_7, u_8}" with
    | .ok parsedType => pure parsedType
    | .error error => throwError error
  let expected ← Term.elabType parsedType
  Term.synthesizeSyntheticMVarsNoPostponing
  let expected ← instantiateMVars expected
  if expected.hasMVar || expected.hasLevelMVar then
    throwError "unresolved metavariables in frozen type for {info.name}"
  unless ← isProp expected do
    throwError "expected frozen theorem type is not Prop for {info.name}"
  let actual := info.type.instantiateLevelParams info.levelParams levels
  unless ← isProp actual do
    throwError "actual theorem type is not Prop for {info.name}"
  unless ← isDefEq actual expected do
    throwError "frozen type mismatch for {info.name}: actual {actual}, expected {expected}"
  logInfo m!"RIGID_PROP_"Eq.{0} @extDerivFun_apply_chart.{u_5, u_6, u_7, u_8} @extDerivFun_apply_chart.{u_5, u_6, u_7, u_8}"_CONTRACT_OK:{info.name}:{info.levelParams}"

run_cmd liftTermElabM do
  let info ← getConstInfo "extDerivFun_apply_fixed_chart_eq".toName
  let levels : List Level := [Level.param "u_5".toName, Level.param "u_6".toName, Level.param "u_7".toName, Level.param "u_8".toName]
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "Eq.{0} @extDerivFun_apply_fixed_chart.{u_5, u_6, u_7, u_8} @extDerivFun_apply_fixed_chart.{u_5, u_6, u_7, u_8}" with
    | .ok parsedType => pure parsedType
    | .error error => throwError error
  let expected ← Term.elabType parsedType
  Term.synthesizeSyntheticMVarsNoPostponing
  let expected ← instantiateMVars expected
  if expected.hasMVar || expected.hasLevelMVar then
    throwError "unresolved metavariables in frozen type for {info.name}"
  unless ← isProp expected do
    throwError "expected frozen theorem type is not Prop for {info.name}"
  let actual := info.type.instantiateLevelParams info.levelParams levels
  unless ← isProp actual do
    throwError "actual theorem type is not Prop for {info.name}"
  unless ← isDefEq actual expected do
    throwError "frozen type mismatch for {info.name}: actual {actual}, expected {expected}"
  logInfo m!"RIGID_PROP_"Eq.{0} @extDerivFun_apply_fixed_chart.{u_5, u_6, u_7, u_8} @extDerivFun_apply_fixed_chart.{u_5, u_6, u_7, u_8}"_CONTRACT_OK:{info.name}:{info.levelParams}"

run_cmd liftTermElabM do
  let info ← getConstInfo "isLocallyConstant_of_extDerivFun_eq_zero_eq".toName
  let levels : List Level := [Level.param "u_5".toName, Level.param "u_6".toName, Level.param "u_7".toName]
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "Eq.{0} @isLocallyConstant_of_extDerivFun_eq_zero.{u_5, u_6, u_7} @isLocallyConstant_of_extDerivFun_eq_zero.{u_5, u_6, u_7}" with
    | .ok parsedType => pure parsedType
    | .error error => throwError error
  let expected ← Term.elabType parsedType
  Term.synthesizeSyntheticMVarsNoPostponing
  let expected ← instantiateMVars expected
  if expected.hasMVar || expected.hasLevelMVar then
    throwError "unresolved metavariables in frozen type for {info.name}"
  unless ← isProp expected do
    throwError "expected frozen theorem type is not Prop for {info.name}"
  let actual := info.type.instantiateLevelParams info.levelParams levels
  unless ← isProp actual do
    throwError "actual theorem type is not Prop for {info.name}"
  unless ← isDefEq actual expected do
    throwError "frozen type mismatch for {info.name}: actual {actual}, expected {expected}"
  logInfo m!"RIGID_PROP_"Eq.{0} @isLocallyConstant_of_extDerivFun_eq_zero.{u_5, u_6, u_7} @isLocallyConstant_of_extDerivFun_eq_zero.{u_5, u_6, u_7}"_CONTRACT_OK:{info.name}:{info.levelParams}"

run_cmd liftTermElabM do
  let info ← getConstInfo "extDerivFun_apply_mlieBracket_chart_eq".toName
  let levels : List Level := [Level.param "u_5".toName, Level.param "u_6".toName, Level.param "u_7".toName]
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "Eq.{0} @extDerivFun_apply_mlieBracket_chart.{u_5, u_6, u_7} @extDerivFun_apply_mlieBracket_chart.{u_5, u_6, u_7}" with
    | .ok parsedType => pure parsedType
    | .error error => throwError error
  let expected ← Term.elabType parsedType
  Term.synthesizeSyntheticMVarsNoPostponing
  let expected ← instantiateMVars expected
  if expected.hasMVar || expected.hasLevelMVar then
    throwError "unresolved metavariables in frozen type for {info.name}"
  unless ← isProp expected do
    throwError "expected frozen theorem type is not Prop for {info.name}"
  let actual := info.type.instantiateLevelParams info.levelParams levels
  unless ← isProp actual do
    throwError "actual theorem type is not Prop for {info.name}"
  unless ← isDefEq actual expected do
    throwError "frozen type mismatch for {info.name}: actual {actual}, expected {expected}"
  logInfo m!"RIGID_PROP_"Eq.{0} @extDerivFun_apply_mlieBracket_chart.{u_5, u_6, u_7} @extDerivFun_apply_mlieBracket_chart.{u_5, u_6, u_7}"_CONTRACT_OK:{info.name}:{info.levelParams}"

run_cmd liftTermElabM do
  let info ← getConstInfo "mpullback_extChartAt_symm_apply_eq".toName
  let levels : List Level := [Level.param "u_5".toName, Level.param "u_6".toName, Level.param "u_7".toName]
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "Eq.{0} @mpullback_extChartAt_symm_apply.{u_5, u_6, u_7} @mpullback_extChartAt_symm_apply.{u_5, u_6, u_7}" with
    | .ok parsedType => pure parsedType
    | .error error => throwError error
  let expected ← Term.elabType parsedType
  Term.synthesizeSyntheticMVarsNoPostponing
  let expected ← instantiateMVars expected
  if expected.hasMVar || expected.hasLevelMVar then
    throwError "unresolved metavariables in frozen type for {info.name}"
  unless ← isProp expected do
    throwError "expected frozen theorem type is not Prop for {info.name}"
  let actual := info.type.instantiateLevelParams info.levelParams levels
  unless ← isProp actual do
    throwError "actual theorem type is not Prop for {info.name}"
  unless ← isDefEq actual expected do
    throwError "frozen type mismatch for {info.name}: actual {actual}, expected {expected}"
  logInfo m!"RIGID_PROP_"Eq.{0} @mpullback_extChartAt_symm_apply.{u_5, u_6, u_7} @mpullback_extChartAt_symm_apply.{u_5, u_6, u_7}"_CONTRACT_OK:{info.name}:{info.levelParams}"

run_cmd liftTermElabM do
  let info ← getConstInfo "extDerivFun_section_eventually_chart_eq".toName
  let levels : List Level := [Level.param "u_5".toName, Level.param "u_6".toName, Level.param "u_7".toName]
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "Eq.{0} @extDerivFun_section_eventually_chart.{u_5, u_6, u_7} @extDerivFun_section_eventually_chart.{u_5, u_6, u_7}" with
    | .ok parsedType => pure parsedType
    | .error error => throwError error
  let expected ← Term.elabType parsedType
  Term.synthesizeSyntheticMVarsNoPostponing
  let expected ← instantiateMVars expected
  if expected.hasMVar || expected.hasLevelMVar then
    throwError "unresolved metavariables in frozen type for {info.name}"
  unless ← isProp expected do
    throwError "expected frozen theorem type is not Prop for {info.name}"
  let actual := info.type.instantiateLevelParams info.levelParams levels
  unless ← isProp actual do
    throwError "actual theorem type is not Prop for {info.name}"
  unless ← isDefEq actual expected do
    throwError "frozen type mismatch for {info.name}: actual {actual}, expected {expected}"
  logInfo m!"RIGID_PROP_"Eq.{0} @extDerivFun_section_eventually_chart.{u_5, u_6, u_7} @extDerivFun_section_eventually_chart.{u_5, u_6, u_7}"_CONTRACT_OK:{info.name}:{info.levelParams}"

run_cmd liftTermElabM do
  let info ← getConstInfo "extDerivFun_extDerivFun_chart_eq".toName
  let levels : List Level := [Level.param "u_5".toName, Level.param "u_6".toName, Level.param "u_7".toName]
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "Eq.{0} @extDerivFun_extDerivFun_chart.{u_5, u_6, u_7} @extDerivFun_extDerivFun_chart.{u_5, u_6, u_7}" with
    | .ok parsedType => pure parsedType
    | .error error => throwError error
  let expected ← Term.elabType parsedType
  Term.synthesizeSyntheticMVarsNoPostponing
  let expected ← instantiateMVars expected
  if expected.hasMVar || expected.hasLevelMVar then
    throwError "unresolved metavariables in frozen type for {info.name}"
  unless ← isProp expected do
    throwError "expected frozen theorem type is not Prop for {info.name}"
  let actual := info.type.instantiateLevelParams info.levelParams levels
  unless ← isProp actual do
    throwError "actual theorem type is not Prop for {info.name}"
  unless ← isDefEq actual expected do
    throwError "frozen type mismatch for {info.name}: actual {actual}, expected {expected}"
  logInfo m!"RIGID_PROP_"Eq.{0} @extDerivFun_extDerivFun_chart.{u_5, u_6, u_7} @extDerivFun_extDerivFun_chart.{u_5, u_6, u_7}"_CONTRACT_OK:{info.name}:{info.levelParams}"

run_cmd liftTermElabM do
  let info ← getConstInfo "extDerivFun_apply_mlieBracket_eq".toName
  let levels : List Level := [Level.param "u_5".toName, Level.param "u_6".toName, Level.param "u_7".toName]
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "Eq.{0} @extDerivFun_apply_mlieBracket.{u_5, u_6, u_7} @extDerivFun_apply_mlieBracket.{u_5, u_6, u_7}" with
    | .ok parsedType => pure parsedType
    | .error error => throwError error
  let expected ← Term.elabType parsedType
  Term.synthesizeSyntheticMVarsNoPostponing
  let expected ← instantiateMVars expected
  if expected.hasMVar || expected.hasLevelMVar then
    throwError "unresolved metavariables in frozen type for {info.name}"
  unless ← isProp expected do
    throwError "expected frozen theorem type is not Prop for {info.name}"
  let actual := info.type.instantiateLevelParams info.levelParams levels
  unless ← isProp actual do
    throwError "actual theorem type is not Prop for {info.name}"
  unless ← isDefEq actual expected do
    throwError "frozen type mismatch for {info.name}: actual {actual}, expected {expected}"
  logInfo m!"RIGID_PROP_"Eq.{0} @extDerivFun_apply_mlieBracket.{u_5, u_6, u_7} @extDerivFun_apply_mlieBracket.{u_5, u_6, u_7}"_CONTRACT_OK:{info.name}:{info.levelParams}"
