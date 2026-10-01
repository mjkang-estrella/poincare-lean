import Lean
import Poincare.FlatModelConnection
open Lean Elab Command Meta
set_option autoImplicit false
run_cmd do
  let name := "flatCovariantDerivative_contMDiff".toName
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
  logInfo "AXIOM_CONTRACT_OK: flatCovariantDerivative_contMDiff"
run_cmd do
  let name := "mdiffAt_vectorSpace_iff_differentiableAt".toName
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
  logInfo "AXIOM_CONTRACT_OK: mdiffAt_vectorSpace_iff_differentiableAt"
run_cmd do
  let name := "flatCovariantDerivative".toName
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
  logInfo "AXIOM_CONTRACT_OK: flatCovariantDerivative"
run_cmd do
  let name := "flatCovariantDerivative_apply".toName
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
  logInfo "AXIOM_CONTRACT_OK: flatCovariantDerivative_apply"
run_cmd do
  let name := "mlieBracket_vectorSpace_eq".toName
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
  logInfo "AXIOM_CONTRACT_OK: mlieBracket_vectorSpace_eq"
run_cmd do
  let name := "flatCovariantDerivative_curvatureOp_eq_zero".toName
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
  logInfo "AXIOM_CONTRACT_OK: flatCovariantDerivative_curvatureOp_eq_zero"
run_cmd do
  let name := "flatCovariantDerivative_torsion_eq_zero".toName
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
  logInfo "AXIOM_CONTRACT_OK: flatCovariantDerivative_torsion_eq_zero"
run_cmd do
  let name := "flatCovariantDerivative_inner_compatible".toName
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
  logInfo "AXIOM_CONTRACT_OK: flatCovariantDerivative_inner_compatible"
run_cmd do
  let name := "flatCovariantDerivative_eq".toName
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
  logInfo "AXIOM_CONTRACT_OK: flatCovariantDerivative_eq"
run_cmd do
  let name := "mdiffAt_vectorSpace_iff_differentiableAt_eq".toName
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
  logInfo "AXIOM_CONTRACT_OK: mdiffAt_vectorSpace_iff_differentiableAt_eq"
run_cmd do
  let name := "flatCovariantDerivative_apply_eq".toName
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
  logInfo "AXIOM_CONTRACT_OK: flatCovariantDerivative_apply_eq"
run_cmd do
  let name := "flatCovariantDerivative_curvatureOp_eq_zero_eq".toName
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
  logInfo "AXIOM_CONTRACT_OK: flatCovariantDerivative_curvatureOp_eq_zero_eq"
run_cmd do
  let name := "flatCovariantDerivative_torsion_eq_zero_eq".toName
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
  logInfo "AXIOM_CONTRACT_OK: flatCovariantDerivative_torsion_eq_zero_eq"
run_cmd do
  let name := "flatCovariantDerivative_inner_compatible_eq".toName
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
  logInfo "AXIOM_CONTRACT_OK: flatCovariantDerivative_inner_compatible_eq"
open scoped Manifold
universe u_1 u_2 u_3 u_4
run_cmd liftTermElabM do
  let info ← getConstInfo "flatCovariantDerivative_contMDiff".toName
  let levels : List Level := [Level.param "u_1".toName, Level.param "u_2".toName]
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField.{u_1} 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup.{u_2} E] [inst_2 : NormedSpace.{u_1, u_2} 𝕜 E] {k : WithTop.{0} ENat}, CovariantDerivative.ContMDiffCovariantDerivative.{u_1, u_2, u_2, u_2, u_2, u_2} (flatCovariantDerivative.{u_1, u_2} 𝕜 E) k" with
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
  logInfo "FROZEN_CONTRACT_OK: flatCovariantDerivative_contMDiff"
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
run_cmd liftTermElabM do
  let info ← getConstInfo "flatCovariantDerivative_apply".toName
  let levels : List Level := [Level.param "u_1".toName, Level.param "u_2".toName]
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField.{u_1} 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup.{u_2} E] [inst_2 : NormedSpace.{u_1, u_2} 𝕜 E] (σ : (x : E) → TangentSpace.{u_2, u_1, u_2, u_2} (modelWithCornersSelf.{u_1, u_2} 𝕜 E) x) (x : E), Eq.{u_2 + 1} ((flatCovariantDerivative.{u_1, u_2} 𝕜 E) σ x) (fderiv.{u_1, u_2, u_2} 𝕜 σ x)" with
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
  logInfo "FROZEN_CONTRACT_OK: flatCovariantDerivative_apply"
run_cmd liftTermElabM do
  let info ← getConstInfo "mlieBracket_vectorSpace_eq".toName
  let levels : List Level := [Level.param "u_1".toName, Level.param "u_2".toName]
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField.{u_1} 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup.{u_2} E] [inst_2 : NormedSpace.{u_1, u_2} 𝕜 E] (V W : (x : E) → TangentSpace.{u_2, u_1, u_2, u_2} (modelWithCornersSelf.{u_1, u_2} 𝕜 E) x), Eq.{u_2 + 1} (VectorField.mlieBracket.{u_1, u_2, u_2, u_2} (modelWithCornersSelf.{u_1, u_2} 𝕜 E) V W) (VectorField.lieBracket.{u_1, u_2} 𝕜 V W)" with
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
  logInfo "FROZEN_CONTRACT_OK: mlieBracket_vectorSpace_eq"
run_cmd liftTermElabM do
  let info ← getConstInfo "flatCovariantDerivative_curvatureOp_eq_zero".toName
  let levels : List Level := [Level.param "u_1".toName, Level.param "u_2".toName]
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField.{u_1} 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup.{u_2} E] [inst_2 : NormedSpace.{u_1, u_2} 𝕜 E] {V W Z : (x : E) → TangentSpace.{u_2, u_1, u_2, u_2} (modelWithCornersSelf.{u_1, u_2} 𝕜 E) x} {x : E}, DifferentiableAt.{u_1, u_2, u_2} 𝕜 V x → DifferentiableAt.{u_1, u_2, u_2} 𝕜 W x → DifferentiableAt.{u_1, u_2, u_2} 𝕜 (fderiv.{u_1, u_2, u_2} 𝕜 Z) x → IsSymmSndFDerivAt.{u_1, u_2, u_2} 𝕜 Z x → Eq.{u_2 + 1} (CovariantDerivative.curvatureOp.{u_1, u_2, u_2, u_2} (flatCovariantDerivative.{u_1, u_2} 𝕜 E) V W Z x) (0 : TangentSpace.{u_2, u_1, u_2, u_2} (modelWithCornersSelf.{u_1, u_2} 𝕜 E) x)" with
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
  logInfo "FROZEN_CONTRACT_OK: flatCovariantDerivative_curvatureOp_eq_zero"
run_cmd liftTermElabM do
  let info ← getConstInfo "flatCovariantDerivative_torsion_eq_zero".toName
  let levels : List Level := [Level.param "u_1".toName, Level.param "u_2".toName]
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField.{u_1} 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup.{u_2} E] [inst_2 : NormedSpace.{u_1, u_2} 𝕜 E] [inst_3 : CompleteSpace.{u_1} 𝕜] [inst_4 : CompleteSpace.{u_2} E] [inst_5 : FiniteDimensional.{u_1, u_2} 𝕜 E], Eq.{u_2 + 1} (CovariantDerivative.torsion.{u_1, u_2, u_2, u_2} (flatCovariantDerivative.{u_1, u_2} 𝕜 E)) (0 : (x : E) → ContinuousLinearMap.{u_1, u_1, u_2, u_2} (RingHom.id.{u_1} 𝕜) (TangentSpace.{u_2, u_1, u_2, u_2} (modelWithCornersSelf.{u_1, u_2} 𝕜 E) x) (ContinuousLinearMap.{u_1, u_1, u_2, u_2} (RingHom.id.{u_1} 𝕜) (TangentSpace.{u_2, u_1, u_2, u_2} (modelWithCornersSelf.{u_1, u_2} 𝕜 E) x) (TangentSpace.{u_2, u_1, u_2, u_2} (modelWithCornersSelf.{u_1, u_2} 𝕜 E) x)))" with
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
  logInfo "FROZEN_CONTRACT_OK: flatCovariantDerivative_torsion_eq_zero"
run_cmd liftTermElabM do
  let info ← getConstInfo "flatCovariantDerivative_inner_compatible".toName
  let levels : List Level := [Level.param "u_3".toName]
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "∀ {F : Type u_3} [inst : NormedAddCommGroup.{u_3} F] [inst_1 : InnerProductSpace.{0, u_3} Real F] {Y Z : F → F} {x : F}, DifferentiableAt.{0, u_3, u_3} Real Y x → DifferentiableAt.{0, u_3, u_3} Real Z x → ∀ (v : F), Eq.{1} ((fderiv.{0, u_3, 0} Real (fun (y : F) => Inner.inner.{0, u_3} Real (Y y) (Z y)) x) v) (HAdd.hAdd.{0, 0, 0} (Inner.inner.{0, u_3} Real (Z x) (((flatCovariantDerivative.{0, u_3} Real F) Y x) v)) (Inner.inner.{0, u_3} Real (Y x) (((flatCovariantDerivative.{0, u_3} Real F) Z x) v)))" with
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
  logInfo "FROZEN_CONTRACT_OK: flatCovariantDerivative_inner_compatible"
run_cmd liftTermElabM do
  let info ← getConstInfo "flatCovariantDerivative_eq".toName
  let levels : List Level := [Level.param "u_3".toName, Level.param "u_4".toName]
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "Eq.{max (u_3 + 2) (u_4 + 2)} flatCovariantDerivative.{u_4, u_3} flatCovariantDerivative.{u_4, u_3}" with
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
  logInfo "FROZEN_CONTRACT_OK: flatCovariantDerivative_eq"
run_cmd liftTermElabM do
  let info ← getConstInfo "mdiffAt_vectorSpace_iff_differentiableAt_eq".toName
  let levels : List Level := [Level.param "u_3".toName, Level.param "u_4".toName]
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "Eq.{0} @mdiffAt_vectorSpace_iff_differentiableAt.{u_3, u_4} @mdiffAt_vectorSpace_iff_differentiableAt.{u_3, u_4}" with
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
  logInfo "FROZEN_CONTRACT_OK: mdiffAt_vectorSpace_iff_differentiableAt_eq"
run_cmd liftTermElabM do
  let info ← getConstInfo "flatCovariantDerivative_apply_eq".toName
  let levels : List Level := [Level.param "u_3".toName, Level.param "u_4".toName]
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "Eq.{0} @flatCovariantDerivative_apply.{u_3, u_4} @flatCovariantDerivative_apply.{u_3, u_4}" with
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
  logInfo "FROZEN_CONTRACT_OK: flatCovariantDerivative_apply_eq"
run_cmd liftTermElabM do
  let info ← getConstInfo "flatCovariantDerivative_curvatureOp_eq_zero_eq".toName
  let levels : List Level := [Level.param "u_3".toName, Level.param "u_4".toName]
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "Eq.{0} @flatCovariantDerivative_curvatureOp_eq_zero.{u_3, u_4} @flatCovariantDerivative_curvatureOp_eq_zero.{u_3, u_4}" with
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
  logInfo "FROZEN_CONTRACT_OK: flatCovariantDerivative_curvatureOp_eq_zero_eq"
run_cmd liftTermElabM do
  let info ← getConstInfo "flatCovariantDerivative_torsion_eq_zero_eq".toName
  let levels : List Level := [Level.param "u_3".toName, Level.param "u_4".toName]
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "Eq.{0} @flatCovariantDerivative_torsion_eq_zero.{u_3, u_4} @flatCovariantDerivative_torsion_eq_zero.{u_3, u_4}" with
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
  logInfo "FROZEN_CONTRACT_OK: flatCovariantDerivative_torsion_eq_zero_eq"
run_cmd liftTermElabM do
  let info ← getConstInfo "flatCovariantDerivative_inner_compatible_eq".toName
  let levels : List Level := [Level.param "u_3".toName]
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "Eq.{0} @flatCovariantDerivative_inner_compatible.{u_3} @flatCovariantDerivative_inner_compatible.{u_3}" with
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
  logInfo "FROZEN_CONTRACT_OK: flatCovariantDerivative_inner_compatible_eq"
