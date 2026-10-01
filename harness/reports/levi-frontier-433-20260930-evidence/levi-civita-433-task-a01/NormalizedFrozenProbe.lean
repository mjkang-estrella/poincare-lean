import Lean
import Poincare.LeviCivitaUniqueness
open Lean Elab Command Meta
set_option autoImplicit false
run_cmd do
  let name := "CovariantDerivative.MetricCompatibleAt".toName
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
  logInfo "AXIOM_CONTRACT_OK: CovariantDerivative.MetricCompatibleAt"
run_cmd do
  let name := "CovariantDerivative.TorsionFreeAt".toName
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
  logInfo "AXIOM_CONTRACT_OK: CovariantDerivative.TorsionFreeAt"
run_cmd do
  let name := "CovariantDerivative.leviCivita_unique_at".toName
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
  logInfo "AXIOM_CONTRACT_OK: CovariantDerivative.leviCivita_unique_at"
run_cmd do
  let name := "CovariantDerivative.leviCivita_unique_at_values".toName
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
  logInfo "AXIOM_CONTRACT_OK: CovariantDerivative.leviCivita_unique_at_values"
run_cmd do
  let name := "CovariantDerivative.koszul_formula".toName
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
  logInfo "AXIOM_CONTRACT_OK: CovariantDerivative.koszul_formula"
run_cmd do
  let name := "CovariantDerivative.metricCompatibleAt_eq".toName
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
  logInfo "AXIOM_CONTRACT_OK: CovariantDerivative.metricCompatibleAt_eq"
run_cmd do
  let name := "CovariantDerivative.torsionFreeAt_eq".toName
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
  logInfo "AXIOM_CONTRACT_OK: CovariantDerivative.torsionFreeAt_eq"
run_cmd do
  let name := "CovariantDerivative.leviCivita_unique_at_eq".toName
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
  logInfo "AXIOM_CONTRACT_OK: CovariantDerivative.leviCivita_unique_at_eq"
run_cmd do
  let name := "CovariantDerivative.leviCivita_unique_at_values_eq".toName
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
  logInfo "AXIOM_CONTRACT_OK: CovariantDerivative.leviCivita_unique_at_values_eq"
run_cmd do
  let name := "CovariantDerivative.koszul_formula_eq".toName
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
  logInfo "AXIOM_CONTRACT_OK: CovariantDerivative.koszul_formula_eq"
open scoped Manifold
universe u_1 u_2 u_3 u_4 u_5 u_6
run_cmd liftTermElabM do
  let info ← getConstInfo "CovariantDerivative.MetricCompatibleAt".toName
  let levels : List Level := [Level.param "u_1".toName, Level.param "u_2".toName, Level.param "u_3".toName]
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "{E : Type u_1} → [inst : NormedAddCommGroup.{u_1} E] → [inst_1 : NormedSpace.{0, u_1} Real E] → {H : Type u_2} → [inst_2 : TopologicalSpace.{u_2} H] → {I : ModelWithCorners.{0, u_1, u_2} Real E H} → {M : Type u_3} → [inst_3 : TopologicalSpace.{u_3} M] → [inst_4 : ChartedSpace.{u_2, u_3} H M] → [inst_5 : IsManifold.{0, u_1, u_2, u_3} I (1 : WithTop.{0} ENat) M] → ((y : M) → ContinuousLinearMap.{0, 0, u_1, u_1} (RingHom.id.{0} Real) (TangentSpace.{u_1, 0, u_2, u_3} I y) (ContinuousLinearMap.{0, 0, u_1, 0} (RingHom.id.{0} Real) (TangentSpace.{u_1, 0, u_2, u_3} I y) Real)) → CovariantDerivative.{0, u_1, u_2, u_3, u_1, u_1} I E (TangentSpace.{u_1, 0, u_2, u_3} I) → M → Prop" with
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
  logInfo "FROZEN_CONTRACT_OK: CovariantDerivative.MetricCompatibleAt"
run_cmd liftTermElabM do
  let info ← getConstInfo "CovariantDerivative.TorsionFreeAt".toName
  let levels : List Level := [Level.param "u_1".toName, Level.param "u_2".toName, Level.param "u_3".toName]
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "{E : Type u_1} → [inst : NormedAddCommGroup.{u_1} E] → [inst_1 : NormedSpace.{0, u_1} Real E] → {H : Type u_2} → [inst_2 : TopologicalSpace.{u_2} H] → {I : ModelWithCorners.{0, u_1, u_2} Real E H} → {M : Type u_3} → [inst_3 : TopologicalSpace.{u_3} M] → [inst_4 : ChartedSpace.{u_2, u_3} H M] → [inst_5 : IsManifold.{0, u_1, u_2, u_3} I (1 : WithTop.{0} ENat) M] → CovariantDerivative.{0, u_1, u_2, u_3, u_1, u_1} I E (TangentSpace.{u_1, 0, u_2, u_3} I) → M → Prop" with
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
  logInfo "FROZEN_CONTRACT_OK: CovariantDerivative.TorsionFreeAt"
run_cmd liftTermElabM do
  let info ← getConstInfo "CovariantDerivative.leviCivita_unique_at".toName
  let levels : List Level := [Level.param "u_1".toName, Level.param "u_2".toName, Level.param "u_3".toName]
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "∀ {E : Type u_1} [inst : NormedAddCommGroup.{u_1} E] [inst_1 : NormedSpace.{0, u_1} Real E] {H : Type u_2} [inst_2 : TopologicalSpace.{u_2} H] {I : ModelWithCorners.{0, u_1, u_2} Real E H} {M : Type u_3} [inst_3 : TopologicalSpace.{u_3} M] [inst_4 : ChartedSpace.{u_2, u_3} H M] [inst_5 : IsManifold.{0, u_1, u_2, u_3} I (1 : WithTop.{0} ENat) M] {g : (y : M) → ContinuousLinearMap.{0, 0, u_1, u_1} (RingHom.id.{0} Real) (TangentSpace.{u_1, 0, u_2, u_3} I y) (ContinuousLinearMap.{0, 0, u_1, 0} (RingHom.id.{0} Real) (TangentSpace.{u_1, 0, u_2, u_3} I y) Real)} {cov cov' : CovariantDerivative.{0, u_1, u_2, u_3, u_1, u_1} I E (TangentSpace.{u_1, 0, u_2, u_3} I)} {x : M}, (∀ (v w : TangentSpace.{u_1, 0, u_2, u_3} I x), Eq.{1} (((g x) v) w) (((g x) w) v)) → (∀ (v : TangentSpace.{u_1, 0, u_2, u_3} I x), (∀ (w : TangentSpace.{u_1, 0, u_2, u_3} I x), Eq.{1} (((g x) v) w) (0 : Real)) → Eq.{u_1 + 1} v (0 : TangentSpace.{u_1, 0, u_2, u_3} I x)) → CovariantDerivative.MetricCompatibleAt.{u_1, u_2, u_3} g cov x → CovariantDerivative.MetricCompatibleAt.{u_1, u_2, u_3} g cov' x → CovariantDerivative.TorsionFreeAt.{u_1, u_2, u_3} cov x → CovariantDerivative.TorsionFreeAt.{u_1, u_2, u_3} cov' x → ∀ {σ : (y : M) → TangentSpace.{u_1, 0, u_2, u_3} I y}, MDifferentiableAt.{0, u_1, u_2, u_3, u_1, max u_1 u_2, max u_1 u_3} I (ModelWithCorners.prod.{0, u_1, u_2, u_1, u_1} I (modelWithCornersSelf.{0, u_1} Real E)) (fun (y : M) => Bundle.TotalSpace.mk'.{u_3, u_1, u_1} E y (σ y)) x → Eq.{u_1 + 1} (↑cov σ x) (↑cov' σ x)" with
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
  logInfo "FROZEN_CONTRACT_OK: CovariantDerivative.leviCivita_unique_at"
run_cmd liftTermElabM do
  let info ← getConstInfo "CovariantDerivative.leviCivita_unique_at_values".toName
  let levels : List Level := [Level.param "u_1".toName, Level.param "u_2".toName, Level.param "u_3".toName]
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "∀ {E : Type u_1} [inst : NormedAddCommGroup.{u_1} E] [inst_1 : NormedSpace.{0, u_1} Real E] {H : Type u_2} [inst_2 : TopologicalSpace.{u_2} H] {I : ModelWithCorners.{0, u_1, u_2} Real E H} {M : Type u_3} [inst_3 : TopologicalSpace.{u_3} M] [inst_4 : ChartedSpace.{u_2, u_3} H M] [inst_5 : IsManifold.{0, u_1, u_2, u_3} I (1 : WithTop.{0} ENat) M] {g : (y : M) → ContinuousLinearMap.{0, 0, u_1, u_1} (RingHom.id.{0} Real) (TangentSpace.{u_1, 0, u_2, u_3} I y) (ContinuousLinearMap.{0, 0, u_1, 0} (RingHom.id.{0} Real) (TangentSpace.{u_1, 0, u_2, u_3} I y) Real)} {x : M} (cov cov' : ((y : M) → TangentSpace.{u_1, 0, u_2, u_3} I y) → ContinuousLinearMap.{0, 0, u_1, u_1} (RingHom.id.{0} Real) (TangentSpace.{u_1, 0, u_2, u_3} I x) (TangentSpace.{u_1, 0, u_2, u_3} I x)), (∀ (v w : TangentSpace.{u_1, 0, u_2, u_3} I x), Eq.{1} (((g x) v) w) (((g x) w) v)) → (∀ (v : TangentSpace.{u_1, 0, u_2, u_3} I x), (∀ (w : TangentSpace.{u_1, 0, u_2, u_3} I x), Eq.{1} (((g x) v) w) (0 : Real)) → Eq.{u_1 + 1} v (0 : TangentSpace.{u_1, 0, u_2, u_3} I x)) → (∀ {Y Z : (y : M) → TangentSpace.{u_1, 0, u_2, u_3} I y}, MDifferentiableAt.{0, u_1, u_2, u_3, u_1, max u_1 u_2, max u_1 u_3} I (ModelWithCorners.prod.{0, u_1, u_2, u_1, u_1} I (modelWithCornersSelf.{0, u_1} Real E)) (fun (y : M) => Bundle.TotalSpace.mk'.{u_3, u_1, u_1} E y (Y y)) x → MDifferentiableAt.{0, u_1, u_2, u_3, u_1, max u_1 u_2, max u_1 u_3} I (ModelWithCorners.prod.{0, u_1, u_2, u_1, u_1} I (modelWithCornersSelf.{0, u_1} Real E)) (fun (y : M) => Bundle.TotalSpace.mk'.{u_3, u_1, u_1} E y (Z y)) x → ∀ (v : TangentSpace.{u_1, 0, u_2, u_3} I x), Eq.{1} (((fun (f : M → ℝ) (z : M) => (NormedSpace.fromTangentSpace (f z)).toContinuousLinearMap.comp (mfderiv I 𝓘(ℝ, ℝ) f z)) (fun (y : M) => ((g y) (Y y)) (Z y)) x) v) (HAdd.hAdd.{0, 0, 0} (((g x) ((cov Y) v)) (Z x)) (((g x) (Y x)) ((cov Z) v)))) → (∀ {Y Z : (y : M) → TangentSpace.{u_1, 0, u_2, u_3} I y}, MDifferentiableAt.{0, u_1, u_2, u_3, u_1, max u_1 u_2, max u_1 u_3} I (ModelWithCorners.prod.{0, u_1, u_2, u_1, u_1} I (modelWithCornersSelf.{0, u_1} Real E)) (fun (y : M) => Bundle.TotalSpace.mk'.{u_3, u_1, u_1} E y (Y y)) x → MDifferentiableAt.{0, u_1, u_2, u_3, u_1, max u_1 u_2, max u_1 u_3} I (ModelWithCorners.prod.{0, u_1, u_2, u_1, u_1} I (modelWithCornersSelf.{0, u_1} Real E)) (fun (y : M) => Bundle.TotalSpace.mk'.{u_3, u_1, u_1} E y (Z y)) x → ∀ (v : TangentSpace.{u_1, 0, u_2, u_3} I x), Eq.{1} (((fun (f : M → ℝ) (z : M) => (NormedSpace.fromTangentSpace (f z)).toContinuousLinearMap.comp (mfderiv I 𝓘(ℝ, ℝ) f z)) (fun (y : M) => ((g y) (Y y)) (Z y)) x) v) (HAdd.hAdd.{0, 0, 0} (((g x) ((cov' Y) v)) (Z x)) (((g x) (Y x)) ((cov' Z) v)))) → (∀ {X Y : (y : M) → TangentSpace.{u_1, 0, u_2, u_3} I y}, MDifferentiableAt.{0, u_1, u_2, u_3, u_1, max u_1 u_2, max u_1 u_3} I (ModelWithCorners.prod.{0, u_1, u_2, u_1, u_1} I (modelWithCornersSelf.{0, u_1} Real E)) (fun (y : M) => Bundle.TotalSpace.mk'.{u_3, u_1, u_1} E y (X y)) x → MDifferentiableAt.{0, u_1, u_2, u_3, u_1, max u_1 u_2, max u_1 u_3} I (ModelWithCorners.prod.{0, u_1, u_2, u_1, u_1} I (modelWithCornersSelf.{0, u_1} Real E)) (fun (y : M) => Bundle.TotalSpace.mk'.{u_3, u_1, u_1} E y (Y y)) x → Eq.{u_1 + 1} (HSub.hSub.{u_1, u_1, u_1} ((cov Y) (X x)) ((cov X) (Y x))) (VectorField.mlieBracket.{0, u_2, u_1, u_3} I X Y x)) → (∀ {X Y : (y : M) → TangentSpace.{u_1, 0, u_2, u_3} I y}, MDifferentiableAt.{0, u_1, u_2, u_3, u_1, max u_1 u_2, max u_1 u_3} I (ModelWithCorners.prod.{0, u_1, u_2, u_1, u_1} I (modelWithCornersSelf.{0, u_1} Real E)) (fun (y : M) => Bundle.TotalSpace.mk'.{u_3, u_1, u_1} E y (X y)) x → MDifferentiableAt.{0, u_1, u_2, u_3, u_1, max u_1 u_2, max u_1 u_3} I (ModelWithCorners.prod.{0, u_1, u_2, u_1, u_1} I (modelWithCornersSelf.{0, u_1} Real E)) (fun (y : M) => Bundle.TotalSpace.mk'.{u_3, u_1, u_1} E y (Y y)) x → Eq.{u_1 + 1} (HSub.hSub.{u_1, u_1, u_1} ((cov' Y) (X x)) ((cov' X) (Y x))) (VectorField.mlieBracket.{0, u_2, u_1, u_3} I X Y x)) → ∀ {σ : (y : M) → TangentSpace.{u_1, 0, u_2, u_3} I y}, MDifferentiableAt.{0, u_1, u_2, u_3, u_1, max u_1 u_2, max u_1 u_3} I (ModelWithCorners.prod.{0, u_1, u_2, u_1, u_1} I (modelWithCornersSelf.{0, u_1} Real E)) (fun (y : M) => Bundle.TotalSpace.mk'.{u_3, u_1, u_1} E y (σ y)) x → Eq.{u_1 + 1} (cov σ) (cov' σ)" with
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
  logInfo "FROZEN_CONTRACT_OK: CovariantDerivative.leviCivita_unique_at_values"
run_cmd liftTermElabM do
  let info ← getConstInfo "CovariantDerivative.koszul_formula".toName
  let levels : List Level := [Level.param "u_1".toName, Level.param "u_2".toName, Level.param "u_3".toName]
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "∀ {E : Type u_1} [inst : NormedAddCommGroup.{u_1} E] [inst_1 : NormedSpace.{0, u_1} Real E] {H : Type u_2} [inst_2 : TopologicalSpace.{u_2} H] {I : ModelWithCorners.{0, u_1, u_2} Real E H} {M : Type u_3} [inst_3 : TopologicalSpace.{u_3} M] [inst_4 : ChartedSpace.{u_2, u_3} H M] [inst_5 : IsManifold.{0, u_1, u_2, u_3} I (1 : WithTop.{0} ENat) M] {g : (y : M) → ContinuousLinearMap.{0, 0, u_1, u_1} (RingHom.id.{0} Real) (TangentSpace.{u_1, 0, u_2, u_3} I y) (ContinuousLinearMap.{0, 0, u_1, 0} (RingHom.id.{0} Real) (TangentSpace.{u_1, 0, u_2, u_3} I y) Real)} {cov : CovariantDerivative.{0, u_1, u_2, u_3, u_1, u_1} I E (TangentSpace.{u_1, 0, u_2, u_3} I)} {x : M}, (∀ (v w : TangentSpace.{u_1, 0, u_2, u_3} I x), Eq.{1} (((g x) v) w) (((g x) w) v)) → CovariantDerivative.MetricCompatibleAt.{u_1, u_2, u_3} g cov x → CovariantDerivative.TorsionFreeAt.{u_1, u_2, u_3} cov x → ∀ {X Y Z : (y : M) → TangentSpace.{u_1, 0, u_2, u_3} I y}, MDifferentiableAt.{0, u_1, u_2, u_3, u_1, max u_1 u_2, max u_1 u_3} I (ModelWithCorners.prod.{0, u_1, u_2, u_1, u_1} I (modelWithCornersSelf.{0, u_1} Real E)) (fun (y : M) => Bundle.TotalSpace.mk'.{u_3, u_1, u_1} E y (X y)) x → MDifferentiableAt.{0, u_1, u_2, u_3, u_1, max u_1 u_2, max u_1 u_3} I (ModelWithCorners.prod.{0, u_1, u_2, u_1, u_1} I (modelWithCornersSelf.{0, u_1} Real E)) (fun (y : M) => Bundle.TotalSpace.mk'.{u_3, u_1, u_1} E y (Y y)) x → MDifferentiableAt.{0, u_1, u_2, u_3, u_1, max u_1 u_2, max u_1 u_3} I (ModelWithCorners.prod.{0, u_1, u_2, u_1, u_1} I (modelWithCornersSelf.{0, u_1} Real E)) (fun (y : M) => Bundle.TotalSpace.mk'.{u_3, u_1, u_1} E y (Z y)) x → Eq.{1} (HMul.hMul.{0, 0, 0} (2 : Real) (((g x) ((↑cov Y x) (X x))) (Z x))) (HSub.hSub.{0, 0, 0} (HSub.hSub.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} (HSub.hSub.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} (((fun (f : M → ℝ) (z : M) => (NormedSpace.fromTangentSpace (f z)).toContinuousLinearMap.comp (mfderiv I 𝓘(ℝ, ℝ) f z)) (fun (y : M) => ((g y) (Y y)) (Z y)) x) (X x)) (((fun (f : M → ℝ) (z : M) => (NormedSpace.fromTangentSpace (f z)).toContinuousLinearMap.comp (mfderiv I 𝓘(ℝ, ℝ) f z)) (fun (y : M) => ((g y) (X y)) (Z y)) x) (Y x))) (((fun (f : M → ℝ) (z : M) => (NormedSpace.fromTangentSpace (f z)).toContinuousLinearMap.comp (mfderiv I 𝓘(ℝ, ℝ) f z)) (fun (y : M) => ((g y) (X y)) (Y y)) x) (Z x))) (((g x) (VectorField.mlieBracket.{0, u_2, u_1, u_3} I X Y x)) (Z x))) (((g x) (VectorField.mlieBracket.{0, u_2, u_1, u_3} I X Z x)) (Y x))) (((g x) (VectorField.mlieBracket.{0, u_2, u_1, u_3} I Y Z x)) (X x)))" with
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
  logInfo "FROZEN_CONTRACT_OK: CovariantDerivative.koszul_formula"
run_cmd liftTermElabM do
  let info ← getConstInfo "CovariantDerivative.metricCompatibleAt_eq".toName
  let levels : List Level := [Level.param "u_4".toName, Level.param "u_5".toName, Level.param "u_6".toName]
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "Eq.{max (max (u_4 + 2) (u_5 + 2)) (u_6 + 2)} @CovariantDerivative.MetricCompatibleAt.{u_6, u_5, u_4} @CovariantDerivative.MetricCompatibleAt.{u_6, u_5, u_4}" with
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
  logInfo "FROZEN_CONTRACT_OK: CovariantDerivative.metricCompatibleAt_eq"
run_cmd liftTermElabM do
  let info ← getConstInfo "CovariantDerivative.torsionFreeAt_eq".toName
  let levels : List Level := [Level.param "u_4".toName, Level.param "u_5".toName, Level.param "u_6".toName]
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "Eq.{max (max (u_4 + 2) (u_5 + 2)) (u_6 + 2)} @CovariantDerivative.TorsionFreeAt.{u_6, u_5, u_4} @CovariantDerivative.TorsionFreeAt.{u_6, u_5, u_4}" with
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
  logInfo "FROZEN_CONTRACT_OK: CovariantDerivative.torsionFreeAt_eq"
run_cmd liftTermElabM do
  let info ← getConstInfo "CovariantDerivative.leviCivita_unique_at_eq".toName
  let levels : List Level := [Level.param "u_4".toName, Level.param "u_5".toName, Level.param "u_6".toName]
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "Eq.{0} @CovariantDerivative.leviCivita_unique_at.{u_4, u_5, u_6} @CovariantDerivative.leviCivita_unique_at.{u_4, u_5, u_6}" with
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
  logInfo "FROZEN_CONTRACT_OK: CovariantDerivative.leviCivita_unique_at_eq"
run_cmd liftTermElabM do
  let info ← getConstInfo "CovariantDerivative.leviCivita_unique_at_values_eq".toName
  let levels : List Level := [Level.param "u_4".toName, Level.param "u_5".toName, Level.param "u_6".toName]
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "Eq.{0} @CovariantDerivative.leviCivita_unique_at_values.{u_4, u_5, u_6} @CovariantDerivative.leviCivita_unique_at_values.{u_4, u_5, u_6}" with
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
  logInfo "FROZEN_CONTRACT_OK: CovariantDerivative.leviCivita_unique_at_values_eq"
run_cmd liftTermElabM do
  let info ← getConstInfo "CovariantDerivative.koszul_formula_eq".toName
  let levels : List Level := [Level.param "u_4".toName, Level.param "u_5".toName, Level.param "u_6".toName]
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "Eq.{0} @CovariantDerivative.koszul_formula.{u_4, u_5, u_6} @CovariantDerivative.koszul_formula.{u_4, u_5, u_6}" with
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
  logInfo "FROZEN_CONTRACT_OK: CovariantDerivative.koszul_formula_eq"
