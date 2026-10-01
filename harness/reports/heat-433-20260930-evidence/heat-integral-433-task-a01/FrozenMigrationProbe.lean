import Lean
import Poincare.Global.HeatKernelIntegral
open Lean Elab Command Meta
set_option autoImplicit false
run_cmd do
  let name := "Poincare.heatKernel_integrable".toName
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
  logInfo "AXIOM_CONTRACT_OK: Poincare.heatKernel_integrable"
run_cmd do
  let name := "Poincare.integral_heatKernel_eq_one".toName
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
  logInfo "AXIOM_CONTRACT_OK: Poincare.integral_heatKernel_eq_one"
run_cmd do
  let name := "Poincare.heatSolution".toName
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
  logInfo "AXIOM_CONTRACT_OK: Poincare.heatSolution"
run_cmd do
  let name := "Poincare.heatSolution_apply".toName
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
  logInfo "AXIOM_CONTRACT_OK: Poincare.heatSolution_apply"
run_cmd do
  let name := "Poincare.heatKernel_convolutionExistsAt_of_bounded_continuous".toName
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
  logInfo "AXIOM_CONTRACT_OK: Poincare.heatKernel_convolutionExistsAt_of_bounded_continuous"
run_cmd do
  let name := "Poincare.heatKernel_convolutionExists_of_bounded_continuous".toName
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
  logInfo "AXIOM_CONTRACT_OK: Poincare.heatKernel_convolutionExists_of_bounded_continuous"
run_cmd do
  let name := "Poincare.continuous_heatSolution_of_bounded_continuous".toName
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
  logInfo "AXIOM_CONTRACT_OK: Poincare.continuous_heatSolution_of_bounded_continuous"
run_cmd do
  let name := "Poincare.gaussianApproxIdentity_heatTimeScale_complex".toName
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
  logInfo "AXIOM_CONTRACT_OK: Poincare.gaussianApproxIdentity_heatTimeScale_complex"
universe u_1
run_cmd liftTermElabM do
  let info ← getConstInfo "Poincare.heatKernel_integrable".toName
  let levels : List Level := [Level.param "u_1".toName]
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "∀ {E : Type u_1} [inst : NormedAddCommGroup.{u_1} E] [inst_1 : InnerProductSpace.{0, u_1} Real E] [inst_2 : FiniteDimensional.{0, u_1} Real E] [inst_3 : MeasurableSpace.{u_1} E] [inst_4 : BorelSpace.{u_1} E] {t : Real}, LT.lt.{0} (0 : Real) t → MeasureTheory.Integrable.{0, u_1} (fun (x : E) => Poincare.heatKernel.{u_1} t x) MeasureTheory.MeasureSpace.volume.{u_1}" with
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
  logInfo "FROZEN_CONTRACT_OK: Poincare.heatKernel_integrable"
run_cmd liftTermElabM do
  let info ← getConstInfo "Poincare.integral_heatKernel_eq_one".toName
  let levels : List Level := [Level.param "u_1".toName]
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "∀ {E : Type u_1} [inst : NormedAddCommGroup.{u_1} E] [inst_1 : InnerProductSpace.{0, u_1} Real E] [inst_2 : FiniteDimensional.{0, u_1} Real E] [inst_3 : MeasurableSpace.{u_1} E] [inst_4 : BorelSpace.{u_1} E] {t : Real}, LT.lt.{0} (0 : Real) t → Eq.{1} (∫ (x : E), Poincare.heatKernel.{u_1} t x) (1 : Real)" with
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
  logInfo "FROZEN_CONTRACT_OK: Poincare.integral_heatKernel_eq_one"
run_cmd liftTermElabM do
  let info ← getConstInfo "Poincare.heatSolution".toName
  let levels : List Level := [Level.param "u_1".toName]
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "{E : Type u_1} → [inst : NormedAddCommGroup.{u_1} E] → [inst_1 : InnerProductSpace.{0, u_1} Real E] → [FiniteDimensional.{0, u_1} Real E] → [inst_3 : MeasurableSpace.{u_1} E] → [BorelSpace.{u_1} E] → Real → (E → Real) → E → Real" with
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
  logInfo "FROZEN_CONTRACT_OK: Poincare.heatSolution"
run_cmd liftTermElabM do
  let info ← getConstInfo "Poincare.heatSolution_apply".toName
  let levels : List Level := [Level.param "u_1".toName]
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "∀ {E : Type u_1} [inst : NormedAddCommGroup.{u_1} E] [inst_1 : InnerProductSpace.{0, u_1} Real E] [inst_2 : FiniteDimensional.{0, u_1} Real E] [inst_3 : MeasurableSpace.{u_1} E] [inst_4 : BorelSpace.{u_1} E] (t : Real) (f : E → Real) (x : E), Eq.{1} (Poincare.heatSolution.{u_1} t f x) (∫ (y : E), HMul.hMul.{0, 0, 0} (Poincare.heatKernel.{u_1} t y) (f (HSub.hSub.{u_1, u_1, u_1} x y)))" with
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
  logInfo "FROZEN_CONTRACT_OK: Poincare.heatSolution_apply"
run_cmd liftTermElabM do
  let info ← getConstInfo "Poincare.heatKernel_convolutionExistsAt_of_bounded_continuous".toName
  let levels : List Level := [Level.param "u_1".toName]
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "∀ {E : Type u_1} [inst : NormedAddCommGroup.{u_1} E] [inst_1 : InnerProductSpace.{0, u_1} Real E] [inst_2 : FiniteDimensional.{0, u_1} Real E] [inst_3 : MeasurableSpace.{u_1} E] [inst_4 : BorelSpace.{u_1} E] {t : Real}, LT.lt.{0} (0 : Real) t → ∀ {f : E → Real}, Continuous.{u_1, 0} f → ∀ {C : Real}, (∀ (x : E), LE.le.{0} (Norm.norm.{0} (f x)) C) → ∀ (x : E), MeasureTheory.ConvolutionExistsAt.{0, u_1, 0, 0, 0} (fun (y : E) => Poincare.heatKernel.{u_1} t y) f x (ContinuousLinearMap.lsmul.{0, 0, 0} Real Real) MeasureTheory.MeasureSpace.volume.{u_1}" with
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
  logInfo "FROZEN_CONTRACT_OK: Poincare.heatKernel_convolutionExistsAt_of_bounded_continuous"
run_cmd liftTermElabM do
  let info ← getConstInfo "Poincare.heatKernel_convolutionExists_of_bounded_continuous".toName
  let levels : List Level := [Level.param "u_1".toName]
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "∀ {E : Type u_1} [inst : NormedAddCommGroup.{u_1} E] [inst_1 : InnerProductSpace.{0, u_1} Real E] [inst_2 : FiniteDimensional.{0, u_1} Real E] [inst_3 : MeasurableSpace.{u_1} E] [inst_4 : BorelSpace.{u_1} E] {t : Real}, LT.lt.{0} (0 : Real) t → ∀ {f : E → Real}, Continuous.{u_1, 0} f → ∀ {C : Real}, (∀ (x : E), LE.le.{0} (Norm.norm.{0} (f x)) C) → MeasureTheory.ConvolutionExists.{0, u_1, 0, 0, 0} (fun (y : E) => Poincare.heatKernel.{u_1} t y) f (ContinuousLinearMap.lsmul.{0, 0, 0} Real Real) MeasureTheory.MeasureSpace.volume.{u_1}" with
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
  logInfo "FROZEN_CONTRACT_OK: Poincare.heatKernel_convolutionExists_of_bounded_continuous"
run_cmd liftTermElabM do
  let info ← getConstInfo "Poincare.continuous_heatSolution_of_bounded_continuous".toName
  let levels : List Level := [Level.param "u_1".toName]
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "∀ {E : Type u_1} [inst : NormedAddCommGroup.{u_1} E] [inst_1 : InnerProductSpace.{0, u_1} Real E] [inst_2 : FiniteDimensional.{0, u_1} Real E] [inst_3 : MeasurableSpace.{u_1} E] [inst_4 : BorelSpace.{u_1} E] {t : Real}, LT.lt.{0} (0 : Real) t → ∀ {f : E → Real}, Continuous.{u_1, 0} f → BddAbove.{0} (Set.range.{0, u_1 + 1} fun (x : E) => Norm.norm.{0} (f x)) → Continuous.{u_1, 0} (Poincare.heatSolution.{u_1} t f)" with
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
  logInfo "FROZEN_CONTRACT_OK: Poincare.continuous_heatSolution_of_bounded_continuous"
run_cmd liftTermElabM do
  let info ← getConstInfo "Poincare.gaussianApproxIdentity_heatTimeScale_complex".toName
  let levels : List Level := [Level.param "u_1".toName]
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "∀ {E : Type u_1} [inst : NormedAddCommGroup.{u_1} E] [inst_1 : InnerProductSpace.{0, u_1} Real E] [inst_2 : FiniteDimensional.{0, u_1} Real E] [inst_3 : MeasurableSpace.{u_1} E] [inst_4 : BorelSpace.{u_1} E] {f : E → Complex}, MeasureTheory.Integrable.{0, u_1} f MeasureTheory.MeasureSpace.volume.{u_1} → ∀ {x : E}, ContinuousAt.{u_1, 0} f x → Filter.Tendsto.{0, 0} (fun (t : Real) => ∫ (y : E), HSMul.hSMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (HPow.hPow.{0, 0, 0} (HMul.hMul.{0, 0, 0} ↑Real.pi ↑(Inv.inv.{0} (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (4 : Real) (HPow.hPow.{0, 0, 0} Real.pi (2 : Nat))) t))) (HDiv.hDiv.{0, 0, 0} ↑(Module.finrank.{0, u_1} Real E) (2 : Complex))) (Complex.exp (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (Neg.neg.{0} (HPow.hPow.{0, 0, 0} ↑Real.pi (2 : Nat))) ↑(Inv.inv.{0} (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (4 : Real) (HPow.hPow.{0, 0, 0} Real.pi (2 : Nat))) t))) (HPow.hPow.{0, 0, 0} ↑(Norm.norm.{u_1} (HSub.hSub.{u_1, u_1, u_1} x y)) (2 : Nat))))) (f y)) (nhdsWithin.{0} (0 : Real) (Set.Ioi.{0} (0 : Real))) (nhds.{0} (f x))" with
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
  logInfo "FROZEN_CONTRACT_OK: Poincare.gaussianApproxIdentity_heatTimeScale_complex"
