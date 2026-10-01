import Lean
import Poincare.Global.HeatApproxIdentity
open Lean Elab Command Meta
set_option autoImplicit false
run_cmd do
  let name := "Poincare.heatKernel_fourier_complex_eq_ofReal".toName
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
  logInfo "AXIOM_CONTRACT_OK: Poincare.heatKernel_fourier_complex_eq_ofReal"
run_cmd do
  let name := "Poincare.heatSolution_apply_swap".toName
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
  logInfo "AXIOM_CONTRACT_OK: Poincare.heatSolution_apply_swap"
run_cmd do
  let name := "Poincare.tendsto_heatSolution_nhdsGT_zero".toName
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
  logInfo "AXIOM_CONTRACT_OK: Poincare.tendsto_heatSolution_nhdsGT_zero"
universe u_1
run_cmd liftTermElabM do
  let info ← getConstInfo "Poincare.heatKernel_fourier_complex_eq_ofReal".toName
  let levels : List Level := [Level.param "u_1".toName]
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "∀ {E : Type u_1} [inst : NormedAddCommGroup.{u_1} E] [inst_1 : InnerProductSpace.{0, u_1} Real E] [inst_2 : FiniteDimensional.{0, u_1} Real E] {t : Real}, LT.lt.{0} (0 : Real) t → ∀ (x y : E), Eq.{1} (HMul.hMul.{0, 0, 0} (HPow.hPow.{0, 0, 0} (HMul.hMul.{0, 0, 0} (Complex.ofReal Real.pi) (Complex.ofReal (Inv.inv.{0} (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (4 : Real) (HPow.hPow.{0, 0, 0} Real.pi (2 : Nat))) t)))) (HDiv.hDiv.{0, 0, 0} ((Nat.cast (Module.finrank.{0, u_1} Real E)) : Complex) (2 : Complex))) (Complex.exp (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (Neg.neg.{0} (HPow.hPow.{0, 0, 0} (Complex.ofReal Real.pi) (2 : Nat))) (Complex.ofReal (Inv.inv.{0} (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (4 : Real) (HPow.hPow.{0, 0, 0} Real.pi (2 : Nat))) t)))) (HPow.hPow.{0, 0, 0} (Complex.ofReal (Norm.norm.{u_1} (HSub.hSub.{u_1, u_1, u_1} x y))) (2 : Nat))))) (Complex.ofReal (Poincare.heatKernel.{u_1} t (HSub.hSub.{u_1, u_1, u_1} x y)))" with
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
  logInfo "FROZEN_CONTRACT_OK: Poincare.heatKernel_fourier_complex_eq_ofReal"
run_cmd liftTermElabM do
  let info ← getConstInfo "Poincare.heatSolution_apply_swap".toName
  let levels : List Level := [Level.param "u_1".toName]
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "∀ {E : Type u_1} [inst : NormedAddCommGroup.{u_1} E] [inst_1 : InnerProductSpace.{0, u_1} Real E] [inst_2 : FiniteDimensional.{0, u_1} Real E] [inst_3 : MeasurableSpace.{u_1} E] [inst_4 : BorelSpace.{u_1} E] (t : Real) (f : E → Real) (x : E), Eq.{1} (Poincare.heatSolution.{u_1} t f x) (MeasureTheory.integral.{u_1, 0} MeasureTheory.MeasureSpace.volume.{u_1} fun (y : E) => HMul.hMul.{0, 0, 0} (Poincare.heatKernel.{u_1} t (HSub.hSub.{u_1, u_1, u_1} x y)) (f y))" with
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
  logInfo "FROZEN_CONTRACT_OK: Poincare.heatSolution_apply_swap"
run_cmd liftTermElabM do
  let info ← getConstInfo "Poincare.tendsto_heatSolution_nhdsGT_zero".toName
  let levels : List Level := [Level.param "u_1".toName]
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "∀ {E : Type u_1} [inst : NormedAddCommGroup.{u_1} E] [inst_1 : InnerProductSpace.{0, u_1} Real E] [inst_2 : FiniteDimensional.{0, u_1} Real E] [inst_3 : MeasurableSpace.{u_1} E] [inst_4 : BorelSpace.{u_1} E] {f : E → Real}, MeasureTheory.Integrable.{0, u_1} f MeasureTheory.MeasureSpace.volume.{u_1} → ∀ {x : E}, ContinuousAt.{u_1, 0} f x → Filter.Tendsto.{0, 0} (fun (t : Real) => Poincare.heatSolution.{u_1} t f x) (nhdsWithin.{0} (0 : Real) (Set.Ioi.{0} (0 : Real))) (nhds.{0} (f x))" with
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
  logInfo "FROZEN_CONTRACT_OK: Poincare.tendsto_heatSolution_nhdsGT_zero"
