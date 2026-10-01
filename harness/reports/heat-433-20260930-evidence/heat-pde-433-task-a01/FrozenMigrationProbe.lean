import Lean
import Poincare.Global.HeatKernelPDE
open Lean Elab Command Meta
set_option autoImplicit false
run_cmd do
  let name := "Poincare.hasDerivAt_heatKernel_time".toName
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
  logInfo "AXIOM_CONTRACT_OK: Poincare.hasDerivAt_heatKernel_time"
run_cmd do
  let name := "Poincare.deriv_heatKernel_time".toName
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
  logInfo "AXIOM_CONTRACT_OK: Poincare.deriv_heatKernel_time"
run_cmd do
  let name := "Poincare.heatKernelReal".toName
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
  logInfo "AXIOM_CONTRACT_OK: Poincare.heatKernelReal"
run_cmd do
  let name := "Poincare.heatKernel_real_eq".toName
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
  logInfo "AXIOM_CONTRACT_OK: Poincare.heatKernel_real_eq"
run_cmd do
  let name := "Poincare.heatKernelReal_heatEquation".toName
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
  logInfo "AXIOM_CONTRACT_OK: Poincare.heatKernelReal_heatEquation"
run_cmd do
  let name := "Poincare.heatKernel_real_heatEquation".toName
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
  logInfo "AXIOM_CONTRACT_OK: Poincare.heatKernel_real_heatEquation"
run_cmd do
  let name := "Poincare.heatKernel_real_heatEquation_laplacian".toName
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
  logInfo "AXIOM_CONTRACT_OK: Poincare.heatKernel_real_heatEquation_laplacian"
universe u_1
run_cmd liftTermElabM do
  let info ← getConstInfo "Poincare.hasDerivAt_heatKernel_time".toName
  let levels : List Level := [Level.param "u_1".toName]
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "∀ {E : Type u_1} [inst : NormedAddCommGroup.{u_1} E] [inst_1 : InnerProductSpace.{0, u_1} Real E] [inst_2 : FiniteDimensional.{0, u_1} Real E] {t : Real}, LT.lt.{0} (0 : Real) t → ∀ (x : E), HasDerivAt.{0, 0} (fun (τ : Real) => Poincare.heatKernel.{u_1} τ x) (HAdd.hAdd.{0, 0, 0} (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (4 : Real) Real.pi) (HDiv.hDiv.{0, 0, 0} (Neg.neg.{0} ↑(Module.finrank.{0, u_1} Real E)) (2 : Real))) (HPow.hPow.{0, 0, 0} (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (4 : Real) Real.pi) t) (HSub.hSub.{0, 0, 0} (HDiv.hDiv.{0, 0, 0} (Neg.neg.{0} ↑(Module.finrank.{0, u_1} Real E)) (2 : Real)) (1 : Real)))) (Real.exp (HDiv.hDiv.{0, 0, 0} (Neg.neg.{0} (HPow.hPow.{0, 0, 0} (Norm.norm.{u_1} x) (2 : Nat))) (HMul.hMul.{0, 0, 0} (4 : Real) t)))) (HMul.hMul.{0, 0, 0} (HPow.hPow.{0, 0, 0} (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (4 : Real) Real.pi) t) (HDiv.hDiv.{0, 0, 0} (Neg.neg.{0} ↑(Module.finrank.{0, u_1} Real E)) (2 : Real))) (HMul.hMul.{0, 0, 0} (Real.exp (HDiv.hDiv.{0, 0, 0} (Neg.neg.{0} (HPow.hPow.{0, 0, 0} (Norm.norm.{u_1} x) (2 : Nat))) (HMul.hMul.{0, 0, 0} (4 : Real) t))) (HDiv.hDiv.{0, 0, 0} (HPow.hPow.{0, 0, 0} (Norm.norm.{u_1} x) (2 : Nat)) (HMul.hMul.{0, 0, 0} (4 : Real) (HPow.hPow.{0, 0, 0} t (2 : Nat))))))) t" with
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
  logInfo "FROZEN_CONTRACT_OK: Poincare.hasDerivAt_heatKernel_time"
run_cmd liftTermElabM do
  let info ← getConstInfo "Poincare.deriv_heatKernel_time".toName
  let levels : List Level := [Level.param "u_1".toName]
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "∀ {E : Type u_1} [inst : NormedAddCommGroup.{u_1} E] [inst_1 : InnerProductSpace.{0, u_1} Real E] [inst_2 : FiniteDimensional.{0, u_1} Real E] {t : Real}, LT.lt.{0} (0 : Real) t → ∀ (x : E), Eq.{1} (deriv.{0, 0} (fun (τ : Real) => Poincare.heatKernel.{u_1} τ x) t) (HAdd.hAdd.{0, 0, 0} (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (4 : Real) Real.pi) (HDiv.hDiv.{0, 0, 0} (Neg.neg.{0} ↑(Module.finrank.{0, u_1} Real E)) (2 : Real))) (HPow.hPow.{0, 0, 0} (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (4 : Real) Real.pi) t) (HSub.hSub.{0, 0, 0} (HDiv.hDiv.{0, 0, 0} (Neg.neg.{0} ↑(Module.finrank.{0, u_1} Real E)) (2 : Real)) (1 : Real)))) (Real.exp (HDiv.hDiv.{0, 0, 0} (Neg.neg.{0} (HPow.hPow.{0, 0, 0} (Norm.norm.{u_1} x) (2 : Nat))) (HMul.hMul.{0, 0, 0} (4 : Real) t)))) (HMul.hMul.{0, 0, 0} (HPow.hPow.{0, 0, 0} (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (4 : Real) Real.pi) t) (HDiv.hDiv.{0, 0, 0} (Neg.neg.{0} ↑(Module.finrank.{0, u_1} Real E)) (2 : Real))) (HMul.hMul.{0, 0, 0} (Real.exp (HDiv.hDiv.{0, 0, 0} (Neg.neg.{0} (HPow.hPow.{0, 0, 0} (Norm.norm.{u_1} x) (2 : Nat))) (HMul.hMul.{0, 0, 0} (4 : Real) t))) (HDiv.hDiv.{0, 0, 0} (HPow.hPow.{0, 0, 0} (Norm.norm.{u_1} x) (2 : Nat)) (HMul.hMul.{0, 0, 0} (4 : Real) (HPow.hPow.{0, 0, 0} t (2 : Nat)))))))" with
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
  logInfo "FROZEN_CONTRACT_OK: Poincare.deriv_heatKernel_time"
run_cmd liftTermElabM do
  let info ← getConstInfo "Poincare.heatKernelReal".toName
  let levels : List Level := []
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "Real → Real → Real" with
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
  logInfo "FROZEN_CONTRACT_OK: Poincare.heatKernelReal"
run_cmd liftTermElabM do
  let info ← getConstInfo "Poincare.heatKernel_real_eq".toName
  let levels : List Level := []
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "∀ (t x : Real), Eq.{1} (Poincare.heatKernel.{0} t x) (Poincare.heatKernelReal t x)" with
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
  logInfo "FROZEN_CONTRACT_OK: Poincare.heatKernel_real_eq"
run_cmd liftTermElabM do
  let info ← getConstInfo "Poincare.heatKernelReal_heatEquation".toName
  let levels : List Level := []
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "∀ {t x : Real}, LT.lt.{0} (0 : Real) t → Eq.{1} (deriv.{0, 0} (fun (τ : Real) => Poincare.heatKernelReal τ x) t) (iteratedDeriv.{0, 0} (2 : Nat) (fun (y : Real) => Poincare.heatKernelReal t y) x)" with
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
  logInfo "FROZEN_CONTRACT_OK: Poincare.heatKernelReal_heatEquation"
run_cmd liftTermElabM do
  let info ← getConstInfo "Poincare.heatKernel_real_heatEquation".toName
  let levels : List Level := []
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "∀ {t x : Real}, LT.lt.{0} (0 : Real) t → Eq.{1} (deriv.{0, 0} (fun (τ : Real) => Poincare.heatKernel.{0} τ x) t) (iteratedDeriv.{0, 0} (2 : Nat) (fun (y : Real) => Poincare.heatKernel.{0} t y) x)" with
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
  logInfo "FROZEN_CONTRACT_OK: Poincare.heatKernel_real_heatEquation"
run_cmd liftTermElabM do
  let info ← getConstInfo "Poincare.heatKernel_real_heatEquation_laplacian".toName
  let levels : List Level := []
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "∀ {t x : Real}, LT.lt.{0} (0 : Real) t → Eq.{1} (deriv.{0, 0} (fun (τ : Real) => Poincare.heatKernel.{0} τ x) t) (Laplacian.laplacian.{0, 0} (fun (y : Real) => Poincare.heatKernel.{0} t y) x)" with
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
  logInfo "FROZEN_CONTRACT_OK: Poincare.heatKernel_real_heatEquation_laplacian"
