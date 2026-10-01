import Lean
import Poincare.Global.HeatKernelPDEn
open Lean Elab Command Meta
set_option autoImplicit false
run_cmd do
  let name := "Poincare.hasFDerivAt_neg_norm_sq_div".toName
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
  logInfo "AXIOM_CONTRACT_OK: Poincare.hasFDerivAt_neg_norm_sq_div"
run_cmd do
  let name := "Poincare.hasFDerivAt_exp_neg_norm_sq_div".toName
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
  logInfo "AXIOM_CONTRACT_OK: Poincare.hasFDerivAt_exp_neg_norm_sq_div"
run_cmd do
  let name := "Poincare.iteratedFDeriv_two_exp_neg_norm_sq_div_apply".toName
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
  logInfo "AXIOM_CONTRACT_OK: Poincare.iteratedFDeriv_two_exp_neg_norm_sq_div_apply"
run_cmd do
  let name := "Poincare.sum_sq_inner_stdOrthonormalBasis".toName
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
  logInfo "AXIOM_CONTRACT_OK: Poincare.sum_sq_inner_stdOrthonormalBasis"
run_cmd do
  let name := "Poincare.laplacian_exp_neg_norm_sq_div".toName
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
  logInfo "AXIOM_CONTRACT_OK: Poincare.laplacian_exp_neg_norm_sq_div"
run_cmd do
  let name := "Poincare.heatKernel_heatEquation_laplacian".toName
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
  logInfo "AXIOM_CONTRACT_OK: Poincare.heatKernel_heatEquation_laplacian"
universe u_1 u_2
run_cmd liftTermElabM do
  let info ← getConstInfo "Poincare.hasFDerivAt_neg_norm_sq_div".toName
  let levels : List Level := [Level.param "u_1".toName]
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "∀ {E : Type u_1} [inst : NormedAddCommGroup.{u_1} E] [inst_1 : InnerProductSpace.{0, u_1} Real E] (t : Real), Ne.{1} t (0 : Real) → ∀ (x : E), HasFDerivAt.{0, u_1, 0} (fun (y : E) => HDiv.hDiv.{0, 0, 0} (Neg.neg.{0} (HPow.hPow.{0, 0, 0} (Norm.norm.{u_1} y) (2 : Nat))) (HMul.hMul.{0, 0, 0} (4 : Real) t)) (HSMul.hSMul.{0, u_1, u_1} (Neg.neg.{0} (HDiv.hDiv.{0, 0, 0} (1 : Real) (HMul.hMul.{0, 0, 0} (2 : Real) t))) ((innerSL.{0, u_1} Real) x)) x" with
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
  logInfo "FROZEN_CONTRACT_OK: Poincare.hasFDerivAt_neg_norm_sq_div"
run_cmd liftTermElabM do
  let info ← getConstInfo "Poincare.hasFDerivAt_exp_neg_norm_sq_div".toName
  let levels : List Level := [Level.param "u_1".toName]
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "∀ {E : Type u_1} [inst : NormedAddCommGroup.{u_1} E] [inst_1 : InnerProductSpace.{0, u_1} Real E] (t : Real), Ne.{1} t (0 : Real) → ∀ (x : E), HasFDerivAt.{0, u_1, 0} (fun (y : E) => Real.exp (HDiv.hDiv.{0, 0, 0} (Neg.neg.{0} (HPow.hPow.{0, 0, 0} (Norm.norm.{u_1} y) (2 : Nat))) (HMul.hMul.{0, 0, 0} (4 : Real) t))) (HSMul.hSMul.{0, u_1, u_1} (Real.exp (HDiv.hDiv.{0, 0, 0} (Neg.neg.{0} (HPow.hPow.{0, 0, 0} (Norm.norm.{u_1} x) (2 : Nat))) (HMul.hMul.{0, 0, 0} (4 : Real) t))) (HSMul.hSMul.{0, u_1, u_1} (Neg.neg.{0} (HDiv.hDiv.{0, 0, 0} (1 : Real) (HMul.hMul.{0, 0, 0} (2 : Real) t))) ((innerSL.{0, u_1} Real) x))) x" with
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
  logInfo "FROZEN_CONTRACT_OK: Poincare.hasFDerivAt_exp_neg_norm_sq_div"
run_cmd liftTermElabM do
  let info ← getConstInfo "Poincare.iteratedFDeriv_two_exp_neg_norm_sq_div_apply".toName
  let levels : List Level := [Level.param "u_1".toName]
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "∀ {E : Type u_1} [inst : NormedAddCommGroup.{u_1} E] [inst_1 : InnerProductSpace.{0, u_1} Real E] (t : Real), Ne.{1} t (0 : Real) → ∀ (x v : E), Eq.{1} ((iteratedFDeriv.{0, u_1, 0} Real (2 : Nat) (fun (y : E) => Real.exp (HDiv.hDiv.{0, 0, 0} (Neg.neg.{0} (HPow.hPow.{0, 0, 0} (Norm.norm.{u_1} y) (2 : Nat))) (HMul.hMul.{0, 0, 0} (4 : Real) t))) x) (Matrix.vecCons.{u_1} v (Matrix.vecCons.{u_1} v Matrix.vecEmpty.{u_1}))) (HMul.hMul.{0, 0, 0} (Real.exp (HDiv.hDiv.{0, 0, 0} (Neg.neg.{0} (HPow.hPow.{0, 0, 0} (Norm.norm.{u_1} x) (2 : Nat))) (HMul.hMul.{0, 0, 0} (4 : Real) t))) (HSub.hSub.{0, 0, 0} (HDiv.hDiv.{0, 0, 0} (HPow.hPow.{0, 0, 0} (Inner.inner.{0, u_1} Real x v) (2 : Nat)) (HMul.hMul.{0, 0, 0} (4 : Real) (HPow.hPow.{0, 0, 0} t (2 : Nat)))) (HDiv.hDiv.{0, 0, 0} (HPow.hPow.{0, 0, 0} (Norm.norm.{u_1} v) (2 : Nat)) (HMul.hMul.{0, 0, 0} (2 : Real) t))))" with
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
  logInfo "FROZEN_CONTRACT_OK: Poincare.iteratedFDeriv_two_exp_neg_norm_sq_div_apply"
run_cmd liftTermElabM do
  let info ← getConstInfo "Poincare.sum_sq_inner_stdOrthonormalBasis".toName
  let levels : List Level := [Level.param "u_1".toName]
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "∀ {E : Type u_1} [inst : NormedAddCommGroup.{u_1} E] [inst_1 : InnerProductSpace.{0, u_1} Real E] [inst_2 : FiniteDimensional.{0, u_1} Real E] (x : E), Eq.{1} (∑ i : Fin (Module.finrank.{0, u_1} Real E), HPow.hPow.{0, 0, 0} (Inner.inner.{0, u_1} Real x ((stdOrthonormalBasis.{0, u_1} Real E) i)) (2 : Nat)) (HPow.hPow.{0, 0, 0} (Norm.norm.{u_1} x) (2 : Nat))" with
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
  logInfo "FROZEN_CONTRACT_OK: Poincare.sum_sq_inner_stdOrthonormalBasis"
run_cmd liftTermElabM do
  let info ← getConstInfo "Poincare.laplacian_exp_neg_norm_sq_div".toName
  let levels : List Level := [Level.param "u_1".toName]
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "∀ {E : Type u_1} [inst : NormedAddCommGroup.{u_1} E] [inst_1 : InnerProductSpace.{0, u_1} Real E] [inst_2 : FiniteDimensional.{0, u_1} Real E] (t : Real), Ne.{1} t (0 : Real) → ∀ (x : E), Eq.{1} (Laplacian.laplacian.{u_1, u_1} (fun (y : E) => Real.exp (HDiv.hDiv.{0, 0, 0} (Neg.neg.{0} (HPow.hPow.{0, 0, 0} (Norm.norm.{u_1} y) (2 : Nat))) (HMul.hMul.{0, 0, 0} (4 : Real) t))) x) (HMul.hMul.{0, 0, 0} (Real.exp (HDiv.hDiv.{0, 0, 0} (Neg.neg.{0} (HPow.hPow.{0, 0, 0} (Norm.norm.{u_1} x) (2 : Nat))) (HMul.hMul.{0, 0, 0} (4 : Real) t))) (HSub.hSub.{0, 0, 0} (HDiv.hDiv.{0, 0, 0} (HPow.hPow.{0, 0, 0} (Norm.norm.{u_1} x) (2 : Nat)) (HMul.hMul.{0, 0, 0} (4 : Real) (HPow.hPow.{0, 0, 0} t (2 : Nat)))) (HDiv.hDiv.{0, 0, 0} (↑(Module.finrank.{0, u_1} Real E)) (HMul.hMul.{0, 0, 0} (2 : Real) t))))" with
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
  logInfo "FROZEN_CONTRACT_OK: Poincare.laplacian_exp_neg_norm_sq_div"
run_cmd liftTermElabM do
  let info ← getConstInfo "Poincare.heatKernel_heatEquation_laplacian".toName
  let levels : List Level := [Level.param "u_2".toName]
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "∀ {E : Type u_2} [inst : NormedAddCommGroup.{u_2} E] [inst_1 : InnerProductSpace.{0, u_2} Real E] [inst_2 : FiniteDimensional.{0, u_2} Real E] {t : Real}, LT.lt.{0} (0 : Real) t → ∀ (x : E), Eq.{1} (deriv.{0, 0} (fun (τ : Real) => Poincare.heatKernel.{u_2} τ x) t) (Laplacian.laplacian.{u_2, u_2} (fun (y : E) => Poincare.heatKernel.{u_2} t y) x)" with
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
  logInfo "FROZEN_CONTRACT_OK: Poincare.heatKernel_heatEquation_laplacian"
