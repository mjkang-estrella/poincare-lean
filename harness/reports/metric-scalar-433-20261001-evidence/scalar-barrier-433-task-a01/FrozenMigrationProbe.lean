import Lean
import Poincare.Global.ScalarCurvatureBarrier
open Lean Elab Command Meta
set_option autoImplicit false
run_cmd do
  let name := "Poincare.hasDerivWithinAt_neg_inv".toName
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
  logInfo "AXIOM_CONTRACT_OK: Poincare.hasDerivWithinAt_neg_inv"
run_cmd do
  let name := "Poincare.negative_reciprocal_growth_bound".toName
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
  logInfo "AXIOM_CONTRACT_OK: Poincare.negative_reciprocal_growth_bound"
run_cmd do
  let name := "Poincare.riccati_monotoneOn".toName
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
  logInfo "AXIOM_CONTRACT_OK: Poincare.riccati_monotoneOn"
run_cmd do
  let name := "Poincare.negative_reciprocal_initial_bound".toName
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
  logInfo "AXIOM_CONTRACT_OK: Poincare.negative_reciprocal_initial_bound"
run_cmd do
  let name := "Poincare.lower_bound_of_negative_reciprocal_bound".toName
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
  logInfo "AXIOM_CONTRACT_OK: Poincare.lower_bound_of_negative_reciprocal_bound"
run_cmd do
  let name := "Poincare.riccati_lower_barrier_of_negative".toName
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
  logInfo "AXIOM_CONTRACT_OK: Poincare.riccati_lower_barrier_of_negative"
run_cmd do
  let name := "Poincare.riccati_lower_barrier".toName
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
  logInfo "AXIOM_CONTRACT_OK: Poincare.riccati_lower_barrier"
run_cmd do
  let name := "Poincare.three_dimensional_scalar_curvature_lower_barrier_of_negative".toName
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
  logInfo "AXIOM_CONTRACT_OK: Poincare.three_dimensional_scalar_curvature_lower_barrier_of_negative"
run_cmd do
  let name := "Poincare.three_dimensional_scalar_curvature_lower_barrier".toName
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
  logInfo "AXIOM_CONTRACT_OK: Poincare.three_dimensional_scalar_curvature_lower_barrier"
run_cmd do
  let name := "Poincare.segmented_negative_reciprocal_growth_bound".toName
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
  logInfo "AXIOM_CONTRACT_OK: Poincare.segmented_negative_reciprocal_growth_bound"
run_cmd do
  let name := "Poincare.segmented_riccati_lower_barrier_of_negative".toName
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
  logInfo "AXIOM_CONTRACT_OK: Poincare.segmented_riccati_lower_barrier_of_negative"
run_cmd do
  let name := "Poincare.three_dimensional_scalar_curvature_segmented_lower_barrier_of_negative".toName
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
  logInfo "AXIOM_CONTRACT_OK: Poincare.three_dimensional_scalar_curvature_segmented_lower_barrier_of_negative"
run_cmd do
  let name := "Poincare.segmented_riccati_pointwise_lower_barrier_of_negative".toName
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
  logInfo "AXIOM_CONTRACT_OK: Poincare.segmented_riccati_pointwise_lower_barrier_of_negative"
run_cmd do
  let name := "Poincare.segmented_riccati_pointwise_lower_barrier".toName
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
  logInfo "AXIOM_CONTRACT_OK: Poincare.segmented_riccati_pointwise_lower_barrier"
run_cmd do
  let name := "Poincare.three_dimensional_scalar_curvature_segmented_pointwise_lower_barrier_of_negative".toName
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
  logInfo "AXIOM_CONTRACT_OK: Poincare.three_dimensional_scalar_curvature_segmented_pointwise_lower_barrier_of_negative"
run_cmd do
  let name := "Poincare.three_dimensional_scalar_curvature_segmented_pointwise_lower_barrier".toName
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
  logInfo "AXIOM_CONTRACT_OK: Poincare.three_dimensional_scalar_curvature_segmented_pointwise_lower_barrier"
run_cmd liftTermElabM do
  let info ← getConstInfo "Poincare.hasDerivWithinAt_neg_inv".toName
  let levels : List Level := []
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "∀ {r : Real → Real} {dr t : Real} {s : Set.{0} Real}, HasDerivWithinAt.{0, 0} r dr s t → Ne.{1} (r t) (0 : Real) → HasDerivWithinAt.{0, 0} (fun (x : Real) => Neg.neg.{0} (Inv.inv.{0} (r x))) (HDiv.hDiv.{0, 0, 0} dr (HPow.hPow.{0, 0, 0} (r t) (2 : Nat))) s t" with
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
  logInfo "FROZEN_CONTRACT_OK: Poincare.hasDerivWithinAt_neg_inv"
run_cmd liftTermElabM do
  let info ← getConstInfo "Poincare.negative_reciprocal_growth_bound".toName
  let levels : List Level := []
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "∀ {a b κ : Real}, LE.le.{0} a b → ∀ (r dr : Real → Real), ContinuousOn.{0, 0} r (Set.Icc.{0} a b) → (∀ (t : Real), Membership.mem.{0, 0} (Set.Icc.{0} a b) t → LT.lt.{0} (r t) (0 : Real)) → (∀ (t : Real), Membership.mem.{0, 0} (Set.Ioo.{0} a b) t → HasDerivWithinAt.{0, 0} r (dr t) (Set.Ioi.{0} t) t) → (∀ (t : Real), Membership.mem.{0, 0} (Set.Ioo.{0} a b) t → LE.le.{0} (HMul.hMul.{0, 0, 0} κ (HPow.hPow.{0, 0, 0} (r t) (2 : Nat))) (dr t)) → LE.le.{0} (HMul.hMul.{0, 0, 0} κ (HSub.hSub.{0, 0, 0} b a)) (HSub.hSub.{0, 0, 0} (Neg.neg.{0} (Inv.inv.{0} (r b))) (Neg.neg.{0} (Inv.inv.{0} (r a))))" with
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
  logInfo "FROZEN_CONTRACT_OK: Poincare.negative_reciprocal_growth_bound"
run_cmd liftTermElabM do
  let info ← getConstInfo "Poincare.riccati_monotoneOn".toName
  let levels : List Level := []
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "∀ {a b κ : Real}, LE.le.{0} a b → LE.le.{0} (0 : Real) κ → ∀ (r dr : Real → Real), ContinuousOn.{0, 0} r (Set.Icc.{0} a b) → (∀ (t : Real), Membership.mem.{0, 0} (Set.Ioo.{0} a b) t → HasDerivWithinAt.{0, 0} r (dr t) (Set.Ioi.{0} t) t) → (∀ (t : Real), Membership.mem.{0, 0} (Set.Ioo.{0} a b) t → LE.le.{0} (HMul.hMul.{0, 0, 0} κ (HPow.hPow.{0, 0, 0} (r t) (2 : Nat))) (dr t)) → MonotoneOn.{0, 0} r (Set.Icc.{0} a b)" with
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
  logInfo "FROZEN_CONTRACT_OK: Poincare.riccati_monotoneOn"
run_cmd liftTermElabM do
  let info ← getConstInfo "Poincare.negative_reciprocal_initial_bound".toName
  let levels : List Level := []
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "∀ {r L : Real}, LT.lt.{0} r (0 : Real) → LT.lt.{0} (0 : Real) L → LE.le.{0} (Neg.neg.{0} (Inv.inv.{0} L)) r → LE.le.{0} L (Neg.neg.{0} (Inv.inv.{0} r))" with
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
  logInfo "FROZEN_CONTRACT_OK: Poincare.negative_reciprocal_initial_bound"
run_cmd liftTermElabM do
  let info ← getConstInfo "Poincare.lower_bound_of_negative_reciprocal_bound".toName
  let levels : List Level := []
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "∀ {r L : Real}, LT.lt.{0} r (0 : Real) → LT.lt.{0} (0 : Real) L → LE.le.{0} L (Neg.neg.{0} (Inv.inv.{0} r)) → LE.le.{0} (Neg.neg.{0} (Inv.inv.{0} L)) r" with
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
  logInfo "FROZEN_CONTRACT_OK: Poincare.lower_bound_of_negative_reciprocal_bound"
run_cmd liftTermElabM do
  let info ← getConstInfo "Poincare.riccati_lower_barrier_of_negative".toName
  let levels : List Level := []
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "∀ {a b κ C : Real}, LE.le.{0} a b → LT.lt.{0} (0 : Real) κ → LT.lt.{0} (0 : Real) C → ∀ (r dr : Real → Real), ContinuousOn.{0, 0} r (Set.Icc.{0} a b) → (∀ (t : Real), Membership.mem.{0, 0} (Set.Icc.{0} a b) t → LT.lt.{0} (r t) (0 : Real)) → (∀ (t : Real), Membership.mem.{0, 0} (Set.Ioo.{0} a b) t → HasDerivWithinAt.{0, 0} r (dr t) (Set.Ioi.{0} t) t) → (∀ (t : Real), Membership.mem.{0, 0} (Set.Ioo.{0} a b) t → LE.le.{0} (HMul.hMul.{0, 0, 0} κ (HPow.hPow.{0, 0, 0} (r t) (2 : Nat))) (dr t)) → LE.le.{0} (Neg.neg.{0} (Inv.inv.{0} (HMul.hMul.{0, 0, 0} κ C))) (r a) → LE.le.{0} (Neg.neg.{0} (Inv.inv.{0} (HMul.hMul.{0, 0, 0} κ (HAdd.hAdd.{0, 0, 0} C (HSub.hSub.{0, 0, 0} b a))))) (r b)" with
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
  logInfo "FROZEN_CONTRACT_OK: Poincare.riccati_lower_barrier_of_negative"
run_cmd liftTermElabM do
  let info ← getConstInfo "Poincare.riccati_lower_barrier".toName
  let levels : List Level := []
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "∀ {a b κ C : Real}, LE.le.{0} a b → LT.lt.{0} (0 : Real) κ → LT.lt.{0} (0 : Real) C → ∀ (r dr : Real → Real), ContinuousOn.{0, 0} r (Set.Icc.{0} a b) → (∀ (t : Real), Membership.mem.{0, 0} (Set.Ioo.{0} a b) t → HasDerivWithinAt.{0, 0} r (dr t) (Set.Ioi.{0} t) t) → (∀ (t : Real), Membership.mem.{0, 0} (Set.Ioo.{0} a b) t → LE.le.{0} (HMul.hMul.{0, 0, 0} κ (HPow.hPow.{0, 0, 0} (r t) (2 : Nat))) (dr t)) → LE.le.{0} (Neg.neg.{0} (Inv.inv.{0} (HMul.hMul.{0, 0, 0} κ C))) (r a) → LE.le.{0} (Neg.neg.{0} (Inv.inv.{0} (HMul.hMul.{0, 0, 0} κ (HAdd.hAdd.{0, 0, 0} C (HSub.hSub.{0, 0, 0} b a))))) (r b)" with
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
  logInfo "FROZEN_CONTRACT_OK: Poincare.riccati_lower_barrier"
run_cmd liftTermElabM do
  let info ← getConstInfo "Poincare.three_dimensional_scalar_curvature_lower_barrier_of_negative".toName
  let levels : List Level := []
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "∀ {a b C : Real}, LE.le.{0} a b → LT.lt.{0} (0 : Real) C → ∀ (r dr : Real → Real), ContinuousOn.{0, 0} r (Set.Icc.{0} a b) → (∀ (t : Real), Membership.mem.{0, 0} (Set.Icc.{0} a b) t → LT.lt.{0} (r t) (0 : Real)) → (∀ (t : Real), Membership.mem.{0, 0} (Set.Ioo.{0} a b) t → HasDerivWithinAt.{0, 0} r (dr t) (Set.Ioi.{0} t) t) → (∀ (t : Real), Membership.mem.{0, 0} (Set.Ioo.{0} a b) t → LE.le.{0} (HMul.hMul.{0, 0, 0} (2 / 3 : Real) (HPow.hPow.{0, 0, 0} (r t) (2 : Nat))) (dr t)) → LE.le.{0} (Neg.neg.{0} (HDiv.hDiv.{0, 0, 0} (3 : Real) (HMul.hMul.{0, 0, 0} (2 : Real) C))) (r a) → LE.le.{0} (Neg.neg.{0} (HDiv.hDiv.{0, 0, 0} (3 : Real) (HMul.hMul.{0, 0, 0} (2 : Real) (HAdd.hAdd.{0, 0, 0} C (HSub.hSub.{0, 0, 0} b a))))) (r b)" with
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
  logInfo "FROZEN_CONTRACT_OK: Poincare.three_dimensional_scalar_curvature_lower_barrier_of_negative"
run_cmd liftTermElabM do
  let info ← getConstInfo "Poincare.three_dimensional_scalar_curvature_lower_barrier".toName
  let levels : List Level := []
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "∀ {a b C : Real}, LE.le.{0} a b → LT.lt.{0} (0 : Real) C → ∀ (r dr : Real → Real), ContinuousOn.{0, 0} r (Set.Icc.{0} a b) → (∀ (t : Real), Membership.mem.{0, 0} (Set.Ioo.{0} a b) t → HasDerivWithinAt.{0, 0} r (dr t) (Set.Ioi.{0} t) t) → (∀ (t : Real), Membership.mem.{0, 0} (Set.Ioo.{0} a b) t → LE.le.{0} (HMul.hMul.{0, 0, 0} (2 / 3 : Real) (HPow.hPow.{0, 0, 0} (r t) (2 : Nat))) (dr t)) → LE.le.{0} (Neg.neg.{0} (HDiv.hDiv.{0, 0, 0} (3 : Real) (HMul.hMul.{0, 0, 0} (2 : Real) C))) (r a) → LE.le.{0} (Neg.neg.{0} (HDiv.hDiv.{0, 0, 0} (3 : Real) (HMul.hMul.{0, 0, 0} (2 : Real) (HAdd.hAdd.{0, 0, 0} C (HSub.hSub.{0, 0, 0} b a))))) (r b)" with
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
  logInfo "FROZEN_CONTRACT_OK: Poincare.three_dimensional_scalar_curvature_lower_barrier"
run_cmd liftTermElabM do
  let info ← getConstInfo "Poincare.segmented_negative_reciprocal_growth_bound".toName
  let levels : List Level := []
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "∀ {κ : Real} (r dr : Nat → Real → Real) (start : Nat → Real) (n : Nat), (∀ (k : Nat), LT.lt.{0} k n → LE.le.{0} (start k) (start (HAdd.hAdd.{0, 0, 0} k (1 : Nat)))) → (∀ (k : Nat), LT.lt.{0} k n → ContinuousOn.{0, 0} (r k) (Set.Icc.{0} (start k) (start (HAdd.hAdd.{0, 0, 0} k (1 : Nat))))) → (∀ (k : Nat), LE.le.{0} k n → LT.lt.{0} (r k (start k)) (0 : Real)) → (∀ (k : Nat), LT.lt.{0} k n → ∀ (t : Real), Membership.mem.{0, 0} (Set.Icc.{0} (start k) (start (HAdd.hAdd.{0, 0, 0} k (1 : Nat)))) t → LT.lt.{0} (r k t) (0 : Real)) → (∀ (k : Nat), LT.lt.{0} k n → ∀ (t : Real), Membership.mem.{0, 0} (Set.Ioo.{0} (start k) (start (HAdd.hAdd.{0, 0, 0} k (1 : Nat)))) t → HasDerivWithinAt.{0, 0} (r k) (dr k t) (Set.Ioi.{0} t) t) → (∀ (k : Nat), LT.lt.{0} k n → ∀ (t : Real), Membership.mem.{0, 0} (Set.Ioo.{0} (start k) (start (HAdd.hAdd.{0, 0, 0} k (1 : Nat)))) t → LE.le.{0} (HMul.hMul.{0, 0, 0} κ (HPow.hPow.{0, 0, 0} (r k t) (2 : Nat))) (dr k t)) → (∀ (k : Nat), LT.lt.{0} k n → LE.le.{0} (r k (start (HAdd.hAdd.{0, 0, 0} k (1 : Nat)))) (r (HAdd.hAdd.{0, 0, 0} k (1 : Nat)) (start (HAdd.hAdd.{0, 0, 0} k (1 : Nat))))) → LE.le.{0} (HMul.hMul.{0, 0, 0} κ (HSub.hSub.{0, 0, 0} (start n) (start (0 : Nat)))) (HSub.hSub.{0, 0, 0} (Neg.neg.{0} (Inv.inv.{0} (r n (start n)))) (Neg.neg.{0} (Inv.inv.{0} (r (0 : Nat) (start (0 : Nat))))))" with
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
  logInfo "FROZEN_CONTRACT_OK: Poincare.segmented_negative_reciprocal_growth_bound"
run_cmd liftTermElabM do
  let info ← getConstInfo "Poincare.segmented_riccati_lower_barrier_of_negative".toName
  let levels : List Level := []
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "∀ {κ C : Real}, LT.lt.{0} (0 : Real) κ → LT.lt.{0} (0 : Real) C → ∀ (r dr : Nat → Real → Real) (start : Nat → Real) (n : Nat), LE.le.{0} (0 : Real) (HSub.hSub.{0, 0, 0} (start n) (start (0 : Nat))) → (∀ (k : Nat), LT.lt.{0} k n → LE.le.{0} (start k) (start (HAdd.hAdd.{0, 0, 0} k (1 : Nat)))) → (∀ (k : Nat), LT.lt.{0} k n → ContinuousOn.{0, 0} (r k) (Set.Icc.{0} (start k) (start (HAdd.hAdd.{0, 0, 0} k (1 : Nat))))) → (∀ (k : Nat), LE.le.{0} k n → LT.lt.{0} (r k (start k)) (0 : Real)) → (∀ (k : Nat), LT.lt.{0} k n → ∀ (t : Real), Membership.mem.{0, 0} (Set.Icc.{0} (start k) (start (HAdd.hAdd.{0, 0, 0} k (1 : Nat)))) t → LT.lt.{0} (r k t) (0 : Real)) → (∀ (k : Nat), LT.lt.{0} k n → ∀ (t : Real), Membership.mem.{0, 0} (Set.Ioo.{0} (start k) (start (HAdd.hAdd.{0, 0, 0} k (1 : Nat)))) t → HasDerivWithinAt.{0, 0} (r k) (dr k t) (Set.Ioi.{0} t) t) → (∀ (k : Nat), LT.lt.{0} k n → ∀ (t : Real), Membership.mem.{0, 0} (Set.Ioo.{0} (start k) (start (HAdd.hAdd.{0, 0, 0} k (1 : Nat)))) t → LE.le.{0} (HMul.hMul.{0, 0, 0} κ (HPow.hPow.{0, 0, 0} (r k t) (2 : Nat))) (dr k t)) → (∀ (k : Nat), LT.lt.{0} k n → LE.le.{0} (r k (start (HAdd.hAdd.{0, 0, 0} k (1 : Nat)))) (r (HAdd.hAdd.{0, 0, 0} k (1 : Nat)) (start (HAdd.hAdd.{0, 0, 0} k (1 : Nat))))) → LE.le.{0} (Neg.neg.{0} (Inv.inv.{0} (HMul.hMul.{0, 0, 0} κ C))) (r (0 : Nat) (start (0 : Nat))) → LE.le.{0} (Neg.neg.{0} (Inv.inv.{0} (HMul.hMul.{0, 0, 0} κ (HAdd.hAdd.{0, 0, 0} C (HSub.hSub.{0, 0, 0} (start n) (start (0 : Nat))))))) (r n (start n))" with
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
  logInfo "FROZEN_CONTRACT_OK: Poincare.segmented_riccati_lower_barrier_of_negative"
run_cmd liftTermElabM do
  let info ← getConstInfo "Poincare.three_dimensional_scalar_curvature_segmented_lower_barrier_of_negative".toName
  let levels : List Level := []
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "∀ {C : Real}, LT.lt.{0} (0 : Real) C → ∀ (r dr : Nat → Real → Real) (start : Nat → Real) (n : Nat), LE.le.{0} (0 : Real) (HSub.hSub.{0, 0, 0} (start n) (start (0 : Nat))) → (∀ (k : Nat), LT.lt.{0} k n → LE.le.{0} (start k) (start (HAdd.hAdd.{0, 0, 0} k (1 : Nat)))) → (∀ (k : Nat), LT.lt.{0} k n → ContinuousOn.{0, 0} (r k) (Set.Icc.{0} (start k) (start (HAdd.hAdd.{0, 0, 0} k (1 : Nat))))) → (∀ (k : Nat), LE.le.{0} k n → LT.lt.{0} (r k (start k)) (0 : Real)) → (∀ (k : Nat), LT.lt.{0} k n → ∀ (t : Real), Membership.mem.{0, 0} (Set.Icc.{0} (start k) (start (HAdd.hAdd.{0, 0, 0} k (1 : Nat)))) t → LT.lt.{0} (r k t) (0 : Real)) → (∀ (k : Nat), LT.lt.{0} k n → ∀ (t : Real), Membership.mem.{0, 0} (Set.Ioo.{0} (start k) (start (HAdd.hAdd.{0, 0, 0} k (1 : Nat)))) t → HasDerivWithinAt.{0, 0} (r k) (dr k t) (Set.Ioi.{0} t) t) → (∀ (k : Nat), LT.lt.{0} k n → ∀ (t : Real), Membership.mem.{0, 0} (Set.Ioo.{0} (start k) (start (HAdd.hAdd.{0, 0, 0} k (1 : Nat)))) t → LE.le.{0} (HMul.hMul.{0, 0, 0} (2 / 3 : Real) (HPow.hPow.{0, 0, 0} (r k t) (2 : Nat))) (dr k t)) → (∀ (k : Nat), LT.lt.{0} k n → LE.le.{0} (r k (start (HAdd.hAdd.{0, 0, 0} k (1 : Nat)))) (r (HAdd.hAdd.{0, 0, 0} k (1 : Nat)) (start (HAdd.hAdd.{0, 0, 0} k (1 : Nat))))) → LE.le.{0} (Neg.neg.{0} (HDiv.hDiv.{0, 0, 0} (3 : Real) (HMul.hMul.{0, 0, 0} (2 : Real) C))) (r (0 : Nat) (start (0 : Nat))) → LE.le.{0} (Neg.neg.{0} (HDiv.hDiv.{0, 0, 0} (3 : Real) (HMul.hMul.{0, 0, 0} (2 : Real) (HAdd.hAdd.{0, 0, 0} C (HSub.hSub.{0, 0, 0} (start n) (start (0 : Nat))))))) (r n (start n))" with
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
  logInfo "FROZEN_CONTRACT_OK: Poincare.three_dimensional_scalar_curvature_segmented_lower_barrier_of_negative"
run_cmd liftTermElabM do
  let info ← getConstInfo "Poincare.segmented_riccati_pointwise_lower_barrier_of_negative".toName
  let levels : List Level := []
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "∀ {κ C : Real}, LT.lt.{0} (0 : Real) κ → LT.lt.{0} (0 : Real) C → ∀ (r dr : Nat → Real → Real) (start : Nat → Real), (∀ (k : Nat), LE.le.{0} (start k) (start (HAdd.hAdd.{0, 0, 0} k (1 : Nat)))) → (∀ (k : Nat), ContinuousOn.{0, 0} (r k) (Set.Icc.{0} (start k) (start (HAdd.hAdd.{0, 0, 0} k (1 : Nat))))) → (∀ (k : Nat), LT.lt.{0} (r k (start k)) (0 : Real)) → (∀ (k : Nat) (t : Real), Membership.mem.{0, 0} (Set.Icc.{0} (start k) (start (HAdd.hAdd.{0, 0, 0} k (1 : Nat)))) t → LT.lt.{0} (r k t) (0 : Real)) → (∀ (k : Nat) (t : Real), Membership.mem.{0, 0} (Set.Ioo.{0} (start k) (start (HAdd.hAdd.{0, 0, 0} k (1 : Nat)))) t → HasDerivWithinAt.{0, 0} (r k) (dr k t) (Set.Ioi.{0} t) t) → (∀ (k : Nat) (t : Real), Membership.mem.{0, 0} (Set.Ioo.{0} (start k) (start (HAdd.hAdd.{0, 0, 0} k (1 : Nat)))) t → LE.le.{0} (HMul.hMul.{0, 0, 0} κ (HPow.hPow.{0, 0, 0} (r k t) (2 : Nat))) (dr k t)) → (∀ (k : Nat), LE.le.{0} (r k (start (HAdd.hAdd.{0, 0, 0} k (1 : Nat)))) (r (HAdd.hAdd.{0, 0, 0} k (1 : Nat)) (start (HAdd.hAdd.{0, 0, 0} k (1 : Nat))))) → LE.le.{0} (Neg.neg.{0} (Inv.inv.{0} (HMul.hMul.{0, 0, 0} κ C))) (r (0 : Nat) (start (0 : Nat))) → ∀ (k : Nat) (t : Real), Membership.mem.{0, 0} (Set.Icc.{0} (start k) (start (HAdd.hAdd.{0, 0, 0} k (1 : Nat)))) t → LE.le.{0} (Neg.neg.{0} (Inv.inv.{0} (HMul.hMul.{0, 0, 0} κ (HAdd.hAdd.{0, 0, 0} C (HSub.hSub.{0, 0, 0} t (start (0 : Nat))))))) (r k t)" with
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
  logInfo "FROZEN_CONTRACT_OK: Poincare.segmented_riccati_pointwise_lower_barrier_of_negative"
run_cmd liftTermElabM do
  let info ← getConstInfo "Poincare.segmented_riccati_pointwise_lower_barrier".toName
  let levels : List Level := []
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "∀ {κ C : Real}, LT.lt.{0} (0 : Real) κ → LT.lt.{0} (0 : Real) C → ∀ (r dr : Nat → Real → Real) (start : Nat → Real), (∀ (k : Nat), LE.le.{0} (start k) (start (HAdd.hAdd.{0, 0, 0} k (1 : Nat)))) → (∀ (k : Nat), ContinuousOn.{0, 0} (r k) (Set.Icc.{0} (start k) (start (HAdd.hAdd.{0, 0, 0} k (1 : Nat))))) → (∀ (k : Nat) (t : Real), Membership.mem.{0, 0} (Set.Ioo.{0} (start k) (start (HAdd.hAdd.{0, 0, 0} k (1 : Nat)))) t → HasDerivWithinAt.{0, 0} (r k) (dr k t) (Set.Ioi.{0} t) t) → (∀ (k : Nat) (t : Real), Membership.mem.{0, 0} (Set.Ioo.{0} (start k) (start (HAdd.hAdd.{0, 0, 0} k (1 : Nat)))) t → LE.le.{0} (HMul.hMul.{0, 0, 0} κ (HPow.hPow.{0, 0, 0} (r k t) (2 : Nat))) (dr k t)) → (∀ (k : Nat), LE.le.{0} (r k (start (HAdd.hAdd.{0, 0, 0} k (1 : Nat)))) (r (HAdd.hAdd.{0, 0, 0} k (1 : Nat)) (start (HAdd.hAdd.{0, 0, 0} k (1 : Nat))))) → LE.le.{0} (Neg.neg.{0} (Inv.inv.{0} (HMul.hMul.{0, 0, 0} κ C))) (r (0 : Nat) (start (0 : Nat))) → ∀ (k : Nat) (t : Real), Membership.mem.{0, 0} (Set.Icc.{0} (start k) (start (HAdd.hAdd.{0, 0, 0} k (1 : Nat)))) t → LE.le.{0} (Neg.neg.{0} (Inv.inv.{0} (HMul.hMul.{0, 0, 0} κ (HAdd.hAdd.{0, 0, 0} C (HSub.hSub.{0, 0, 0} t (start (0 : Nat))))))) (r k t)" with
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
  logInfo "FROZEN_CONTRACT_OK: Poincare.segmented_riccati_pointwise_lower_barrier"
run_cmd liftTermElabM do
  let info ← getConstInfo "Poincare.three_dimensional_scalar_curvature_segmented_pointwise_lower_barrier_of_negative".toName
  let levels : List Level := []
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "∀ {C : Real}, LT.lt.{0} (0 : Real) C → ∀ (r dr : Nat → Real → Real) (start : Nat → Real), (∀ (k : Nat), LE.le.{0} (start k) (start (HAdd.hAdd.{0, 0, 0} k (1 : Nat)))) → (∀ (k : Nat), ContinuousOn.{0, 0} (r k) (Set.Icc.{0} (start k) (start (HAdd.hAdd.{0, 0, 0} k (1 : Nat))))) → (∀ (k : Nat), LT.lt.{0} (r k (start k)) (0 : Real)) → (∀ (k : Nat) (t : Real), Membership.mem.{0, 0} (Set.Icc.{0} (start k) (start (HAdd.hAdd.{0, 0, 0} k (1 : Nat)))) t → LT.lt.{0} (r k t) (0 : Real)) → (∀ (k : Nat) (t : Real), Membership.mem.{0, 0} (Set.Ioo.{0} (start k) (start (HAdd.hAdd.{0, 0, 0} k (1 : Nat)))) t → HasDerivWithinAt.{0, 0} (r k) (dr k t) (Set.Ioi.{0} t) t) → (∀ (k : Nat) (t : Real), Membership.mem.{0, 0} (Set.Ioo.{0} (start k) (start (HAdd.hAdd.{0, 0, 0} k (1 : Nat)))) t → LE.le.{0} (HMul.hMul.{0, 0, 0} (2 / 3 : Real) (HPow.hPow.{0, 0, 0} (r k t) (2 : Nat))) (dr k t)) → (∀ (k : Nat), LE.le.{0} (r k (start (HAdd.hAdd.{0, 0, 0} k (1 : Nat)))) (r (HAdd.hAdd.{0, 0, 0} k (1 : Nat)) (start (HAdd.hAdd.{0, 0, 0} k (1 : Nat))))) → LE.le.{0} (Neg.neg.{0} (HDiv.hDiv.{0, 0, 0} (3 : Real) (HMul.hMul.{0, 0, 0} (2 : Real) C))) (r (0 : Nat) (start (0 : Nat))) → ∀ (k : Nat) (t : Real), Membership.mem.{0, 0} (Set.Icc.{0} (start k) (start (HAdd.hAdd.{0, 0, 0} k (1 : Nat)))) t → LE.le.{0} (Neg.neg.{0} (HDiv.hDiv.{0, 0, 0} (3 : Real) (HMul.hMul.{0, 0, 0} (2 : Real) (HAdd.hAdd.{0, 0, 0} C (HSub.hSub.{0, 0, 0} t (start (0 : Nat))))))) (r k t)" with
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
  logInfo "FROZEN_CONTRACT_OK: Poincare.three_dimensional_scalar_curvature_segmented_pointwise_lower_barrier_of_negative"
run_cmd liftTermElabM do
  let info ← getConstInfo "Poincare.three_dimensional_scalar_curvature_segmented_pointwise_lower_barrier".toName
  let levels : List Level := []
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "∀ {C : Real}, LT.lt.{0} (0 : Real) C → ∀ (r dr : Nat → Real → Real) (start : Nat → Real), (∀ (k : Nat), LE.le.{0} (start k) (start (HAdd.hAdd.{0, 0, 0} k (1 : Nat)))) → (∀ (k : Nat), ContinuousOn.{0, 0} (r k) (Set.Icc.{0} (start k) (start (HAdd.hAdd.{0, 0, 0} k (1 : Nat))))) → (∀ (k : Nat) (t : Real), Membership.mem.{0, 0} (Set.Ioo.{0} (start k) (start (HAdd.hAdd.{0, 0, 0} k (1 : Nat)))) t → HasDerivWithinAt.{0, 0} (r k) (dr k t) (Set.Ioi.{0} t) t) → (∀ (k : Nat) (t : Real), Membership.mem.{0, 0} (Set.Ioo.{0} (start k) (start (HAdd.hAdd.{0, 0, 0} k (1 : Nat)))) t → LE.le.{0} (HMul.hMul.{0, 0, 0} (2 / 3 : Real) (HPow.hPow.{0, 0, 0} (r k t) (2 : Nat))) (dr k t)) → (∀ (k : Nat), LE.le.{0} (r k (start (HAdd.hAdd.{0, 0, 0} k (1 : Nat)))) (r (HAdd.hAdd.{0, 0, 0} k (1 : Nat)) (start (HAdd.hAdd.{0, 0, 0} k (1 : Nat))))) → LE.le.{0} (Neg.neg.{0} (HDiv.hDiv.{0, 0, 0} (3 : Real) (HMul.hMul.{0, 0, 0} (2 : Real) C))) (r (0 : Nat) (start (0 : Nat))) → ∀ (k : Nat) (t : Real), Membership.mem.{0, 0} (Set.Icc.{0} (start k) (start (HAdd.hAdd.{0, 0, 0} k (1 : Nat)))) t → LE.le.{0} (Neg.neg.{0} (HDiv.hDiv.{0, 0, 0} (3 : Real) (HMul.hMul.{0, 0, 0} (2 : Real) (HAdd.hAdd.{0, 0, 0} C (HSub.hSub.{0, 0, 0} t (start (0 : Nat))))))) (r k t)" with
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
  logInfo "FROZEN_CONTRACT_OK: Poincare.three_dimensional_scalar_curvature_segmented_pointwise_lower_barrier"
