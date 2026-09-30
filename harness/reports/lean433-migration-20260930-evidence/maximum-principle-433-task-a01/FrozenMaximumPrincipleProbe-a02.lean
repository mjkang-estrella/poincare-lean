import Lean
import Poincare.MaximumPrinciple
open Lean Elab Command Meta
set_option autoImplicit false
run_cmd do
  let name := "RicciFlow.ode_comparison_nonpos".toName
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
  logInfo "AXIOM_CONTRACT_OK: RicciFlow.ode_comparison_nonpos"
run_cmd do
  let name := "RicciFlow.ode_comparison_nonneg".toName
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
  logInfo "AXIOM_CONTRACT_OK: RicciFlow.ode_comparison_nonneg"
run_cmd do
  let name := "RicciFlow.riccati_lower_bound".toName
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
  logInfo "AXIOM_CONTRACT_OK: RicciFlow.riccati_lower_bound"
run_cmd do
  let name := "RicciFlow.riccati_forces_finite_time".toName
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
  logInfo "AXIOM_CONTRACT_OK: RicciFlow.riccati_forces_finite_time"
run_cmd do
  let name := "RicciFlow.einstein_scalar_hasDerivAt_riccati".toName
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
  logInfo "AXIOM_CONTRACT_OK: RicciFlow.einstein_scalar_hasDerivAt_riccati"
run_cmd do
  let name := "RicciFlow.riccati_upper_bound".toName
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
  logInfo "AXIOM_CONTRACT_OK: RicciFlow.riccati_upper_bound"
run_cmd do
  let name := "RicciFlow.riccati_doubling_time".toName
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
  logInfo "AXIOM_CONTRACT_OK: RicciFlow.riccati_doubling_time"
run_cmd do
  let name := "RicciFlow.secondDeriv_nonneg_of_isLocalMin".toName
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
  logInfo "AXIOM_CONTRACT_OK: RicciFlow.secondDeriv_nonneg_of_isLocalMin"
run_cmd do
  let name := "RicciFlow.hessian_nonneg_of_isLocalMin".toName
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
  logInfo "AXIOM_CONTRACT_OK: RicciFlow.hessian_nonneg_of_isLocalMin"
run_cmd do
  let name := "RicciFlow.fderiv_fderiv_nonneg_of_isLocalMin_contDiffAt".toName
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
  logInfo "AXIOM_CONTRACT_OK: RicciFlow.fderiv_fderiv_nonneg_of_isLocalMin_contDiffAt"
run_cmd do
  let name := "RicciFlow.exists_first_zero".toName
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
  logInfo "AXIOM_CONTRACT_OK: RicciFlow.exists_first_zero"
run_cmd do
  let name := "RicciFlow.ode_comparison_nonpos_eq".toName
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
  logInfo "AXIOM_CONTRACT_OK: RicciFlow.ode_comparison_nonpos_eq"
run_cmd do
  let name := "RicciFlow.ode_comparison_nonneg_eq".toName
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
  logInfo "AXIOM_CONTRACT_OK: RicciFlow.ode_comparison_nonneg_eq"
run_cmd do
  let name := "RicciFlow.riccati_lower_bound_eq".toName
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
  logInfo "AXIOM_CONTRACT_OK: RicciFlow.riccati_lower_bound_eq"
run_cmd do
  let name := "RicciFlow.riccati_forces_finite_time_eq".toName
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
  logInfo "AXIOM_CONTRACT_OK: RicciFlow.riccati_forces_finite_time_eq"
run_cmd do
  let name := "RicciFlow.einstein_scalar_hasDerivAt_riccati_eq".toName
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
  logInfo "AXIOM_CONTRACT_OK: RicciFlow.einstein_scalar_hasDerivAt_riccati_eq"
run_cmd do
  let name := "RicciFlow.riccati_upper_bound_eq".toName
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
  logInfo "AXIOM_CONTRACT_OK: RicciFlow.riccati_upper_bound_eq"
run_cmd do
  let name := "RicciFlow.riccati_doubling_time_eq".toName
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
  logInfo "AXIOM_CONTRACT_OK: RicciFlow.riccati_doubling_time_eq"
run_cmd do
  let name := "RicciFlow.secondDeriv_nonneg_of_isLocalMin_eq".toName
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
  logInfo "AXIOM_CONTRACT_OK: RicciFlow.secondDeriv_nonneg_of_isLocalMin_eq"
run_cmd do
  let name := "RicciFlow.hessian_nonneg_of_isLocalMin_eq".toName
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
  logInfo "AXIOM_CONTRACT_OK: RicciFlow.hessian_nonneg_of_isLocalMin_eq"
run_cmd do
  let name := "RicciFlow.fderiv_fderiv_nonneg_of_isLocalMin_contDiffAt_eq".toName
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
  logInfo "AXIOM_CONTRACT_OK: RicciFlow.fderiv_fderiv_nonneg_of_isLocalMin_contDiffAt_eq"
run_cmd do
  let name := "RicciFlow.exists_first_zero_eq".toName
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
  logInfo "AXIOM_CONTRACT_OK: RicciFlow.exists_first_zero_eq"
universe u_1
run_cmd liftTermElabM do
  let info ← getConstInfo "RicciFlow.ode_comparison_nonpos".toName
  let levels : List Level := []
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "∀ {u u' : Real → Real} {C T : Real}, (∀ (t : Real), Membership.mem.{0, 0} (Set.Icc.{0} (0 : Real) T) t → HasDerivAt.{0, 0} u (u' t) t) → (∀ (t : Real), Membership.mem.{0, 0} (Set.Icc.{0} (0 : Real) T) t → LE.le.{0} (u' t) (HMul.hMul.{0, 0, 0} C (u t))) → LE.le.{0} (u (0 : Real)) (0 : Real) → ∀ {t : Real}, Membership.mem.{0, 0} (Set.Icc.{0} (0 : Real) T) t → LE.le.{0} (u t) (0 : Real)" with
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
  logInfo "FROZEN_CONTRACT_OK: RicciFlow.ode_comparison_nonpos"
run_cmd liftTermElabM do
  let info ← getConstInfo "RicciFlow.ode_comparison_nonneg".toName
  let levels : List Level := []
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "∀ {u u' : Real → Real} {C T : Real}, (∀ (t : Real), Membership.mem.{0, 0} (Set.Icc.{0} (0 : Real) T) t → HasDerivAt.{0, 0} u (u' t) t) → (∀ (t : Real), Membership.mem.{0, 0} (Set.Icc.{0} (0 : Real) T) t → LE.le.{0} (HMul.hMul.{0, 0, 0} C (u t)) (u' t)) → LE.le.{0} (0 : Real) (u (0 : Real)) → ∀ {t : Real}, Membership.mem.{0, 0} (Set.Icc.{0} (0 : Real) T) t → LE.le.{0} (0 : Real) (u t)" with
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
  logInfo "FROZEN_CONTRACT_OK: RicciFlow.ode_comparison_nonneg"
run_cmd liftTermElabM do
  let info ← getConstInfo "RicciFlow.riccati_lower_bound".toName
  let levels : List Level := []
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "∀ {u u' : Real → Real} {a T : Real}, LE.le.{0} (0 : Real) a → (∀ (t : Real), Membership.mem.{0, 0} (Set.Icc.{0} (0 : Real) T) t → HasDerivAt.{0, 0} u (u' t) t) → (∀ (t : Real), Membership.mem.{0, 0} (Set.Icc.{0} (0 : Real) T) t → LE.le.{0} (HMul.hMul.{0, 0, 0} a (HPow.hPow.{0, 0, 0} (u t) (2 : Nat))) (u' t)) → LT.lt.{0} (0 : Real) (u (0 : Real)) → ∀ {t : Real}, Membership.mem.{0, 0} (Set.Icc.{0} (0 : Real) T) t → LE.le.{0} (HDiv.hDiv.{0, 0, 0} (u (0 : Real)) (HSub.hSub.{0, 0, 0} (1 : Real) (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} a (u (0 : Real))) t))) (u t)" with
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
  logInfo "FROZEN_CONTRACT_OK: RicciFlow.riccati_lower_bound"
run_cmd liftTermElabM do
  let info ← getConstInfo "RicciFlow.riccati_forces_finite_time".toName
  let levels : List Level := []
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "∀ {u u' : Real → Real} {a T : Real}, LT.lt.{0} (0 : Real) a → LE.le.{0} (0 : Real) T → (∀ (t : Real), Membership.mem.{0, 0} (Set.Icc.{0} (0 : Real) T) t → HasDerivAt.{0, 0} u (u' t) t) → (∀ (t : Real), Membership.mem.{0, 0} (Set.Icc.{0} (0 : Real) T) t → LE.le.{0} (HMul.hMul.{0, 0, 0} a (HPow.hPow.{0, 0, 0} (u t) (2 : Nat))) (u' t)) → LT.lt.{0} (0 : Real) (u (0 : Real)) → LT.lt.{0} T (HDiv.hDiv.{0, 0, 0} (1 : Real) (HMul.hMul.{0, 0, 0} a (u (0 : Real))))" with
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
  logInfo "FROZEN_CONTRACT_OK: RicciFlow.riccati_forces_finite_time"
run_cmd liftTermElabM do
  let info ← getConstInfo "RicciFlow.einstein_scalar_hasDerivAt_riccati".toName
  let levels : List Level := []
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "∀ {lam n t : Real}, Ne.{1} n (0 : Real) → Ne.{1} (HSub.hSub.{0, 0, 0} (1 : Real) (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (2 : Real) lam) t)) (0 : Real) → HasDerivAt.{0, 0} (fun (s : Real) => HDiv.hDiv.{0, 0, 0} (HMul.hMul.{0, 0, 0} lam n) (HSub.hSub.{0, 0, 0} (1 : Real) (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (2 : Real) lam) s))) (HMul.hMul.{0, 0, 0} (HDiv.hDiv.{0, 0, 0} (2 : Real) n) (HPow.hPow.{0, 0, 0} (HDiv.hDiv.{0, 0, 0} (HMul.hMul.{0, 0, 0} lam n) (HSub.hSub.{0, 0, 0} (1 : Real) (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (2 : Real) lam) t))) (2 : Nat))) t" with
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
  logInfo "FROZEN_CONTRACT_OK: RicciFlow.einstein_scalar_hasDerivAt_riccati"
run_cmd liftTermElabM do
  let info ← getConstInfo "RicciFlow.riccati_upper_bound".toName
  let levels : List Level := []
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "∀ {u u' : Real → Real} {a T : Real}, LE.le.{0} (0 : Real) a → (∀ (t : Real), Membership.mem.{0, 0} (Set.Icc.{0} (0 : Real) T) t → HasDerivAt.{0, 0} u (u' t) t) → (∀ (t : Real), Membership.mem.{0, 0} (Set.Icc.{0} (0 : Real) T) t → LE.le.{0} (u' t) (HMul.hMul.{0, 0, 0} a (HPow.hPow.{0, 0, 0} (u t) (2 : Nat)))) → (∀ (t : Real), Membership.mem.{0, 0} (Set.Icc.{0} (0 : Real) T) t → LT.lt.{0} (0 : Real) (u t)) → ∀ {t : Real}, Membership.mem.{0, 0} (Set.Icc.{0} (0 : Real) T) t → LT.lt.{0} (0 : Real) (HSub.hSub.{0, 0, 0} (1 : Real) (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} a (u (0 : Real))) t)) → LE.le.{0} (u t) (HDiv.hDiv.{0, 0, 0} (u (0 : Real)) (HSub.hSub.{0, 0, 0} (1 : Real) (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} a (u (0 : Real))) t)))" with
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
  logInfo "FROZEN_CONTRACT_OK: RicciFlow.riccati_upper_bound"
run_cmd liftTermElabM do
  let info ← getConstInfo "RicciFlow.riccati_doubling_time".toName
  let levels : List Level := []
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "∀ {u u' : Real → Real} {a T : Real}, LT.lt.{0} (0 : Real) a → (∀ (t : Real), Membership.mem.{0, 0} (Set.Icc.{0} (0 : Real) T) t → HasDerivAt.{0, 0} u (u' t) t) → (∀ (t : Real), Membership.mem.{0, 0} (Set.Icc.{0} (0 : Real) T) t → LE.le.{0} (u' t) (HMul.hMul.{0, 0, 0} a (HPow.hPow.{0, 0, 0} (u t) (2 : Nat)))) → (∀ (t : Real), Membership.mem.{0, 0} (Set.Icc.{0} (0 : Real) T) t → LT.lt.{0} (0 : Real) (u t)) → ∀ {t : Real}, Membership.mem.{0, 0} (Set.Icc.{0} (0 : Real) T) t → LE.le.{0} t (HDiv.hDiv.{0, 0, 0} (1 : Real) (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (2 : Real) a) (u (0 : Real)))) → LE.le.{0} (u t) (HMul.hMul.{0, 0, 0} (2 : Real) (u (0 : Real)))" with
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
  logInfo "FROZEN_CONTRACT_OK: RicciFlow.riccati_doubling_time"
run_cmd liftTermElabM do
  let info ← getConstInfo "RicciFlow.secondDeriv_nonneg_of_isLocalMin".toName
  let levels : List Level := []
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "∀ {g g' g'' : Real → Real}, (∀ (t : Real), HasDerivAt.{0, 0} g (g' t) t) → (∀ (t : Real), HasDerivAt.{0, 0} g' (g'' t) t) → Continuous.{0, 0} g'' → IsLocalMin.{0, 0} g (0 : Real) → LE.le.{0} (0 : Real) (g'' (0 : Real))" with
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
  logInfo "FROZEN_CONTRACT_OK: RicciFlow.secondDeriv_nonneg_of_isLocalMin"
run_cmd liftTermElabM do
  let info ← getConstInfo "RicciFlow.hessian_nonneg_of_isLocalMin".toName
  let levels : List Level := [Level.param "u_1".toName]
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "∀ {E : Type u_1} [inst : NormedAddCommGroup.{u_1} E] [inst_1 : NormedSpace.{0, u_1} Real E] {f : E → Real}, ContDiff.{0, u_1, 0} Real (2 : WithTop.{0} ENat) f → ∀ {x₀ : E}, IsLocalMin.{u_1, 0} f x₀ → ∀ (v : E), LE.le.{0} (0 : Real) (((fderiv.{0, u_1, u_1} Real (fderiv.{0, u_1, 0} Real f) x₀) v) v)" with
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
  logInfo "FROZEN_CONTRACT_OK: RicciFlow.hessian_nonneg_of_isLocalMin"
run_cmd liftTermElabM do
  let info ← getConstInfo "RicciFlow.fderiv_fderiv_nonneg_of_isLocalMin_contDiffAt".toName
  let levels : List Level := [Level.param "u_1".toName]
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "∀ {E : Type u_1} [inst : NormedAddCommGroup.{u_1} E] [inst_1 : NormedSpace.{0, u_1} Real E] {f : E → Real} {x₀ : E}, ContDiffAt.{0, u_1, 0} Real (2 : WithTop.{0} ENat) f x₀ → IsLocalMin.{u_1, 0} f x₀ → ∀ (v : E), LE.le.{0} (0 : Real) (((fderiv.{0, u_1, u_1} Real (fderiv.{0, u_1, 0} Real f) x₀) v) v)" with
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
  logInfo "FROZEN_CONTRACT_OK: RicciFlow.fderiv_fderiv_nonneg_of_isLocalMin_contDiffAt"
run_cmd liftTermElabM do
  let info ← getConstInfo "RicciFlow.exists_first_zero".toName
  let levels : List Level := []
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "∀ {g : Real → Real} {T : Real}, ContinuousOn.{0, 0} g (Set.Icc.{0} (0 : Real) T) → LT.lt.{0} (0 : Real) (g (0 : Real)) → (∃ (t : Real), And (Membership.mem.{0, 0} (Set.Icc.{0} (0 : Real) T) t) (LE.le.{0} (g t) (0 : Real))) → ∃ (t₀ : Real), And (Membership.mem.{0, 0} (Set.Ioc.{0} (0 : Real) T) t₀) (And (Eq.{1} (g t₀) (0 : Real)) (∀ (s : Real), Membership.mem.{0, 0} (Set.Ico.{0} (0 : Real) t₀) s → LT.lt.{0} (0 : Real) (g s)))" with
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
  logInfo "FROZEN_CONTRACT_OK: RicciFlow.exists_first_zero"
run_cmd liftTermElabM do
  let info ← getConstInfo "RicciFlow.ode_comparison_nonpos_eq".toName
  let levels : List Level := []
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "Eq.{0} @RicciFlow.ode_comparison_nonpos @RicciFlow.ode_comparison_nonpos" with
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
  logInfo "FROZEN_CONTRACT_OK: RicciFlow.ode_comparison_nonpos_eq"
run_cmd liftTermElabM do
  let info ← getConstInfo "RicciFlow.ode_comparison_nonneg_eq".toName
  let levels : List Level := []
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "Eq.{0} @RicciFlow.ode_comparison_nonneg @RicciFlow.ode_comparison_nonneg" with
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
  logInfo "FROZEN_CONTRACT_OK: RicciFlow.ode_comparison_nonneg_eq"
run_cmd liftTermElabM do
  let info ← getConstInfo "RicciFlow.riccati_lower_bound_eq".toName
  let levels : List Level := []
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "Eq.{0} @RicciFlow.riccati_lower_bound @RicciFlow.riccati_lower_bound" with
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
  logInfo "FROZEN_CONTRACT_OK: RicciFlow.riccati_lower_bound_eq"
run_cmd liftTermElabM do
  let info ← getConstInfo "RicciFlow.riccati_forces_finite_time_eq".toName
  let levels : List Level := []
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "Eq.{0} @RicciFlow.riccati_forces_finite_time @RicciFlow.riccati_forces_finite_time" with
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
  logInfo "FROZEN_CONTRACT_OK: RicciFlow.riccati_forces_finite_time_eq"
run_cmd liftTermElabM do
  let info ← getConstInfo "RicciFlow.einstein_scalar_hasDerivAt_riccati_eq".toName
  let levels : List Level := []
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "Eq.{0} @RicciFlow.einstein_scalar_hasDerivAt_riccati @RicciFlow.einstein_scalar_hasDerivAt_riccati" with
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
  logInfo "FROZEN_CONTRACT_OK: RicciFlow.einstein_scalar_hasDerivAt_riccati_eq"
run_cmd liftTermElabM do
  let info ← getConstInfo "RicciFlow.riccati_upper_bound_eq".toName
  let levels : List Level := []
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "Eq.{0} @RicciFlow.riccati_upper_bound @RicciFlow.riccati_upper_bound" with
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
  logInfo "FROZEN_CONTRACT_OK: RicciFlow.riccati_upper_bound_eq"
run_cmd liftTermElabM do
  let info ← getConstInfo "RicciFlow.riccati_doubling_time_eq".toName
  let levels : List Level := []
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "Eq.{0} @RicciFlow.riccati_doubling_time @RicciFlow.riccati_doubling_time" with
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
  logInfo "FROZEN_CONTRACT_OK: RicciFlow.riccati_doubling_time_eq"
run_cmd liftTermElabM do
  let info ← getConstInfo "RicciFlow.secondDeriv_nonneg_of_isLocalMin_eq".toName
  let levels : List Level := []
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "Eq.{0} @RicciFlow.secondDeriv_nonneg_of_isLocalMin @RicciFlow.secondDeriv_nonneg_of_isLocalMin" with
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
  logInfo "FROZEN_CONTRACT_OK: RicciFlow.secondDeriv_nonneg_of_isLocalMin_eq"
run_cmd liftTermElabM do
  let info ← getConstInfo "RicciFlow.hessian_nonneg_of_isLocalMin_eq".toName
  let levels : List Level := [Level.param "u_1".toName]
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "Eq.{0} @RicciFlow.hessian_nonneg_of_isLocalMin.{u_1} @RicciFlow.hessian_nonneg_of_isLocalMin.{u_1}" with
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
  logInfo "FROZEN_CONTRACT_OK: RicciFlow.hessian_nonneg_of_isLocalMin_eq"
run_cmd liftTermElabM do
  let info ← getConstInfo "RicciFlow.fderiv_fderiv_nonneg_of_isLocalMin_contDiffAt_eq".toName
  let levels : List Level := [Level.param "u_1".toName]
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "Eq.{0} @RicciFlow.fderiv_fderiv_nonneg_of_isLocalMin_contDiffAt.{u_1} @RicciFlow.fderiv_fderiv_nonneg_of_isLocalMin_contDiffAt.{u_1}" with
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
  logInfo "FROZEN_CONTRACT_OK: RicciFlow.fderiv_fderiv_nonneg_of_isLocalMin_contDiffAt_eq"
run_cmd liftTermElabM do
  let info ← getConstInfo "RicciFlow.exists_first_zero_eq".toName
  let levels : List Level := []
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "Eq.{0} @RicciFlow.exists_first_zero @RicciFlow.exists_first_zero" with
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
  logInfo "FROZEN_CONTRACT_OK: RicciFlow.exists_first_zero_eq"
