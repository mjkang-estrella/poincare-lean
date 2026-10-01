import Lean
import Poincare.Global.ParabolicHolderMultiplier
open Lean Elab Command Meta
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
run_cmd do
  let name := "Poincare.ParabolicHolderMultiplier.ddu_time_bound".toName
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
      if info.isAxiom then
        unless ["propext".toName, "Classical.choice".toName, "Quot.sound".toName].contains current do
          throwError "forbidden visited axiom {current} in {name}"
      pending := info.getUsedConstantsAsSet.toList ++ pending
      match info with
      | .recInfo value =>
        pending := value.all ++ pending
        for rule in value.rules do
          pending := rule.ctor :: rule.rhs.getUsedConstants.toList ++ pending
      | .inductInfo value => pending := value.all ++ value.ctors ++ pending
      | .ctorInfo value => pending := value.induct :: pending
      | _ => pure ()
  let allowed : List Name := ["propext".toName, "Classical.choice".toName, "Quot.sound".toName]
  let footprint ← collectAxioms name
  for dependency in footprint do
    unless allowed.contains dependency do
      throwError "forbidden axiom {dependency} in {name}"
  logInfo "AXIOM_CONTRACT_OK: Poincare.ParabolicHolderMultiplier.ddu_time_bound"
run_cmd do
  let name := "Poincare.ParabolicHolderMultiplier.ddu_zero_trace".toName
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
      if info.isAxiom then
        unless ["propext".toName, "Classical.choice".toName, "Quot.sound".toName].contains current do
          throwError "forbidden visited axiom {current} in {name}"
      pending := info.getUsedConstantsAsSet.toList ++ pending
      match info with
      | .recInfo value =>
        pending := value.all ++ pending
        for rule in value.rules do
          pending := rule.ctor :: rule.rhs.getUsedConstants.toList ++ pending
      | .inductInfo value => pending := value.all ++ value.ctors ++ pending
      | .ctorInfo value => pending := value.induct :: pending
      | _ => pure ()
  let allowed : List Name := ["propext".toName, "Classical.choice".toName, "Quot.sound".toName]
  let footprint ← collectAxioms name
  for dependency in footprint do
    unless allowed.contains dependency do
      throwError "forbidden axiom {dependency} in {name}"
  logInfo "AXIOM_CONTRACT_OK: Poincare.ParabolicHolderMultiplier.ddu_zero_trace"
run_cmd do
  let name := "Poincare.ParabolicHolderMultiplier.du_zero_trace".toName
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
      if info.isAxiom then
        unless ["propext".toName, "Classical.choice".toName, "Quot.sound".toName].contains current do
          throwError "forbidden visited axiom {current} in {name}"
      pending := info.getUsedConstantsAsSet.toList ++ pending
      match info with
      | .recInfo value =>
        pending := value.all ++ pending
        for rule in value.rules do
          pending := rule.ctor :: rule.rhs.getUsedConstants.toList ++ pending
      | .inductInfo value => pending := value.all ++ value.ctors ++ pending
      | .ctorInfo value => pending := value.induct :: pending
      | _ => pure ()
  let allowed : List Name := ["propext".toName, "Classical.choice".toName, "Quot.sound".toName]
  let footprint ← collectAxioms name
  for dependency in footprint do
    unless allowed.contains dependency do
      throwError "forbidden axiom {dependency} in {name}"
  logInfo "AXIOM_CONTRACT_OK: Poincare.ParabolicHolderMultiplier.du_zero_trace"
run_cmd do
  let name := "Poincare.ParabolicHolderMultiplier.entry".toName
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
      if info.isAxiom then
        unless ["propext".toName, "Classical.choice".toName, "Quot.sound".toName].contains current do
          throwError "forbidden visited axiom {current} in {name}"
      pending := info.getUsedConstantsAsSet.toList ++ pending
      match info with
      | .recInfo value =>
        pending := value.all ++ pending
        for rule in value.rules do
          pending := rule.ctor :: rule.rhs.getUsedConstants.toList ++ pending
      | .inductInfo value => pending := value.all ++ value.ctors ++ pending
      | .ctorInfo value => pending := value.induct :: pending
      | _ => pure ()
  let allowed : List Name := ["propext".toName, "Classical.choice".toName, "Quot.sound".toName]
  let footprint ← collectAxioms name
  for dependency in footprint do
    unless allowed.contains dependency do
      throwError "forbidden axiom {dependency} in {name}"
  logInfo "AXIOM_CONTRACT_OK: Poincare.ParabolicHolderMultiplier.entry"
run_cmd do
  let name := "Poincare.ParabolicHolderMultiplier.entry._proof_1".toName
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
      if info.isAxiom then
        unless ["propext".toName, "Classical.choice".toName, "Quot.sound".toName].contains current do
          throwError "forbidden visited axiom {current} in {name}"
      pending := info.getUsedConstantsAsSet.toList ++ pending
      match info with
      | .recInfo value =>
        pending := value.all ++ pending
        for rule in value.rules do
          pending := rule.ctor :: rule.rhs.getUsedConstants.toList ++ pending
      | .inductInfo value => pending := value.all ++ value.ctors ++ pending
      | .ctorInfo value => pending := value.induct :: pending
      | _ => pure ()
  let allowed : List Name := ["propext".toName, "Classical.choice".toName, "Quot.sound".toName]
  let footprint ← collectAxioms name
  for dependency in footprint do
    unless allowed.contains dependency do
      throwError "forbidden axiom {dependency} in {name}"
  logInfo "AXIOM_CONTRACT_OK: Poincare.ParabolicHolderMultiplier.entry._proof_1"
run_cmd do
  let name := "Poincare.ParabolicHolderMultiplier.entry._proof_10".toName
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
      if info.isAxiom then
        unless ["propext".toName, "Classical.choice".toName, "Quot.sound".toName].contains current do
          throwError "forbidden visited axiom {current} in {name}"
      pending := info.getUsedConstantsAsSet.toList ++ pending
      match info with
      | .recInfo value =>
        pending := value.all ++ pending
        for rule in value.rules do
          pending := rule.ctor :: rule.rhs.getUsedConstants.toList ++ pending
      | .inductInfo value => pending := value.all ++ value.ctors ++ pending
      | .ctorInfo value => pending := value.induct :: pending
      | _ => pure ()
  let allowed : List Name := ["propext".toName, "Classical.choice".toName, "Quot.sound".toName]
  let footprint ← collectAxioms name
  for dependency in footprint do
    unless allowed.contains dependency do
      throwError "forbidden axiom {dependency} in {name}"
  logInfo "AXIOM_CONTRACT_OK: Poincare.ParabolicHolderMultiplier.entry._proof_10"
run_cmd do
  let name := "Poincare.ParabolicHolderMultiplier.entry._proof_11".toName
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
      if info.isAxiom then
        unless ["propext".toName, "Classical.choice".toName, "Quot.sound".toName].contains current do
          throwError "forbidden visited axiom {current} in {name}"
      pending := info.getUsedConstantsAsSet.toList ++ pending
      match info with
      | .recInfo value =>
        pending := value.all ++ pending
        for rule in value.rules do
          pending := rule.ctor :: rule.rhs.getUsedConstants.toList ++ pending
      | .inductInfo value => pending := value.all ++ value.ctors ++ pending
      | .ctorInfo value => pending := value.induct :: pending
      | _ => pure ()
  let allowed : List Name := ["propext".toName, "Classical.choice".toName, "Quot.sound".toName]
  let footprint ← collectAxioms name
  for dependency in footprint do
    unless allowed.contains dependency do
      throwError "forbidden axiom {dependency} in {name}"
  logInfo "AXIOM_CONTRACT_OK: Poincare.ParabolicHolderMultiplier.entry._proof_11"
run_cmd do
  let name := "Poincare.ParabolicHolderMultiplier.entry._proof_12".toName
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
      if info.isAxiom then
        unless ["propext".toName, "Classical.choice".toName, "Quot.sound".toName].contains current do
          throwError "forbidden visited axiom {current} in {name}"
      pending := info.getUsedConstantsAsSet.toList ++ pending
      match info with
      | .recInfo value =>
        pending := value.all ++ pending
        for rule in value.rules do
          pending := rule.ctor :: rule.rhs.getUsedConstants.toList ++ pending
      | .inductInfo value => pending := value.all ++ value.ctors ++ pending
      | .ctorInfo value => pending := value.induct :: pending
      | _ => pure ()
  let allowed : List Name := ["propext".toName, "Classical.choice".toName, "Quot.sound".toName]
  let footprint ← collectAxioms name
  for dependency in footprint do
    unless allowed.contains dependency do
      throwError "forbidden axiom {dependency} in {name}"
  logInfo "AXIOM_CONTRACT_OK: Poincare.ParabolicHolderMultiplier.entry._proof_12"
run_cmd do
  let name := "Poincare.ParabolicHolderMultiplier.entry._proof_13".toName
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
      if info.isAxiom then
        unless ["propext".toName, "Classical.choice".toName, "Quot.sound".toName].contains current do
          throwError "forbidden visited axiom {current} in {name}"
      pending := info.getUsedConstantsAsSet.toList ++ pending
      match info with
      | .recInfo value =>
        pending := value.all ++ pending
        for rule in value.rules do
          pending := rule.ctor :: rule.rhs.getUsedConstants.toList ++ pending
      | .inductInfo value => pending := value.all ++ value.ctors ++ pending
      | .ctorInfo value => pending := value.induct :: pending
      | _ => pure ()
  let allowed : List Name := ["propext".toName, "Classical.choice".toName, "Quot.sound".toName]
  let footprint ← collectAxioms name
  for dependency in footprint do
    unless allowed.contains dependency do
      throwError "forbidden axiom {dependency} in {name}"
  logInfo "AXIOM_CONTRACT_OK: Poincare.ParabolicHolderMultiplier.entry._proof_13"
run_cmd do
  let name := "Poincare.ParabolicHolderMultiplier.entry._proof_2".toName
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
      if info.isAxiom then
        unless ["propext".toName, "Classical.choice".toName, "Quot.sound".toName].contains current do
          throwError "forbidden visited axiom {current} in {name}"
      pending := info.getUsedConstantsAsSet.toList ++ pending
      match info with
      | .recInfo value =>
        pending := value.all ++ pending
        for rule in value.rules do
          pending := rule.ctor :: rule.rhs.getUsedConstants.toList ++ pending
      | .inductInfo value => pending := value.all ++ value.ctors ++ pending
      | .ctorInfo value => pending := value.induct :: pending
      | _ => pure ()
  let allowed : List Name := ["propext".toName, "Classical.choice".toName, "Quot.sound".toName]
  let footprint ← collectAxioms name
  for dependency in footprint do
    unless allowed.contains dependency do
      throwError "forbidden axiom {dependency} in {name}"
  logInfo "AXIOM_CONTRACT_OK: Poincare.ParabolicHolderMultiplier.entry._proof_2"
run_cmd do
  let name := "Poincare.ParabolicHolderMultiplier.entry._proof_3".toName
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
      if info.isAxiom then
        unless ["propext".toName, "Classical.choice".toName, "Quot.sound".toName].contains current do
          throwError "forbidden visited axiom {current} in {name}"
      pending := info.getUsedConstantsAsSet.toList ++ pending
      match info with
      | .recInfo value =>
        pending := value.all ++ pending
        for rule in value.rules do
          pending := rule.ctor :: rule.rhs.getUsedConstants.toList ++ pending
      | .inductInfo value => pending := value.all ++ value.ctors ++ pending
      | .ctorInfo value => pending := value.induct :: pending
      | _ => pure ()
  let allowed : List Name := ["propext".toName, "Classical.choice".toName, "Quot.sound".toName]
  let footprint ← collectAxioms name
  for dependency in footprint do
    unless allowed.contains dependency do
      throwError "forbidden axiom {dependency} in {name}"
  logInfo "AXIOM_CONTRACT_OK: Poincare.ParabolicHolderMultiplier.entry._proof_3"
run_cmd do
  let name := "Poincare.ParabolicHolderMultiplier.entry._proof_4".toName
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
      if info.isAxiom then
        unless ["propext".toName, "Classical.choice".toName, "Quot.sound".toName].contains current do
          throwError "forbidden visited axiom {current} in {name}"
      pending := info.getUsedConstantsAsSet.toList ++ pending
      match info with
      | .recInfo value =>
        pending := value.all ++ pending
        for rule in value.rules do
          pending := rule.ctor :: rule.rhs.getUsedConstants.toList ++ pending
      | .inductInfo value => pending := value.all ++ value.ctors ++ pending
      | .ctorInfo value => pending := value.induct :: pending
      | _ => pure ()
  let allowed : List Name := ["propext".toName, "Classical.choice".toName, "Quot.sound".toName]
  let footprint ← collectAxioms name
  for dependency in footprint do
    unless allowed.contains dependency do
      throwError "forbidden axiom {dependency} in {name}"
  logInfo "AXIOM_CONTRACT_OK: Poincare.ParabolicHolderMultiplier.entry._proof_4"
run_cmd do
  let name := "Poincare.ParabolicHolderMultiplier.entry._proof_5".toName
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
      if info.isAxiom then
        unless ["propext".toName, "Classical.choice".toName, "Quot.sound".toName].contains current do
          throwError "forbidden visited axiom {current} in {name}"
      pending := info.getUsedConstantsAsSet.toList ++ pending
      match info with
      | .recInfo value =>
        pending := value.all ++ pending
        for rule in value.rules do
          pending := rule.ctor :: rule.rhs.getUsedConstants.toList ++ pending
      | .inductInfo value => pending := value.all ++ value.ctors ++ pending
      | .ctorInfo value => pending := value.induct :: pending
      | _ => pure ()
  let allowed : List Name := ["propext".toName, "Classical.choice".toName, "Quot.sound".toName]
  let footprint ← collectAxioms name
  for dependency in footprint do
    unless allowed.contains dependency do
      throwError "forbidden axiom {dependency} in {name}"
  logInfo "AXIOM_CONTRACT_OK: Poincare.ParabolicHolderMultiplier.entry._proof_5"
run_cmd do
  let name := "Poincare.ParabolicHolderMultiplier.entry._proof_6".toName
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
      if info.isAxiom then
        unless ["propext".toName, "Classical.choice".toName, "Quot.sound".toName].contains current do
          throwError "forbidden visited axiom {current} in {name}"
      pending := info.getUsedConstantsAsSet.toList ++ pending
      match info with
      | .recInfo value =>
        pending := value.all ++ pending
        for rule in value.rules do
          pending := rule.ctor :: rule.rhs.getUsedConstants.toList ++ pending
      | .inductInfo value => pending := value.all ++ value.ctors ++ pending
      | .ctorInfo value => pending := value.induct :: pending
      | _ => pure ()
  let allowed : List Name := ["propext".toName, "Classical.choice".toName, "Quot.sound".toName]
  let footprint ← collectAxioms name
  for dependency in footprint do
    unless allowed.contains dependency do
      throwError "forbidden axiom {dependency} in {name}"
  logInfo "AXIOM_CONTRACT_OK: Poincare.ParabolicHolderMultiplier.entry._proof_6"
run_cmd do
  let name := "Poincare.ParabolicHolderMultiplier.entry._proof_7".toName
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
      if info.isAxiom then
        unless ["propext".toName, "Classical.choice".toName, "Quot.sound".toName].contains current do
          throwError "forbidden visited axiom {current} in {name}"
      pending := info.getUsedConstantsAsSet.toList ++ pending
      match info with
      | .recInfo value =>
        pending := value.all ++ pending
        for rule in value.rules do
          pending := rule.ctor :: rule.rhs.getUsedConstants.toList ++ pending
      | .inductInfo value => pending := value.all ++ value.ctors ++ pending
      | .ctorInfo value => pending := value.induct :: pending
      | _ => pure ()
  let allowed : List Name := ["propext".toName, "Classical.choice".toName, "Quot.sound".toName]
  let footprint ← collectAxioms name
  for dependency in footprint do
    unless allowed.contains dependency do
      throwError "forbidden axiom {dependency} in {name}"
  logInfo "AXIOM_CONTRACT_OK: Poincare.ParabolicHolderMultiplier.entry._proof_7"
run_cmd do
  let name := "Poincare.ParabolicHolderMultiplier.entry._proof_8".toName
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
      if info.isAxiom then
        unless ["propext".toName, "Classical.choice".toName, "Quot.sound".toName].contains current do
          throwError "forbidden visited axiom {current} in {name}"
      pending := info.getUsedConstantsAsSet.toList ++ pending
      match info with
      | .recInfo value =>
        pending := value.all ++ pending
        for rule in value.rules do
          pending := rule.ctor :: rule.rhs.getUsedConstants.toList ++ pending
      | .inductInfo value => pending := value.all ++ value.ctors ++ pending
      | .ctorInfo value => pending := value.induct :: pending
      | _ => pure ()
  let allowed : List Name := ["propext".toName, "Classical.choice".toName, "Quot.sound".toName]
  let footprint ← collectAxioms name
  for dependency in footprint do
    unless allowed.contains dependency do
      throwError "forbidden axiom {dependency} in {name}"
  logInfo "AXIOM_CONTRACT_OK: Poincare.ParabolicHolderMultiplier.entry._proof_8"
run_cmd do
  let name := "Poincare.ParabolicHolderMultiplier.entry._proof_9".toName
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
      if info.isAxiom then
        unless ["propext".toName, "Classical.choice".toName, "Quot.sound".toName].contains current do
          throwError "forbidden visited axiom {current} in {name}"
      pending := info.getUsedConstantsAsSet.toList ++ pending
      match info with
      | .recInfo value =>
        pending := value.all ++ pending
        for rule in value.rules do
          pending := rule.ctor :: rule.rhs.getUsedConstants.toList ++ pending
      | .inductInfo value => pending := value.all ++ value.ctors ++ pending
      | .ctorInfo value => pending := value.induct :: pending
      | _ => pure ()
  let allowed : List Name := ["propext".toName, "Classical.choice".toName, "Quot.sound".toName]
  let footprint ← collectAxioms name
  for dependency in footprint do
    unless allowed.contains dependency do
      throwError "forbidden axiom {dependency} in {name}"
  logInfo "AXIOM_CONTRACT_OK: Poincare.ParabolicHolderMultiplier.entry._proof_9"
run_cmd do
  let name := "Poincare.ParabolicHolderMultiplier.entry.congr_simp".toName
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
      if info.isAxiom then
        unless ["propext".toName, "Classical.choice".toName, "Quot.sound".toName].contains current do
          throwError "forbidden visited axiom {current} in {name}"
      pending := info.getUsedConstantsAsSet.toList ++ pending
      match info with
      | .recInfo value =>
        pending := value.all ++ pending
        for rule in value.rules do
          pending := rule.ctor :: rule.rhs.getUsedConstants.toList ++ pending
      | .inductInfo value => pending := value.all ++ value.ctors ++ pending
      | .ctorInfo value => pending := value.induct :: pending
      | _ => pure ()
  let allowed : List Name := ["propext".toName, "Classical.choice".toName, "Quot.sound".toName]
  let footprint ← collectAxioms name
  for dependency in footprint do
    unless allowed.contains dependency do
      throwError "forbidden axiom {dependency} in {name}"
  logInfo "AXIOM_CONTRACT_OK: Poincare.ParabolicHolderMultiplier.entry.congr_simp"
run_cmd do
  let name := "Poincare.ParabolicHolderMultiplier.entry_apply".toName
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
      if info.isAxiom then
        unless ["propext".toName, "Classical.choice".toName, "Quot.sound".toName].contains current do
          throwError "forbidden visited axiom {current} in {name}"
      pending := info.getUsedConstantsAsSet.toList ++ pending
      match info with
      | .recInfo value =>
        pending := value.all ++ pending
        for rule in value.rules do
          pending := rule.ctor :: rule.rhs.getUsedConstants.toList ++ pending
      | .inductInfo value => pending := value.all ++ value.ctors ++ pending
      | .ctorInfo value => pending := value.induct :: pending
      | _ => pure ()
  let allowed : List Name := ["propext".toName, "Classical.choice".toName, "Quot.sound".toName]
  let footprint ← collectAxioms name
  for dependency in footprint do
    unless allowed.contains dependency do
      throwError "forbidden axiom {dependency} in {name}"
  logInfo "AXIOM_CONTRACT_OK: Poincare.ParabolicHolderMultiplier.entry_apply"
run_cmd do
  let name := "Poincare.ParabolicHolderMultiplier.entry_holderBound".toName
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
      if info.isAxiom then
        unless ["propext".toName, "Classical.choice".toName, "Quot.sound".toName].contains current do
          throwError "forbidden visited axiom {current} in {name}"
      pending := info.getUsedConstantsAsSet.toList ++ pending
      match info with
      | .recInfo value =>
        pending := value.all ++ pending
        for rule in value.rules do
          pending := rule.ctor :: rule.rhs.getUsedConstants.toList ++ pending
      | .inductInfo value => pending := value.all ++ value.ctors ++ pending
      | .ctorInfo value => pending := value.induct :: pending
      | _ => pure ()
  let allowed : List Name := ["propext".toName, "Classical.choice".toName, "Quot.sound".toName]
  let footprint ← collectAxioms name
  for dependency in footprint do
    unless allowed.contains dependency do
      throwError "forbidden axiom {dependency} in {name}"
  logInfo "AXIOM_CONTRACT_OK: Poincare.ParabolicHolderMultiplier.entry_holderBound"
run_cmd do
  let name := "Poincare.ParabolicHolderMultiplier.error_small".toName
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
      if info.isAxiom then
        unless ["propext".toName, "Classical.choice".toName, "Quot.sound".toName].contains current do
          throwError "forbidden visited axiom {current} in {name}"
      pending := info.getUsedConstantsAsSet.toList ++ pending
      match info with
      | .recInfo value =>
        pending := value.all ++ pending
        for rule in value.rules do
          pending := rule.ctor :: rule.rhs.getUsedConstants.toList ++ pending
      | .inductInfo value => pending := value.all ++ value.ctors ++ pending
      | .ctorInfo value => pending := value.induct :: pending
      | _ => pure ()
  let allowed : List Name := ["propext".toName, "Classical.choice".toName, "Quot.sound".toName]
  let footprint ← collectAxioms name
  for dependency in footprint do
    unless allowed.contains dependency do
      throwError "forbidden axiom {dependency} in {name}"
  logInfo "AXIOM_CONTRACT_OK: Poincare.ParabolicHolderMultiplier.error_small"
run_cmd do
  let name := "Poincare.ParabolicHolderMultiplier.eval_norm_le".toName
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
      if info.isAxiom then
        unless ["propext".toName, "Classical.choice".toName, "Quot.sound".toName].contains current do
          throwError "forbidden visited axiom {current} in {name}"
      pending := info.getUsedConstantsAsSet.toList ++ pending
      match info with
      | .recInfo value =>
        pending := value.all ++ pending
        for rule in value.rules do
          pending := rule.ctor :: rule.rhs.getUsedConstants.toList ++ pending
      | .inductInfo value => pending := value.all ++ value.ctors ++ pending
      | .ctorInfo value => pending := value.induct :: pending
      | _ => pure ()
  let allowed : List Name := ["propext".toName, "Classical.choice".toName, "Quot.sound".toName]
  let footprint ← collectAxioms name
  for dependency in footprint do
    unless allowed.contains dependency do
      throwError "forbidden axiom {dependency} in {name}"
  logInfo "AXIOM_CONTRACT_OK: Poincare.ParabolicHolderMultiplier.eval_norm_le"
run_cmd do
  let name := "Poincare.ParabolicHolderMultiplier.forcing".toName
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
      if info.isAxiom then
        unless ["propext".toName, "Classical.choice".toName, "Quot.sound".toName].contains current do
          throwError "forbidden visited axiom {current} in {name}"
      pending := info.getUsedConstantsAsSet.toList ++ pending
      match info with
      | .recInfo value =>
        pending := value.all ++ pending
        for rule in value.rules do
          pending := rule.ctor :: rule.rhs.getUsedConstants.toList ++ pending
      | .inductInfo value => pending := value.all ++ value.ctors ++ pending
      | .ctorInfo value => pending := value.induct :: pending
      | _ => pure ()
  let allowed : List Name := ["propext".toName, "Classical.choice".toName, "Quot.sound".toName]
  let footprint ← collectAxioms name
  for dependency in footprint do
    unless allowed.contains dependency do
      throwError "forbidden axiom {dependency} in {name}"
  logInfo "AXIOM_CONTRACT_OK: Poincare.ParabolicHolderMultiplier.forcing"
run_cmd do
  let name := "Poincare.ParabolicHolderMultiplier.forcing._proof_1".toName
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
      if info.isAxiom then
        unless ["propext".toName, "Classical.choice".toName, "Quot.sound".toName].contains current do
          throwError "forbidden visited axiom {current} in {name}"
      pending := info.getUsedConstantsAsSet.toList ++ pending
      match info with
      | .recInfo value =>
        pending := value.all ++ pending
        for rule in value.rules do
          pending := rule.ctor :: rule.rhs.getUsedConstants.toList ++ pending
      | .inductInfo value => pending := value.all ++ value.ctors ++ pending
      | .ctorInfo value => pending := value.induct :: pending
      | _ => pure ()
  let allowed : List Name := ["propext".toName, "Classical.choice".toName, "Quot.sound".toName]
  let footprint ← collectAxioms name
  for dependency in footprint do
    unless allowed.contains dependency do
      throwError "forbidden axiom {dependency} in {name}"
  logInfo "AXIOM_CONTRACT_OK: Poincare.ParabolicHolderMultiplier.forcing._proof_1"
run_cmd do
  let name := "Poincare.ParabolicHolderMultiplier.forcing._proof_10".toName
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
      if info.isAxiom then
        unless ["propext".toName, "Classical.choice".toName, "Quot.sound".toName].contains current do
          throwError "forbidden visited axiom {current} in {name}"
      pending := info.getUsedConstantsAsSet.toList ++ pending
      match info with
      | .recInfo value =>
        pending := value.all ++ pending
        for rule in value.rules do
          pending := rule.ctor :: rule.rhs.getUsedConstants.toList ++ pending
      | .inductInfo value => pending := value.all ++ value.ctors ++ pending
      | .ctorInfo value => pending := value.induct :: pending
      | _ => pure ()
  let allowed : List Name := ["propext".toName, "Classical.choice".toName, "Quot.sound".toName]
  let footprint ← collectAxioms name
  for dependency in footprint do
    unless allowed.contains dependency do
      throwError "forbidden axiom {dependency} in {name}"
  logInfo "AXIOM_CONTRACT_OK: Poincare.ParabolicHolderMultiplier.forcing._proof_10"
run_cmd do
  let name := "Poincare.ParabolicHolderMultiplier.forcing._proof_11".toName
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
      if info.isAxiom then
        unless ["propext".toName, "Classical.choice".toName, "Quot.sound".toName].contains current do
          throwError "forbidden visited axiom {current} in {name}"
      pending := info.getUsedConstantsAsSet.toList ++ pending
      match info with
      | .recInfo value =>
        pending := value.all ++ pending
        for rule in value.rules do
          pending := rule.ctor :: rule.rhs.getUsedConstants.toList ++ pending
      | .inductInfo value => pending := value.all ++ value.ctors ++ pending
      | .ctorInfo value => pending := value.induct :: pending
      | _ => pure ()
  let allowed : List Name := ["propext".toName, "Classical.choice".toName, "Quot.sound".toName]
  let footprint ← collectAxioms name
  for dependency in footprint do
    unless allowed.contains dependency do
      throwError "forbidden axiom {dependency} in {name}"
  logInfo "AXIOM_CONTRACT_OK: Poincare.ParabolicHolderMultiplier.forcing._proof_11"
run_cmd do
  let name := "Poincare.ParabolicHolderMultiplier.forcing._proof_12".toName
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
      if info.isAxiom then
        unless ["propext".toName, "Classical.choice".toName, "Quot.sound".toName].contains current do
          throwError "forbidden visited axiom {current} in {name}"
      pending := info.getUsedConstantsAsSet.toList ++ pending
      match info with
      | .recInfo value =>
        pending := value.all ++ pending
        for rule in value.rules do
          pending := rule.ctor :: rule.rhs.getUsedConstants.toList ++ pending
      | .inductInfo value => pending := value.all ++ value.ctors ++ pending
      | .ctorInfo value => pending := value.induct :: pending
      | _ => pure ()
  let allowed : List Name := ["propext".toName, "Classical.choice".toName, "Quot.sound".toName]
  let footprint ← collectAxioms name
  for dependency in footprint do
    unless allowed.contains dependency do
      throwError "forbidden axiom {dependency} in {name}"
  logInfo "AXIOM_CONTRACT_OK: Poincare.ParabolicHolderMultiplier.forcing._proof_12"
run_cmd do
  let name := "Poincare.ParabolicHolderMultiplier.forcing._proof_13".toName
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
      if info.isAxiom then
        unless ["propext".toName, "Classical.choice".toName, "Quot.sound".toName].contains current do
          throwError "forbidden visited axiom {current} in {name}"
      pending := info.getUsedConstantsAsSet.toList ++ pending
      match info with
      | .recInfo value =>
        pending := value.all ++ pending
        for rule in value.rules do
          pending := rule.ctor :: rule.rhs.getUsedConstants.toList ++ pending
      | .inductInfo value => pending := value.all ++ value.ctors ++ pending
      | .ctorInfo value => pending := value.induct :: pending
      | _ => pure ()
  let allowed : List Name := ["propext".toName, "Classical.choice".toName, "Quot.sound".toName]
  let footprint ← collectAxioms name
  for dependency in footprint do
    unless allowed.contains dependency do
      throwError "forbidden axiom {dependency} in {name}"
  logInfo "AXIOM_CONTRACT_OK: Poincare.ParabolicHolderMultiplier.forcing._proof_13"
run_cmd do
  let name := "Poincare.ParabolicHolderMultiplier.forcing._proof_2".toName
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
      if info.isAxiom then
        unless ["propext".toName, "Classical.choice".toName, "Quot.sound".toName].contains current do
          throwError "forbidden visited axiom {current} in {name}"
      pending := info.getUsedConstantsAsSet.toList ++ pending
      match info with
      | .recInfo value =>
        pending := value.all ++ pending
        for rule in value.rules do
          pending := rule.ctor :: rule.rhs.getUsedConstants.toList ++ pending
      | .inductInfo value => pending := value.all ++ value.ctors ++ pending
      | .ctorInfo value => pending := value.induct :: pending
      | _ => pure ()
  let allowed : List Name := ["propext".toName, "Classical.choice".toName, "Quot.sound".toName]
  let footprint ← collectAxioms name
  for dependency in footprint do
    unless allowed.contains dependency do
      throwError "forbidden axiom {dependency} in {name}"
  logInfo "AXIOM_CONTRACT_OK: Poincare.ParabolicHolderMultiplier.forcing._proof_2"
run_cmd do
  let name := "Poincare.ParabolicHolderMultiplier.forcing._proof_3".toName
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
      if info.isAxiom then
        unless ["propext".toName, "Classical.choice".toName, "Quot.sound".toName].contains current do
          throwError "forbidden visited axiom {current} in {name}"
      pending := info.getUsedConstantsAsSet.toList ++ pending
      match info with
      | .recInfo value =>
        pending := value.all ++ pending
        for rule in value.rules do
          pending := rule.ctor :: rule.rhs.getUsedConstants.toList ++ pending
      | .inductInfo value => pending := value.all ++ value.ctors ++ pending
      | .ctorInfo value => pending := value.induct :: pending
      | _ => pure ()
  let allowed : List Name := ["propext".toName, "Classical.choice".toName, "Quot.sound".toName]
  let footprint ← collectAxioms name
  for dependency in footprint do
    unless allowed.contains dependency do
      throwError "forbidden axiom {dependency} in {name}"
  logInfo "AXIOM_CONTRACT_OK: Poincare.ParabolicHolderMultiplier.forcing._proof_3"
run_cmd do
  let name := "Poincare.ParabolicHolderMultiplier.forcing._proof_4".toName
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
      if info.isAxiom then
        unless ["propext".toName, "Classical.choice".toName, "Quot.sound".toName].contains current do
          throwError "forbidden visited axiom {current} in {name}"
      pending := info.getUsedConstantsAsSet.toList ++ pending
      match info with
      | .recInfo value =>
        pending := value.all ++ pending
        for rule in value.rules do
          pending := rule.ctor :: rule.rhs.getUsedConstants.toList ++ pending
      | .inductInfo value => pending := value.all ++ value.ctors ++ pending
      | .ctorInfo value => pending := value.induct :: pending
      | _ => pure ()
  let allowed : List Name := ["propext".toName, "Classical.choice".toName, "Quot.sound".toName]
  let footprint ← collectAxioms name
  for dependency in footprint do
    unless allowed.contains dependency do
      throwError "forbidden axiom {dependency} in {name}"
  logInfo "AXIOM_CONTRACT_OK: Poincare.ParabolicHolderMultiplier.forcing._proof_4"
run_cmd do
  let name := "Poincare.ParabolicHolderMultiplier.forcing._proof_5".toName
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
      if info.isAxiom then
        unless ["propext".toName, "Classical.choice".toName, "Quot.sound".toName].contains current do
          throwError "forbidden visited axiom {current} in {name}"
      pending := info.getUsedConstantsAsSet.toList ++ pending
      match info with
      | .recInfo value =>
        pending := value.all ++ pending
        for rule in value.rules do
          pending := rule.ctor :: rule.rhs.getUsedConstants.toList ++ pending
      | .inductInfo value => pending := value.all ++ value.ctors ++ pending
      | .ctorInfo value => pending := value.induct :: pending
      | _ => pure ()
  let allowed : List Name := ["propext".toName, "Classical.choice".toName, "Quot.sound".toName]
  let footprint ← collectAxioms name
  for dependency in footprint do
    unless allowed.contains dependency do
      throwError "forbidden axiom {dependency} in {name}"
  logInfo "AXIOM_CONTRACT_OK: Poincare.ParabolicHolderMultiplier.forcing._proof_5"
run_cmd do
  let name := "Poincare.ParabolicHolderMultiplier.forcing._proof_6".toName
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
      if info.isAxiom then
        unless ["propext".toName, "Classical.choice".toName, "Quot.sound".toName].contains current do
          throwError "forbidden visited axiom {current} in {name}"
      pending := info.getUsedConstantsAsSet.toList ++ pending
      match info with
      | .recInfo value =>
        pending := value.all ++ pending
        for rule in value.rules do
          pending := rule.ctor :: rule.rhs.getUsedConstants.toList ++ pending
      | .inductInfo value => pending := value.all ++ value.ctors ++ pending
      | .ctorInfo value => pending := value.induct :: pending
      | _ => pure ()
  let allowed : List Name := ["propext".toName, "Classical.choice".toName, "Quot.sound".toName]
  let footprint ← collectAxioms name
  for dependency in footprint do
    unless allowed.contains dependency do
      throwError "forbidden axiom {dependency} in {name}"
  logInfo "AXIOM_CONTRACT_OK: Poincare.ParabolicHolderMultiplier.forcing._proof_6"
run_cmd do
  let name := "Poincare.ParabolicHolderMultiplier.forcing._proof_7".toName
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
      if info.isAxiom then
        unless ["propext".toName, "Classical.choice".toName, "Quot.sound".toName].contains current do
          throwError "forbidden visited axiom {current} in {name}"
      pending := info.getUsedConstantsAsSet.toList ++ pending
      match info with
      | .recInfo value =>
        pending := value.all ++ pending
        for rule in value.rules do
          pending := rule.ctor :: rule.rhs.getUsedConstants.toList ++ pending
      | .inductInfo value => pending := value.all ++ value.ctors ++ pending
      | .ctorInfo value => pending := value.induct :: pending
      | _ => pure ()
  let allowed : List Name := ["propext".toName, "Classical.choice".toName, "Quot.sound".toName]
  let footprint ← collectAxioms name
  for dependency in footprint do
    unless allowed.contains dependency do
      throwError "forbidden axiom {dependency} in {name}"
  logInfo "AXIOM_CONTRACT_OK: Poincare.ParabolicHolderMultiplier.forcing._proof_7"
run_cmd do
  let name := "Poincare.ParabolicHolderMultiplier.forcing._proof_8".toName
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
      if info.isAxiom then
        unless ["propext".toName, "Classical.choice".toName, "Quot.sound".toName].contains current do
          throwError "forbidden visited axiom {current} in {name}"
      pending := info.getUsedConstantsAsSet.toList ++ pending
      match info with
      | .recInfo value =>
        pending := value.all ++ pending
        for rule in value.rules do
          pending := rule.ctor :: rule.rhs.getUsedConstants.toList ++ pending
      | .inductInfo value => pending := value.all ++ value.ctors ++ pending
      | .ctorInfo value => pending := value.induct :: pending
      | _ => pure ()
  let allowed : List Name := ["propext".toName, "Classical.choice".toName, "Quot.sound".toName]
  let footprint ← collectAxioms name
  for dependency in footprint do
    unless allowed.contains dependency do
      throwError "forbidden axiom {dependency} in {name}"
  logInfo "AXIOM_CONTRACT_OK: Poincare.ParabolicHolderMultiplier.forcing._proof_8"
run_cmd do
  let name := "Poincare.ParabolicHolderMultiplier.forcing._proof_9".toName
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
      if info.isAxiom then
        unless ["propext".toName, "Classical.choice".toName, "Quot.sound".toName].contains current do
          throwError "forbidden visited axiom {current} in {name}"
      pending := info.getUsedConstantsAsSet.toList ++ pending
      match info with
      | .recInfo value =>
        pending := value.all ++ pending
        for rule in value.rules do
          pending := rule.ctor :: rule.rhs.getUsedConstants.toList ++ pending
      | .inductInfo value => pending := value.all ++ value.ctors ++ pending
      | .ctorInfo value => pending := value.induct :: pending
      | _ => pure ()
  let allowed : List Name := ["propext".toName, "Classical.choice".toName, "Quot.sound".toName]
  let footprint ← collectAxioms name
  for dependency in footprint do
    unless allowed.contains dependency do
      throwError "forbidden axiom {dependency} in {name}"
  logInfo "AXIOM_CONTRACT_OK: Poincare.ParabolicHolderMultiplier.forcing._proof_9"
run_cmd do
  let name := "Poincare.ParabolicHolderMultiplier.forcing_apply".toName
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
      if info.isAxiom then
        unless ["propext".toName, "Classical.choice".toName, "Quot.sound".toName].contains current do
          throwError "forbidden visited axiom {current} in {name}"
      pending := info.getUsedConstantsAsSet.toList ++ pending
      match info with
      | .recInfo value =>
        pending := value.all ++ pending
        for rule in value.rules do
          pending := rule.ctor :: rule.rhs.getUsedConstants.toList ++ pending
      | .inductInfo value => pending := value.all ++ value.ctors ++ pending
      | .ctorInfo value => pending := value.induct :: pending
      | _ => pure ()
  let allowed : List Name := ["propext".toName, "Classical.choice".toName, "Quot.sound".toName]
  let footprint ← collectAxioms name
  for dependency in footprint do
    unless allowed.contains dependency do
      throwError "forbidden axiom {dependency} in {name}"
  logInfo "AXIOM_CONTRACT_OK: Poincare.ParabolicHolderMultiplier.forcing_apply"
run_cmd do
  let name := "Poincare.ParabolicHolderMultiplier.forcing_eq_sum".toName
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
      if info.isAxiom then
        unless ["propext".toName, "Classical.choice".toName, "Quot.sound".toName].contains current do
          throwError "forbidden visited axiom {current} in {name}"
      pending := info.getUsedConstantsAsSet.toList ++ pending
      match info with
      | .recInfo value =>
        pending := value.all ++ pending
        for rule in value.rules do
          pending := rule.ctor :: rule.rhs.getUsedConstants.toList ++ pending
      | .inductInfo value => pending := value.all ++ value.ctors ++ pending
      | .ctorInfo value => pending := value.induct :: pending
      | _ => pure ()
  let allowed : List Name := ["propext".toName, "Classical.choice".toName, "Quot.sound".toName]
  let footprint ← collectAxioms name
  for dependency in footprint do
    unless allowed.contains dependency do
      throwError "forbidden axiom {dependency} in {name}"
  logInfo "AXIOM_CONTRACT_OK: Poincare.ParabolicHolderMultiplier.forcing_eq_sum"
run_cmd do
  let name := "Poincare.ParabolicHolderMultiplier.norm_entry_le".toName
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
      if info.isAxiom then
        unless ["propext".toName, "Classical.choice".toName, "Quot.sound".toName].contains current do
          throwError "forbidden visited axiom {current} in {name}"
      pending := info.getUsedConstantsAsSet.toList ++ pending
      match info with
      | .recInfo value =>
        pending := value.all ++ pending
        for rule in value.rules do
          pending := rule.ctor :: rule.rhs.getUsedConstants.toList ++ pending
      | .inductInfo value => pending := value.all ++ value.ctors ++ pending
      | .ctorInfo value => pending := value.induct :: pending
      | _ => pure ()
  let allowed : List Name := ["propext".toName, "Classical.choice".toName, "Quot.sound".toName]
  let footprint ← collectAxioms name
  for dependency in footprint do
    unless allowed.contains dependency do
      throwError "forbidden axiom {dependency} in {name}"
  logInfo "AXIOM_CONTRACT_OK: Poincare.ParabolicHolderMultiplier.norm_entry_le"
run_cmd do
  let name := "Poincare.ParabolicHolderMultiplier.norm_error_le".toName
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
      if info.isAxiom then
        unless ["propext".toName, "Classical.choice".toName, "Quot.sound".toName].contains current do
          throwError "forbidden visited axiom {current} in {name}"
      pending := info.getUsedConstantsAsSet.toList ++ pending
      match info with
      | .recInfo value =>
        pending := value.all ++ pending
        for rule in value.rules do
          pending := rule.ctor :: rule.rhs.getUsedConstants.toList ++ pending
      | .inductInfo value => pending := value.all ++ value.ctors ++ pending
      | .ctorInfo value => pending := value.induct :: pending
      | _ => pure ()
  let allowed : List Name := ["propext".toName, "Classical.choice".toName, "Quot.sound".toName]
  let footprint ← collectAxioms name
  for dependency in footprint do
    unless allowed.contains dependency do
      throwError "forbidden axiom {dependency} in {name}"
  logInfo "AXIOM_CONTRACT_OK: Poincare.ParabolicHolderMultiplier.norm_error_le"
run_cmd do
  let name := "Poincare.ParabolicHolderMultiplier.norm_forcing_le".toName
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
      if info.isAxiom then
        unless ["propext".toName, "Classical.choice".toName, "Quot.sound".toName].contains current do
          throwError "forbidden visited axiom {current} in {name}"
      pending := info.getUsedConstantsAsSet.toList ++ pending
      match info with
      | .recInfo value =>
        pending := value.all ++ pending
        for rule in value.rules do
          pending := rule.ctor :: rule.rhs.getUsedConstants.toList ++ pending
      | .inductInfo value => pending := value.all ++ value.ctors ++ pending
      | .ctorInfo value => pending := value.induct :: pending
      | _ => pure ()
  let allowed : List Name := ["propext".toName, "Classical.choice".toName, "Quot.sound".toName]
  let footprint ← collectAxioms name
  for dependency in footprint do
    unless allowed.contains dependency do
      throwError "forbidden axiom {dependency} in {name}"
  logInfo "AXIOM_CONTRACT_OK: Poincare.ParabolicHolderMultiplier.norm_forcing_le"
run_cmd do
  let name := "Poincare.ParabolicHolderMultiplier.norm_mul_ddu_entry_le".toName
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
      if info.isAxiom then
        unless ["propext".toName, "Classical.choice".toName, "Quot.sound".toName].contains current do
          throwError "forbidden visited axiom {current} in {name}"
      pending := info.getUsedConstantsAsSet.toList ++ pending
      match info with
      | .recInfo value =>
        pending := value.all ++ pending
        for rule in value.rules do
          pending := rule.ctor :: rule.rhs.getUsedConstants.toList ++ pending
      | .inductInfo value => pending := value.all ++ value.ctors ++ pending
      | .ctorInfo value => pending := value.induct :: pending
      | _ => pure ()
  let allowed : List Name := ["propext".toName, "Classical.choice".toName, "Quot.sound".toName]
  let footprint ← collectAxioms name
  for dependency in footprint do
    unless allowed.contains dependency do
      throwError "forbidden axiom {dependency} in {name}"
  logInfo "AXIOM_CONTRACT_OK: Poincare.ParabolicHolderMultiplier.norm_mul_ddu_entry_le"
run_cmd do
  let name := "Poincare.ParabolicHolderMultiplier.norm_mul_split".toName
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
      if info.isAxiom then
        unless ["propext".toName, "Classical.choice".toName, "Quot.sound".toName].contains current do
          throwError "forbidden visited axiom {current} in {name}"
      pending := info.getUsedConstantsAsSet.toList ++ pending
      match info with
      | .recInfo value =>
        pending := value.all ++ pending
        for rule in value.rules do
          pending := rule.ctor :: rule.rhs.getUsedConstants.toList ++ pending
      | .inductInfo value => pending := value.all ++ value.ctors ++ pending
      | .ctorInfo value => pending := value.induct :: pending
      | _ => pure ()
  let allowed : List Name := ["propext".toName, "Classical.choice".toName, "Quot.sound".toName]
  let footprint ← collectAxioms name
  for dependency in footprint do
    unless allowed.contains dependency do
      throwError "forbidden axiom {dependency} in {name}"
  logInfo "AXIOM_CONTRACT_OK: Poincare.ParabolicHolderMultiplier.norm_mul_split"
run_cmd do
  let name := "Poincare.ParabolicHolderMultiplier.sum_apply".toName
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
      if info.isAxiom then
        unless ["propext".toName, "Classical.choice".toName, "Quot.sound".toName].contains current do
          throwError "forbidden visited axiom {current} in {name}"
      pending := info.getUsedConstantsAsSet.toList ++ pending
      match info with
      | .recInfo value =>
        pending := value.all ++ pending
        for rule in value.rules do
          pending := rule.ctor :: rule.rhs.getUsedConstants.toList ++ pending
      | .inductInfo value => pending := value.all ++ value.ctors ++ pending
      | .ctorInfo value => pending := value.induct :: pending
      | _ => pure ()
  let allowed : List Name := ["propext".toName, "Classical.choice".toName, "Quot.sound".toName]
  let footprint ← collectAxioms name
  for dependency in footprint do
    unless allowed.contains dependency do
      throwError "forbidden axiom {dependency} in {name}"
  logInfo "AXIOM_CONTRACT_OK: Poincare.ParabolicHolderMultiplier.sum_apply"
run_cmd do
  let name := "Poincare.ParabolicHolderMultiplier.supNorm_ddu_le".toName
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
      if info.isAxiom then
        unless ["propext".toName, "Classical.choice".toName, "Quot.sound".toName].contains current do
          throwError "forbidden visited axiom {current} in {name}"
      pending := info.getUsedConstantsAsSet.toList ++ pending
      match info with
      | .recInfo value =>
        pending := value.all ++ pending
        for rule in value.rules do
          pending := rule.ctor :: rule.rhs.getUsedConstants.toList ++ pending
      | .inductInfo value => pending := value.all ++ value.ctors ++ pending
      | .ctorInfo value => pending := value.induct :: pending
      | _ => pure ()
  let allowed : List Name := ["propext".toName, "Classical.choice".toName, "Quot.sound".toName]
  let footprint ← collectAxioms name
  for dependency in footprint do
    unless allowed.contains dependency do
      throwError "forbidden axiom {dependency} in {name}"
  logInfo "AXIOM_CONTRACT_OK: Poincare.ParabolicHolderMultiplier.supNorm_ddu_le"
run_cmd do
  let name := "Poincare.ParabolicHolderMultiplier.supNorm_entry_le".toName
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
      if info.isAxiom then
        unless ["propext".toName, "Classical.choice".toName, "Quot.sound".toName].contains current do
          throwError "forbidden visited axiom {current} in {name}"
      pending := info.getUsedConstantsAsSet.toList ++ pending
      match info with
      | .recInfo value =>
        pending := value.all ++ pending
        for rule in value.rules do
          pending := rule.ctor :: rule.rhs.getUsedConstants.toList ++ pending
      | .inductInfo value => pending := value.all ++ value.ctors ++ pending
      | .ctorInfo value => pending := value.induct :: pending
      | _ => pure ()
  let allowed : List Name := ["propext".toName, "Classical.choice".toName, "Quot.sound".toName]
  let footprint ← collectAxioms name
  for dependency in footprint do
    unless allowed.contains dependency do
      throwError "forbidden axiom {dependency} in {name}"
  logInfo "AXIOM_CONTRACT_OK: Poincare.ParabolicHolderMultiplier.supNorm_entry_le"
universe u_1
run_cmd liftTermElabM do
  let info ← getConstInfo "Poincare.ParabolicHolderMultiplier.ddu_time_bound".toName
  unless info.levelParams.map Name.toString == [] do
    throwError "frozen universe parameter names mismatch for {info.name}"
  unless (← isProp info.type) == true do
    throwError "original Prop status mismatch for {info.name}"
  let levels : List Level := []
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "∀ {α T : Real} (G : Poincare.ParabolicSolutionGraph.Graph.{0} (E := Poincare.ClosedSmoothModel (3 : Nat)) α T), LT.lt.{0} (OfNat.ofNat.{0} (nat_lit 0)) T → ∀ {t : Real}, Membership.mem.{0, 0} (Set.Icc.{0} (OfNat.ofNat.{0} (nat_lit 0)) T) t → ∀ (x : Poincare.ClosedSmoothModel (OfNat.ofNat.{0} (nat_lit 3))), LE.le.{0} (Norm.norm.{0} (Subtype.val.{1} (WithLp.fst.{0, 0} (Subtype.val.{1} (Poincare.ParabolicSolutionGraph.Graph.ddu.{0} G))) (Prod.mk.{0, 0} t x))) (HMul.hMul.{0, 0, 0} (Norm.norm.{0} (Poincare.ParabolicSolutionGraph.Graph.ddu.{0} G)) (HPow.hPow.{0, 0, 0} t (HDiv.hDiv.{0, 0, 0} α (OfNat.ofNat.{0} (nat_lit 2)))))" with
    | .ok parsedType => pure parsedType
    | .error error => throwError error
  let expected ← Term.elabType parsedType
  Term.synthesizeSyntheticMVarsNoPostponing
  let expected ← instantiateMVars expected
  if expected.hasMVar || expected.hasLevelMVar then
    throwError "unresolved metavariables in frozen type for {info.name}"
  let actual := info.type.instantiateLevelParams info.levelParams levels
  if actual.hasMVar || actual.hasLevelMVar then
    throwError "metavariables in actual constant type for {info.name}"
  unless (← isProp actual) == (← isProp expected) do
    throwError "frozen Prop status mismatch for {info.name}"
  unless ← isDefEq actual expected do
    throwError "frozen type mismatch for {info.name}: actual {actual}, expected {expected}"
  logInfo "FROZEN_CONTRACT_OK: Poincare.ParabolicHolderMultiplier.ddu_time_bound"
run_cmd liftTermElabM do
  let info ← getConstInfo "Poincare.ParabolicHolderMultiplier.ddu_zero_trace".toName
  unless info.levelParams.map Name.toString == [] do
    throwError "frozen universe parameter names mismatch for {info.name}"
  unless (← isProp info.type) == true do
    throwError "original Prop status mismatch for {info.name}"
  let levels : List Level := []
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "∀ {α T : Real} (G : Poincare.ParabolicSolutionGraph.Graph.{0} (E := Poincare.ClosedSmoothModel (3 : Nat)) α T), LT.lt.{0} (OfNat.ofNat.{0} (nat_lit 0)) T → ∀ (x : Poincare.ClosedSmoothModel (OfNat.ofNat.{0} (nat_lit 3))), Eq.{1} (Subtype.val.{1} (WithLp.fst.{0, 0} (Subtype.val.{1} (Poincare.ParabolicSolutionGraph.Graph.ddu.{0} G))) (Prod.mk.{0, 0} (OfNat.ofNat.{0} (nat_lit 0)) x)) (OfNat.ofNat.{0} (nat_lit 0))" with
    | .ok parsedType => pure parsedType
    | .error error => throwError error
  let expected ← Term.elabType parsedType
  Term.synthesizeSyntheticMVarsNoPostponing
  let expected ← instantiateMVars expected
  if expected.hasMVar || expected.hasLevelMVar then
    throwError "unresolved metavariables in frozen type for {info.name}"
  let actual := info.type.instantiateLevelParams info.levelParams levels
  if actual.hasMVar || actual.hasLevelMVar then
    throwError "metavariables in actual constant type for {info.name}"
  unless (← isProp actual) == (← isProp expected) do
    throwError "frozen Prop status mismatch for {info.name}"
  unless ← isDefEq actual expected do
    throwError "frozen type mismatch for {info.name}: actual {actual}, expected {expected}"
  logInfo "FROZEN_CONTRACT_OK: Poincare.ParabolicHolderMultiplier.ddu_zero_trace"
run_cmd liftTermElabM do
  let info ← getConstInfo "Poincare.ParabolicHolderMultiplier.du_zero_trace".toName
  unless info.levelParams.map Name.toString == [] do
    throwError "frozen universe parameter names mismatch for {info.name}"
  unless (← isProp info.type) == true do
    throwError "original Prop status mismatch for {info.name}"
  let levels : List Level := []
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "∀ {α T : Real} (G : Poincare.ParabolicSolutionGraph.Graph.{0} (E := Poincare.ClosedSmoothModel (3 : Nat)) α T), LT.lt.{0} (OfNat.ofNat.{0} (nat_lit 0)) T → ∀ (x : Poincare.ClosedSmoothModel (OfNat.ofNat.{0} (nat_lit 3))), Eq.{1} (Subtype.val.{1} (WithLp.fst.{0, 0} (Subtype.val.{1} (Poincare.ParabolicSolutionGraph.Graph.du.{0} G))) (Prod.mk.{0, 0} (OfNat.ofNat.{0} (nat_lit 0)) x)) (OfNat.ofNat.{0} (nat_lit 0))" with
    | .ok parsedType => pure parsedType
    | .error error => throwError error
  let expected ← Term.elabType parsedType
  Term.synthesizeSyntheticMVarsNoPostponing
  let expected ← instantiateMVars expected
  if expected.hasMVar || expected.hasLevelMVar then
    throwError "unresolved metavariables in frozen type for {info.name}"
  let actual := info.type.instantiateLevelParams info.levelParams levels
  if actual.hasMVar || actual.hasLevelMVar then
    throwError "metavariables in actual constant type for {info.name}"
  unless (← isProp actual) == (← isProp expected) do
    throwError "frozen Prop status mismatch for {info.name}"
  unless ← isDefEq actual expected do
    throwError "frozen type mismatch for {info.name}: actual {actual}, expected {expected}"
  logInfo "FROZEN_CONTRACT_OK: Poincare.ParabolicHolderMultiplier.du_zero_trace"
run_cmd liftTermElabM do
  let info ← getConstInfo "Poincare.ParabolicHolderMultiplier.entry".toName
  unless info.levelParams.map Name.toString == [] do
    throwError "frozen universe parameter names mismatch for {info.name}"
  unless (← isProp info.type) == false do
    throwError "original Prop status mismatch for {info.name}"
  let levels : List Level := []
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "{α T : Real} → Poincare.ParabolicHolder.Y.{0, 0} (E := Poincare.ClosedSmoothModel (3 : Nat)) α T (ContinuousLinearMap.{0, 0, 0, 0} (RingHom.id.{0} Real) (Poincare.ClosedSmoothModel (OfNat.ofNat.{0} (nat_lit 3))) (ContinuousLinearMap.{0, 0, 0, 0} (RingHom.id.{0} Real) (Poincare.ClosedSmoothModel (OfNat.ofNat.{0} (nat_lit 3))) Real)) → (v w : Poincare.ClosedSmoothModel (OfNat.ofNat.{0} (nat_lit 3))) → Eq.{1} (Norm.norm.{0} v) (OfNat.ofNat.{0} (nat_lit 1)) → Eq.{1} (Norm.norm.{0} w) (OfNat.ofNat.{0} (nat_lit 1)) → Poincare.ParabolicHolder.Y.{0, 0} (E := Poincare.ClosedSmoothModel (3 : Nat)) α T Real" with
    | .ok parsedType => pure parsedType
    | .error error => throwError error
  let expected ← Term.elabType parsedType
  Term.synthesizeSyntheticMVarsNoPostponing
  let expected ← instantiateMVars expected
  if expected.hasMVar || expected.hasLevelMVar then
    throwError "unresolved metavariables in frozen type for {info.name}"
  let actual := info.type.instantiateLevelParams info.levelParams levels
  if actual.hasMVar || actual.hasLevelMVar then
    throwError "metavariables in actual constant type for {info.name}"
  unless (← isProp actual) == (← isProp expected) do
    throwError "frozen Prop status mismatch for {info.name}"
  unless ← isDefEq actual expected do
    throwError "frozen type mismatch for {info.name}: actual {actual}, expected {expected}"
  logInfo "FROZEN_CONTRACT_OK: Poincare.ParabolicHolderMultiplier.entry"
run_cmd liftTermElabM do
  let info ← getConstInfo "Poincare.ParabolicHolderMultiplier.entry._proof_1".toName
  unless info.levelParams.map Name.toString == [] do
    throwError "frozen universe parameter names mismatch for {info.name}"
  unless (← isProp info.type) == true do
    throwError "original Prop status mismatch for {info.name}"
  let levels : List Level := []
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "ContinuousAdd.{0} Real" with
    | .ok parsedType => pure parsedType
    | .error error => throwError error
  let expected ← Term.elabType parsedType
  Term.synthesizeSyntheticMVarsNoPostponing
  let expected ← instantiateMVars expected
  if expected.hasMVar || expected.hasLevelMVar then
    throwError "unresolved metavariables in frozen type for {info.name}"
  let actual := info.type.instantiateLevelParams info.levelParams levels
  if actual.hasMVar || actual.hasLevelMVar then
    throwError "metavariables in actual constant type for {info.name}"
  unless (← isProp actual) == (← isProp expected) do
    throwError "frozen Prop status mismatch for {info.name}"
  unless ← isDefEq actual expected do
    throwError "frozen type mismatch for {info.name}: actual {actual}, expected {expected}"
  logInfo "FROZEN_CONTRACT_OK: Poincare.ParabolicHolderMultiplier.entry._proof_1"
run_cmd liftTermElabM do
  let info ← getConstInfo "Poincare.ParabolicHolderMultiplier.entry._proof_10".toName
  unless info.levelParams.map Name.toString == [] do
    throwError "frozen universe parameter names mismatch for {info.name}"
  unless (← isProp info.type) == true do
    throwError "original Prop status mismatch for {info.name}"
  let levels : List Level := []
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "∀ {T : Real} (i : Poincare.ParabolicHolder.Pairs.{0} (Poincare.ParabolicHolder.cylinder.{0} (E := Poincare.ClosedSmoothModel (3 : Nat)) T)), IsBoundedSMul.{0, 0} Real (ContinuousLinearMap.{0, 0, 0, 0} (RingHom.id.{0} Real) (Poincare.ClosedSmoothModel (OfNat.ofNat.{0} (nat_lit 3))) (ContinuousLinearMap.{0, 0, 0, 0} (RingHom.id.{0} Real) (Poincare.ClosedSmoothModel (OfNat.ofNat.{0} (nat_lit 3))) Real))" with
    | .ok parsedType => pure parsedType
    | .error error => throwError error
  let expected ← Term.elabType parsedType
  Term.synthesizeSyntheticMVarsNoPostponing
  let expected ← instantiateMVars expected
  if expected.hasMVar || expected.hasLevelMVar then
    throwError "unresolved metavariables in frozen type for {info.name}"
  let actual := info.type.instantiateLevelParams info.levelParams levels
  if actual.hasMVar || actual.hasLevelMVar then
    throwError "metavariables in actual constant type for {info.name}"
  unless (← isProp actual) == (← isProp expected) do
    throwError "frozen Prop status mismatch for {info.name}"
  unless ← isDefEq actual expected do
    throwError "frozen type mismatch for {info.name}: actual {actual}, expected {expected}"
  logInfo "FROZEN_CONTRACT_OK: Poincare.ParabolicHolderMultiplier.entry._proof_10"
run_cmd liftTermElabM do
  let info ← getConstInfo "Poincare.ParabolicHolderMultiplier.entry._proof_11".toName
  unless info.levelParams.map Name.toString == [] do
    throwError "frozen universe parameter names mismatch for {info.name}"
  unless (← isProp info.type) == true do
    throwError "original Prop status mismatch for {info.name}"
  let levels : List Level := []
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "∀ {α T : Real} (H : Poincare.ParabolicHolder.Y.{0, 0} (E := Poincare.ClosedSmoothModel (3 : Nat)) α T (ContinuousLinearMap.{0, 0, 0, 0} (RingHom.id.{0} Real) (Poincare.ClosedSmoothModel (OfNat.ofNat.{0} (nat_lit 3))) (ContinuousLinearMap.{0, 0, 0, 0} (RingHom.id.{0} Real) (Poincare.ClosedSmoothModel (OfNat.ofNat.{0} (nat_lit 3))) Real))) (v w : Poincare.ClosedSmoothModel (OfNat.ofNat.{0} (nat_lit 3))), ∀ p ∉ Poincare.ParabolicHolder.cylinder.{0} (E := Poincare.ClosedSmoothModel (3 : Nat)) T, Eq.{1} (DFunLike.coe.{1, 1, 1} (DFunLike.coe.{1, 1, 1} (Subtype.val.{1} (WithLp.fst.{0, 0} (Subtype.val.{1} H)) p) v) w) (OfNat.ofNat.{0} (nat_lit 0))" with
    | .ok parsedType => pure parsedType
    | .error error => throwError error
  let expected ← Term.elabType parsedType
  Term.synthesizeSyntheticMVarsNoPostponing
  let expected ← instantiateMVars expected
  if expected.hasMVar || expected.hasLevelMVar then
    throwError "unresolved metavariables in frozen type for {info.name}"
  let actual := info.type.instantiateLevelParams info.levelParams levels
  if actual.hasMVar || actual.hasLevelMVar then
    throwError "metavariables in actual constant type for {info.name}"
  unless (← isProp actual) == (← isProp expected) do
    throwError "frozen Prop status mismatch for {info.name}"
  unless ← isDefEq actual expected do
    throwError "frozen type mismatch for {info.name}: actual {actual}, expected {expected}"
  logInfo "FROZEN_CONTRACT_OK: Poincare.ParabolicHolderMultiplier.entry._proof_11"
run_cmd liftTermElabM do
  let info ← getConstInfo "Poincare.ParabolicHolderMultiplier.entry._proof_12".toName
  unless info.levelParams.map Name.toString == [] do
    throwError "frozen universe parameter names mismatch for {info.name}"
  unless (← isProp info.type) == true do
    throwError "original Prop status mismatch for {info.name}"
  let levels : List Level := []
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "∀ {α T : Real} (H : Poincare.ParabolicHolder.Y.{0, 0} (E := Poincare.ClosedSmoothModel (3 : Nat)) α T (ContinuousLinearMap.{0, 0, 0, 0} (RingHom.id.{0} Real) (Poincare.ClosedSmoothModel (OfNat.ofNat.{0} (nat_lit 3))) (ContinuousLinearMap.{0, 0, 0, 0} (RingHom.id.{0} Real) (Poincare.ClosedSmoothModel (OfNat.ofNat.{0} (nat_lit 3))) Real))) (v w : Poincare.ClosedSmoothModel (OfNat.ofNat.{0} (nat_lit 3))), Eq.{1} (Norm.norm.{0} v) (OfNat.ofNat.{0} (nat_lit 1)) → Eq.{1} (Norm.norm.{0} w) (OfNat.ofNat.{0} (nat_lit 1)) → ∃ (M : Real), ∀ (p : Prod.{0, 0} Real (Poincare.ClosedSmoothModel (OfNat.ofNat.{0} (nat_lit 3)))), Membership.mem.{0, 0} (Poincare.ParabolicHolder.cylinder.{0} (E := Poincare.ClosedSmoothModel (3 : Nat)) T) p → LE.le.{0} (Norm.norm.{0} (DFunLike.coe.{1, 1, 1} (DFunLike.coe.{1, 1, 1} (Subtype.val.{1} (WithLp.fst.{0, 0} (Subtype.val.{1} H)) p) v) w)) M" with
    | .ok parsedType => pure parsedType
    | .error error => throwError error
  let expected ← Term.elabType parsedType
  Term.synthesizeSyntheticMVarsNoPostponing
  let expected ← instantiateMVars expected
  if expected.hasMVar || expected.hasLevelMVar then
    throwError "unresolved metavariables in frozen type for {info.name}"
  let actual := info.type.instantiateLevelParams info.levelParams levels
  if actual.hasMVar || actual.hasLevelMVar then
    throwError "metavariables in actual constant type for {info.name}"
  unless (← isProp actual) == (← isProp expected) do
    throwError "frozen Prop status mismatch for {info.name}"
  unless ← isDefEq actual expected do
    throwError "frozen type mismatch for {info.name}: actual {actual}, expected {expected}"
  logInfo "FROZEN_CONTRACT_OK: Poincare.ParabolicHolderMultiplier.entry._proof_12"
run_cmd liftTermElabM do
  let info ← getConstInfo "Poincare.ParabolicHolderMultiplier.entry._proof_13".toName
  unless info.levelParams.map Name.toString == [] do
    throwError "frozen universe parameter names mismatch for {info.name}"
  unless (← isProp info.type) == true do
    throwError "original Prop status mismatch for {info.name}"
  let levels : List Level := []
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "∀ {α T : Real} (H : Poincare.ParabolicHolder.Y.{0, 0} (E := Poincare.ClosedSmoothModel (3 : Nat)) α T (ContinuousLinearMap.{0, 0, 0, 0} (RingHom.id.{0} Real) (Poincare.ClosedSmoothModel (OfNat.ofNat.{0} (nat_lit 3))) (ContinuousLinearMap.{0, 0, 0, 0} (RingHom.id.{0} Real) (Poincare.ClosedSmoothModel (OfNat.ofNat.{0} (nat_lit 3))) Real))) (v w : Poincare.ClosedSmoothModel (OfNat.ofNat.{0} (nat_lit 3))), Eq.{1} (Norm.norm.{0} v) (OfNat.ofNat.{0} (nat_lit 1)) → Eq.{1} (Norm.norm.{0} w) (OfNat.ofNat.{0} (nat_lit 1)) → ∃ (K : Real), Poincare.ParabolicHolder.HasHolderBound.{0, 0} α (Poincare.ParabolicHolder.cylinder.{0} (E := Poincare.ClosedSmoothModel (3 : Nat)) T) (fun (p : Prod.{0, 0} Real (Poincare.ClosedSmoothModel (OfNat.ofNat.{0} (nat_lit 3)))) => DFunLike.coe.{1, 1, 1} (DFunLike.coe.{1, 1, 1} (Subtype.val.{1} (WithLp.fst.{0, 0} (Subtype.val.{1} H)) p) v) w) K" with
    | .ok parsedType => pure parsedType
    | .error error => throwError error
  let expected ← Term.elabType parsedType
  Term.synthesizeSyntheticMVarsNoPostponing
  let expected ← instantiateMVars expected
  if expected.hasMVar || expected.hasLevelMVar then
    throwError "unresolved metavariables in frozen type for {info.name}"
  let actual := info.type.instantiateLevelParams info.levelParams levels
  if actual.hasMVar || actual.hasLevelMVar then
    throwError "metavariables in actual constant type for {info.name}"
  unless (← isProp actual) == (← isProp expected) do
    throwError "frozen Prop status mismatch for {info.name}"
  unless ← isDefEq actual expected do
    throwError "frozen type mismatch for {info.name}: actual {actual}, expected {expected}"
  logInfo "FROZEN_CONTRACT_OK: Poincare.ParabolicHolderMultiplier.entry._proof_13"
run_cmd liftTermElabM do
  let info ← getConstInfo "Poincare.ParabolicHolderMultiplier.entry._proof_2".toName
  unless info.levelParams.map Name.toString == [] do
    throwError "frozen universe parameter names mismatch for {info.name}"
  unless (← isProp info.type) == true do
    throwError "original Prop status mismatch for {info.name}"
  let levels : List Level := []
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "SMulCommClass.{0, 0, 0} Real Real Real" with
    | .ok parsedType => pure parsedType
    | .error error => throwError error
  let expected ← Term.elabType parsedType
  Term.synthesizeSyntheticMVarsNoPostponing
  let expected ← instantiateMVars expected
  if expected.hasMVar || expected.hasLevelMVar then
    throwError "unresolved metavariables in frozen type for {info.name}"
  let actual := info.type.instantiateLevelParams info.levelParams levels
  if actual.hasMVar || actual.hasLevelMVar then
    throwError "metavariables in actual constant type for {info.name}"
  unless (← isProp actual) == (← isProp expected) do
    throwError "frozen Prop status mismatch for {info.name}"
  unless ← isDefEq actual expected do
    throwError "frozen type mismatch for {info.name}: actual {actual}, expected {expected}"
  logInfo "FROZEN_CONTRACT_OK: Poincare.ParabolicHolderMultiplier.entry._proof_2"
run_cmd liftTermElabM do
  let info ← getConstInfo "Poincare.ParabolicHolderMultiplier.entry._proof_3".toName
  unless info.levelParams.map Name.toString == [] do
    throwError "frozen universe parameter names mismatch for {info.name}"
  unless (← isProp info.type) == true do
    throwError "original Prop status mismatch for {info.name}"
  let levels : List Level := []
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "ContinuousConstSMul.{0, 0} Real Real" with
    | .ok parsedType => pure parsedType
    | .error error => throwError error
  let expected ← Term.elabType parsedType
  Term.synthesizeSyntheticMVarsNoPostponing
  let expected ← instantiateMVars expected
  if expected.hasMVar || expected.hasLevelMVar then
    throwError "unresolved metavariables in frozen type for {info.name}"
  let actual := info.type.instantiateLevelParams info.levelParams levels
  if actual.hasMVar || actual.hasLevelMVar then
    throwError "metavariables in actual constant type for {info.name}"
  unless (← isProp actual) == (← isProp expected) do
    throwError "frozen Prop status mismatch for {info.name}"
  unless ← isDefEq actual expected do
    throwError "frozen type mismatch for {info.name}: actual {actual}, expected {expected}"
  logInfo "FROZEN_CONTRACT_OK: Poincare.ParabolicHolderMultiplier.entry._proof_3"
run_cmd liftTermElabM do
  let info ← getConstInfo "Poincare.ParabolicHolderMultiplier.entry._proof_4".toName
  unless info.levelParams.map Name.toString == [] do
    throwError "frozen universe parameter names mismatch for {info.name}"
  unless (← isProp info.type) == true do
    throwError "original Prop status mismatch for {info.name}"
  let levels : List Level := []
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "RingHomIsometric.{0, 0} (RingHom.id.{0} Real)" with
    | .ok parsedType => pure parsedType
    | .error error => throwError error
  let expected ← Term.elabType parsedType
  Term.synthesizeSyntheticMVarsNoPostponing
  let expected ← instantiateMVars expected
  if expected.hasMVar || expected.hasLevelMVar then
    throwError "unresolved metavariables in frozen type for {info.name}"
  let actual := info.type.instantiateLevelParams info.levelParams levels
  if actual.hasMVar || actual.hasLevelMVar then
    throwError "metavariables in actual constant type for {info.name}"
  unless (← isProp actual) == (← isProp expected) do
    throwError "frozen Prop status mismatch for {info.name}"
  unless ← isDefEq actual expected do
    throwError "frozen type mismatch for {info.name}: actual {actual}, expected {expected}"
  logInfo "FROZEN_CONTRACT_OK: Poincare.ParabolicHolderMultiplier.entry._proof_4"
run_cmd liftTermElabM do
  let info ← getConstInfo "Poincare.ParabolicHolderMultiplier.entry._proof_5".toName
  unless info.levelParams.map Name.toString == [] do
    throwError "frozen universe parameter names mismatch for {info.name}"
  unless (← isProp info.type) == true do
    throwError "original Prop status mismatch for {info.name}"
  let levels : List Level := []
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "SMulCommClass.{0, 0, 0} Real Real Real" with
    | .ok parsedType => pure parsedType
    | .error error => throwError error
  let expected ← Term.elabType parsedType
  Term.synthesizeSyntheticMVarsNoPostponing
  let expected ← instantiateMVars expected
  if expected.hasMVar || expected.hasLevelMVar then
    throwError "unresolved metavariables in frozen type for {info.name}"
  let actual := info.type.instantiateLevelParams info.levelParams levels
  if actual.hasMVar || actual.hasLevelMVar then
    throwError "metavariables in actual constant type for {info.name}"
  unless (← isProp actual) == (← isProp expected) do
    throwError "frozen Prop status mismatch for {info.name}"
  unless ← isDefEq actual expected do
    throwError "frozen type mismatch for {info.name}: actual {actual}, expected {expected}"
  logInfo "FROZEN_CONTRACT_OK: Poincare.ParabolicHolderMultiplier.entry._proof_5"
run_cmd liftTermElabM do
  let info ← getConstInfo "Poincare.ParabolicHolderMultiplier.entry._proof_6".toName
  unless info.levelParams.map Name.toString == [] do
    throwError "frozen universe parameter names mismatch for {info.name}"
  unless (← isProp info.type) == true do
    throwError "original Prop status mismatch for {info.name}"
  let levels : List Level := []
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "ContinuousConstSMul.{0, 0} Real Real" with
    | .ok parsedType => pure parsedType
    | .error error => throwError error
  let expected ← Term.elabType parsedType
  Term.synthesizeSyntheticMVarsNoPostponing
  let expected ← instantiateMVars expected
  if expected.hasMVar || expected.hasLevelMVar then
    throwError "unresolved metavariables in frozen type for {info.name}"
  let actual := info.type.instantiateLevelParams info.levelParams levels
  if actual.hasMVar || actual.hasLevelMVar then
    throwError "metavariables in actual constant type for {info.name}"
  unless (← isProp actual) == (← isProp expected) do
    throwError "frozen Prop status mismatch for {info.name}"
  unless ← isDefEq actual expected do
    throwError "frozen type mismatch for {info.name}: actual {actual}, expected {expected}"
  logInfo "FROZEN_CONTRACT_OK: Poincare.ParabolicHolderMultiplier.entry._proof_6"
run_cmd liftTermElabM do
  let info ← getConstInfo "Poincare.ParabolicHolderMultiplier.entry._proof_7".toName
  unless info.levelParams.map Name.toString == [] do
    throwError "frozen universe parameter names mismatch for {info.name}"
  unless (← isProp info.type) == true do
    throwError "original Prop status mismatch for {info.name}"
  let levels : List Level := []
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "ContinuousConstSMul.{0, 0} Real Real" with
    | .ok parsedType => pure parsedType
    | .error error => throwError error
  let expected ← Term.elabType parsedType
  Term.synthesizeSyntheticMVarsNoPostponing
  let expected ← instantiateMVars expected
  if expected.hasMVar || expected.hasLevelMVar then
    throwError "unresolved metavariables in frozen type for {info.name}"
  let actual := info.type.instantiateLevelParams info.levelParams levels
  if actual.hasMVar || actual.hasLevelMVar then
    throwError "metavariables in actual constant type for {info.name}"
  unless (← isProp actual) == (← isProp expected) do
    throwError "frozen Prop status mismatch for {info.name}"
  unless ← isDefEq actual expected do
    throwError "frozen type mismatch for {info.name}: actual {actual}, expected {expected}"
  logInfo "FROZEN_CONTRACT_OK: Poincare.ParabolicHolderMultiplier.entry._proof_7"
run_cmd liftTermElabM do
  let info ← getConstInfo "Poincare.ParabolicHolderMultiplier.entry._proof_8".toName
  unless info.levelParams.map Name.toString == [] do
    throwError "frozen universe parameter names mismatch for {info.name}"
  unless (← isProp info.type) == true do
    throwError "original Prop status mismatch for {info.name}"
  let levels : List Level := []
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "SMulCommClass.{0, 0, 0} Real Real (ContinuousLinearMap.{0, 0, 0, 0} (RingHom.id.{0} Real) (Poincare.ClosedSmoothModel (OfNat.ofNat.{0} (nat_lit 3))) Real)" with
    | .ok parsedType => pure parsedType
    | .error error => throwError error
  let expected ← Term.elabType parsedType
  Term.synthesizeSyntheticMVarsNoPostponing
  let expected ← instantiateMVars expected
  if expected.hasMVar || expected.hasLevelMVar then
    throwError "unresolved metavariables in frozen type for {info.name}"
  let actual := info.type.instantiateLevelParams info.levelParams levels
  if actual.hasMVar || actual.hasLevelMVar then
    throwError "metavariables in actual constant type for {info.name}"
  unless (← isProp actual) == (← isProp expected) do
    throwError "frozen Prop status mismatch for {info.name}"
  unless ← isDefEq actual expected do
    throwError "frozen type mismatch for {info.name}: actual {actual}, expected {expected}"
  logInfo "FROZEN_CONTRACT_OK: Poincare.ParabolicHolderMultiplier.entry._proof_8"
run_cmd liftTermElabM do
  let info ← getConstInfo "Poincare.ParabolicHolderMultiplier.entry._proof_9".toName
  unless info.levelParams.map Name.toString == [] do
    throwError "frozen universe parameter names mismatch for {info.name}"
  unless (← isProp info.type) == true do
    throwError "original Prop status mismatch for {info.name}"
  let levels : List Level := []
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "∀ (i : Prod.{0, 0} Real (Poincare.ClosedSmoothModel (OfNat.ofNat.{0} (nat_lit 3)))), IsBoundedSMul.{0, 0} Real (ContinuousLinearMap.{0, 0, 0, 0} (RingHom.id.{0} Real) (Poincare.ClosedSmoothModel (OfNat.ofNat.{0} (nat_lit 3))) (ContinuousLinearMap.{0, 0, 0, 0} (RingHom.id.{0} Real) (Poincare.ClosedSmoothModel (OfNat.ofNat.{0} (nat_lit 3))) Real))" with
    | .ok parsedType => pure parsedType
    | .error error => throwError error
  let expected ← Term.elabType parsedType
  Term.synthesizeSyntheticMVarsNoPostponing
  let expected ← instantiateMVars expected
  if expected.hasMVar || expected.hasLevelMVar then
    throwError "unresolved metavariables in frozen type for {info.name}"
  let actual := info.type.instantiateLevelParams info.levelParams levels
  if actual.hasMVar || actual.hasLevelMVar then
    throwError "metavariables in actual constant type for {info.name}"
  unless (← isProp actual) == (← isProp expected) do
    throwError "frozen Prop status mismatch for {info.name}"
  unless ← isDefEq actual expected do
    throwError "frozen type mismatch for {info.name}: actual {actual}, expected {expected}"
  logInfo "FROZEN_CONTRACT_OK: Poincare.ParabolicHolderMultiplier.entry._proof_9"
run_cmd liftTermElabM do
  let info ← getConstInfo "Poincare.ParabolicHolderMultiplier.entry.congr_simp".toName
  unless info.levelParams.map Name.toString == [] do
    throwError "frozen universe parameter names mismatch for {info.name}"
  unless (← isProp info.type) == true do
    throwError "original Prop status mismatch for {info.name}"
  let levels : List Level := []
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "∀ {α T : Real} (H H_1 : Poincare.ParabolicHolder.Y.{0, 0} (E := Poincare.ClosedSmoothModel (3 : Nat)) α T (ContinuousLinearMap.{0, 0, 0, 0} (RingHom.id.{0} Real) (Poincare.ClosedSmoothModel (OfNat.ofNat.{0} (nat_lit 3))) (ContinuousLinearMap.{0, 0, 0, 0} (RingHom.id.{0} Real) (Poincare.ClosedSmoothModel (OfNat.ofNat.{0} (nat_lit 3))) Real))), Eq.{1} H H_1 → ∀ (v v_1 : Poincare.ClosedSmoothModel (OfNat.ofNat.{0} (nat_lit 3))) (e_v : Eq.{1} v v_1) (w w_1 : Poincare.ClosedSmoothModel (OfNat.ofNat.{0} (nat_lit 3))) (e_w : Eq.{1} w w_1) (hv : Eq.{1} (Norm.norm.{0} v) (OfNat.ofNat.{0} (nat_lit 1))) (hw : Eq.{1} (Norm.norm.{0} w) (OfNat.ofNat.{0} (nat_lit 1))), Eq.{1} (Poincare.ParabolicHolderMultiplier.entry H v w hv hw) (Poincare.ParabolicHolderMultiplier.entry H_1 v_1 w_1 (Eq.ndrec.{0, 1} hv e_v) (Eq.ndrec.{0, 1} hw e_w))" with
    | .ok parsedType => pure parsedType
    | .error error => throwError error
  let expected ← Term.elabType parsedType
  Term.synthesizeSyntheticMVarsNoPostponing
  let expected ← instantiateMVars expected
  if expected.hasMVar || expected.hasLevelMVar then
    throwError "unresolved metavariables in frozen type for {info.name}"
  let actual := info.type.instantiateLevelParams info.levelParams levels
  if actual.hasMVar || actual.hasLevelMVar then
    throwError "metavariables in actual constant type for {info.name}"
  unless (← isProp actual) == (← isProp expected) do
    throwError "frozen Prop status mismatch for {info.name}"
  unless ← isDefEq actual expected do
    throwError "frozen type mismatch for {info.name}: actual {actual}, expected {expected}"
  logInfo "FROZEN_CONTRACT_OK: Poincare.ParabolicHolderMultiplier.entry.congr_simp"
run_cmd liftTermElabM do
  let info ← getConstInfo "Poincare.ParabolicHolderMultiplier.entry_apply".toName
  unless info.levelParams.map Name.toString == [] do
    throwError "frozen universe parameter names mismatch for {info.name}"
  unless (← isProp info.type) == true do
    throwError "original Prop status mismatch for {info.name}"
  let levels : List Level := []
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "∀ {α T : Real} (H : Poincare.ParabolicHolder.Y.{0, 0} (E := Poincare.ClosedSmoothModel (3 : Nat)) α T (ContinuousLinearMap.{0, 0, 0, 0} (RingHom.id.{0} Real) (Poincare.ClosedSmoothModel (OfNat.ofNat.{0} (nat_lit 3))) (ContinuousLinearMap.{0, 0, 0, 0} (RingHom.id.{0} Real) (Poincare.ClosedSmoothModel (OfNat.ofNat.{0} (nat_lit 3))) Real))) (v w : Poincare.ClosedSmoothModel (OfNat.ofNat.{0} (nat_lit 3))) (hv : Eq.{1} (Norm.norm.{0} v) (OfNat.ofNat.{0} (nat_lit 1))) (hw : Eq.{1} (Norm.norm.{0} w) (OfNat.ofNat.{0} (nat_lit 1))) (p : Prod.{0, 0} Real (Poincare.ClosedSmoothModel (OfNat.ofNat.{0} (nat_lit 3)))), Eq.{1} (Subtype.val.{1} (WithLp.fst.{0, 0} (Subtype.val.{1} (Poincare.ParabolicHolderMultiplier.entry H v w hv hw))) p) (DFunLike.coe.{1, 1, 1} (DFunLike.coe.{1, 1, 1} (Subtype.val.{1} (WithLp.fst.{0, 0} (Subtype.val.{1} H)) p) v) w)" with
    | .ok parsedType => pure parsedType
    | .error error => throwError error
  let expected ← Term.elabType parsedType
  Term.synthesizeSyntheticMVarsNoPostponing
  let expected ← instantiateMVars expected
  if expected.hasMVar || expected.hasLevelMVar then
    throwError "unresolved metavariables in frozen type for {info.name}"
  let actual := info.type.instantiateLevelParams info.levelParams levels
  if actual.hasMVar || actual.hasLevelMVar then
    throwError "metavariables in actual constant type for {info.name}"
  unless (← isProp actual) == (← isProp expected) do
    throwError "frozen Prop status mismatch for {info.name}"
  unless ← isDefEq actual expected do
    throwError "frozen type mismatch for {info.name}: actual {actual}, expected {expected}"
  logInfo "FROZEN_CONTRACT_OK: Poincare.ParabolicHolderMultiplier.entry_apply"
run_cmd liftTermElabM do
  let info ← getConstInfo "Poincare.ParabolicHolderMultiplier.entry_holderBound".toName
  unless info.levelParams.map Name.toString == [] do
    throwError "frozen universe parameter names mismatch for {info.name}"
  unless (← isProp info.type) == true do
    throwError "original Prop status mismatch for {info.name}"
  let levels : List Level := []
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "∀ {α T : Real} (H : Poincare.ParabolicHolder.Y.{0, 0} (E := Poincare.ClosedSmoothModel (3 : Nat)) α T (ContinuousLinearMap.{0, 0, 0, 0} (RingHom.id.{0} Real) (Poincare.ClosedSmoothModel (OfNat.ofNat.{0} (nat_lit 3))) (ContinuousLinearMap.{0, 0, 0, 0} (RingHom.id.{0} Real) (Poincare.ClosedSmoothModel (OfNat.ofNat.{0} (nat_lit 3))) Real))) {v w : Poincare.ClosedSmoothModel (OfNat.ofNat.{0} (nat_lit 3))}, Eq.{1} (Norm.norm.{0} v) (OfNat.ofNat.{0} (nat_lit 1)) → Eq.{1} (Norm.norm.{0} w) (OfNat.ofNat.{0} (nat_lit 1)) → Poincare.ParabolicHolder.HasHolderBound.{0, 0} α (Poincare.ParabolicHolder.cylinder.{0} (E := Poincare.ClosedSmoothModel (3 : Nat)) T) (fun (p : Prod.{0, 0} Real (Poincare.ClosedSmoothModel (OfNat.ofNat.{0} (nat_lit 3)))) => DFunLike.coe.{1, 1, 1} (DFunLike.coe.{1, 1, 1} (Subtype.val.{1} (WithLp.fst.{0, 0} (Subtype.val.{1} H)) p) v) w) (Poincare.ParabolicHolder.holderSeminorm.{0, 0} α (Poincare.ParabolicHolder.cylinder.{0} (E := Poincare.ClosedSmoothModel (3 : Nat)) T) (Subtype.val.{1} (WithLp.fst.{0, 0} (Subtype.val.{1} H))))" with
    | .ok parsedType => pure parsedType
    | .error error => throwError error
  let expected ← Term.elabType parsedType
  Term.synthesizeSyntheticMVarsNoPostponing
  let expected ← instantiateMVars expected
  if expected.hasMVar || expected.hasLevelMVar then
    throwError "unresolved metavariables in frozen type for {info.name}"
  let actual := info.type.instantiateLevelParams info.levelParams levels
  if actual.hasMVar || actual.hasLevelMVar then
    throwError "metavariables in actual constant type for {info.name}"
  unless (← isProp actual) == (← isProp expected) do
    throwError "frozen Prop status mismatch for {info.name}"
  unless ← isDefEq actual expected do
    throwError "frozen type mismatch for {info.name}: actual {actual}, expected {expected}"
  logInfo "FROZEN_CONTRACT_OK: Poincare.ParabolicHolderMultiplier.entry_holderBound"
run_cmd liftTermElabM do
  let info ← getConstInfo "Poincare.ParabolicHolderMultiplier.error_small".toName
  unless info.levelParams.map Name.toString == [] do
    throwError "frozen universe parameter names mismatch for {info.name}"
  unless (← isProp info.type) == true do
    throwError "original Prop status mismatch for {info.name}"
  let levels : List Level := []
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "∀ {α T : Real} (b : Fin (OfNat.ofNat.{0} (nat_lit 3)) → Fin (OfNat.ofNat.{0} (nat_lit 3)) → Poincare.ParabolicHolder.Y.{0, 0} (E := Poincare.ClosedSmoothModel (3 : Nat)) α T Real) (S : ContinuousLinearMap.{0, 0, 0, 0} (RingHom.id.{0} Real) (Poincare.ParabolicHolder.Y.{0, 0} (E := Poincare.ClosedSmoothModel (3 : Nat)) α T Real) (Poincare.ParabolicSolutionGraph.Graph.{0} (E := Poincare.ClosedSmoothModel (3 : Nat)) α T)), LT.lt.{0} (OfNat.ofNat.{0} (nat_lit 0)) α → LT.lt.{0} (OfNat.ofNat.{0} (nat_lit 0)) T → ∀ {ε Λ C_S : Real}, (∀ (i j : Fin (OfNat.ofNat.{0} (nat_lit 3))), LE.le.{0} (Poincare.ParabolicHolder.supNorm.{0, 0} (Poincare.ParabolicHolder.cylinder.{0} (E := Poincare.ClosedSmoothModel (3 : Nat)) T) (Subtype.val.{1} (WithLp.fst.{0, 0} (Subtype.val.{1} (b i j))))) ε) → (∀ (i j : Fin (OfNat.ofNat.{0} (nat_lit 3))), LE.le.{0} (Poincare.ParabolicHolder.holderSeminorm.{0, 0} α (Poincare.ParabolicHolder.cylinder.{0} (E := Poincare.ClosedSmoothModel (3 : Nat)) T) (Subtype.val.{1} (WithLp.fst.{0, 0} (Subtype.val.{1} (b i j))))) Λ) → LE.le.{0} (Norm.norm.{0} S) C_S → LE.le.{0} (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (OfNat.ofNat.{0} (nat_lit 9)) C_S) ε) (HDiv.hDiv.{0, 0, 0} (OfNat.ofNat.{0} (nat_lit 1)) (OfNat.ofNat.{0} (nat_lit 4))) → LE.le.{0} (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (OfNat.ofNat.{0} (nat_lit 9)) C_S) Λ) (HPow.hPow.{0, 0, 0} T (HDiv.hDiv.{0, 0, 0} α (OfNat.ofNat.{0} (nat_lit 2))))) (HDiv.hDiv.{0, 0, 0} (OfNat.ofNat.{0} (nat_lit 1)) (OfNat.ofNat.{0} (nat_lit 4))) → ∀ (f : Poincare.ParabolicHolder.Y.{0, 0} (E := Poincare.ClosedSmoothModel (3 : Nat)) α T Real), LE.le.{0} (Norm.norm.{0} (Poincare.ParabolicHolderMultiplier.forcing b (DFunLike.coe.{1, 1, 1} S f))) (HMul.hMul.{0, 0, 0} (HDiv.hDiv.{0, 0, 0} (OfNat.ofNat.{0} (nat_lit 1)) (OfNat.ofNat.{0} (nat_lit 2))) (Norm.norm.{0} f))" with
    | .ok parsedType => pure parsedType
    | .error error => throwError error
  let expected ← Term.elabType parsedType
  Term.synthesizeSyntheticMVarsNoPostponing
  let expected ← instantiateMVars expected
  if expected.hasMVar || expected.hasLevelMVar then
    throwError "unresolved metavariables in frozen type for {info.name}"
  let actual := info.type.instantiateLevelParams info.levelParams levels
  if actual.hasMVar || actual.hasLevelMVar then
    throwError "metavariables in actual constant type for {info.name}"
  unless (← isProp actual) == (← isProp expected) do
    throwError "frozen Prop status mismatch for {info.name}"
  unless ← isDefEq actual expected do
    throwError "frozen type mismatch for {info.name}: actual {actual}, expected {expected}"
  logInfo "FROZEN_CONTRACT_OK: Poincare.ParabolicHolderMultiplier.error_small"
run_cmd liftTermElabM do
  let info ← getConstInfo "Poincare.ParabolicHolderMultiplier.eval_norm_le".toName
  unless info.levelParams.map Name.toString == [] do
    throwError "frozen universe parameter names mismatch for {info.name}"
  unless (← isProp info.type) == true do
    throwError "original Prop status mismatch for {info.name}"
  let levels : List Level := []
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "∀ (A : ContinuousLinearMap.{0, 0, 0, 0} (RingHom.id.{0} Real) (Poincare.ClosedSmoothModel (OfNat.ofNat.{0} (nat_lit 3))) (ContinuousLinearMap.{0, 0, 0, 0} (RingHom.id.{0} Real) (Poincare.ClosedSmoothModel (OfNat.ofNat.{0} (nat_lit 3))) Real)) {v w : Poincare.ClosedSmoothModel (OfNat.ofNat.{0} (nat_lit 3))}, Eq.{1} (Norm.norm.{0} v) (OfNat.ofNat.{0} (nat_lit 1)) → Eq.{1} (Norm.norm.{0} w) (OfNat.ofNat.{0} (nat_lit 1)) → LE.le.{0} (Norm.norm.{0} (DFunLike.coe.{1, 1, 1} (DFunLike.coe.{1, 1, 1} A v) w)) (Norm.norm.{0} A)" with
    | .ok parsedType => pure parsedType
    | .error error => throwError error
  let expected ← Term.elabType parsedType
  Term.synthesizeSyntheticMVarsNoPostponing
  let expected ← instantiateMVars expected
  if expected.hasMVar || expected.hasLevelMVar then
    throwError "unresolved metavariables in frozen type for {info.name}"
  let actual := info.type.instantiateLevelParams info.levelParams levels
  if actual.hasMVar || actual.hasLevelMVar then
    throwError "metavariables in actual constant type for {info.name}"
  unless (← isProp actual) == (← isProp expected) do
    throwError "frozen Prop status mismatch for {info.name}"
  unless ← isDefEq actual expected do
    throwError "frozen type mismatch for {info.name}: actual {actual}, expected {expected}"
  logInfo "FROZEN_CONTRACT_OK: Poincare.ParabolicHolderMultiplier.eval_norm_le"
run_cmd liftTermElabM do
  let info ← getConstInfo "Poincare.ParabolicHolderMultiplier.forcing".toName
  unless info.levelParams.map Name.toString == [] do
    throwError "frozen universe parameter names mismatch for {info.name}"
  unless (← isProp info.type) == false do
    throwError "original Prop status mismatch for {info.name}"
  let levels : List Level := []
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "{α T : Real} → (Fin (OfNat.ofNat.{0} (nat_lit 3)) → Fin (OfNat.ofNat.{0} (nat_lit 3)) → Poincare.ParabolicHolder.Y.{0, 0} (E := Poincare.ClosedSmoothModel (3 : Nat)) α T Real) → Poincare.ParabolicSolutionGraph.Graph.{0} (E := Poincare.ClosedSmoothModel (3 : Nat)) α T → Poincare.ParabolicHolder.Y.{0, 0} (E := Poincare.ClosedSmoothModel (3 : Nat)) α T Real" with
    | .ok parsedType => pure parsedType
    | .error error => throwError error
  let expected ← Term.elabType parsedType
  Term.synthesizeSyntheticMVarsNoPostponing
  let expected ← instantiateMVars expected
  if expected.hasMVar || expected.hasLevelMVar then
    throwError "unresolved metavariables in frozen type for {info.name}"
  let actual := info.type.instantiateLevelParams info.levelParams levels
  if actual.hasMVar || actual.hasLevelMVar then
    throwError "metavariables in actual constant type for {info.name}"
  unless (← isProp actual) == (← isProp expected) do
    throwError "frozen Prop status mismatch for {info.name}"
  unless ← isDefEq actual expected do
    throwError "frozen type mismatch for {info.name}: actual {actual}, expected {expected}"
  logInfo "FROZEN_CONTRACT_OK: Poincare.ParabolicHolderMultiplier.forcing"
run_cmd liftTermElabM do
  let info ← getConstInfo "Poincare.ParabolicHolderMultiplier.forcing._proof_1".toName
  unless info.levelParams.map Name.toString == [] do
    throwError "frozen universe parameter names mismatch for {info.name}"
  unless (← isProp info.type) == true do
    throwError "original Prop status mismatch for {info.name}"
  let levels : List Level := []
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "∀ (i : Prod.{0, 0} Real (Poincare.ClosedSmoothModel (OfNat.ofNat.{0} (nat_lit 3)))), IsBoundedSMul.{0, 0} Real Real" with
    | .ok parsedType => pure parsedType
    | .error error => throwError error
  let expected ← Term.elabType parsedType
  Term.synthesizeSyntheticMVarsNoPostponing
  let expected ← instantiateMVars expected
  if expected.hasMVar || expected.hasLevelMVar then
    throwError "unresolved metavariables in frozen type for {info.name}"
  let actual := info.type.instantiateLevelParams info.levelParams levels
  if actual.hasMVar || actual.hasLevelMVar then
    throwError "metavariables in actual constant type for {info.name}"
  unless (← isProp actual) == (← isProp expected) do
    throwError "frozen Prop status mismatch for {info.name}"
  unless ← isDefEq actual expected do
    throwError "frozen type mismatch for {info.name}: actual {actual}, expected {expected}"
  logInfo "FROZEN_CONTRACT_OK: Poincare.ParabolicHolderMultiplier.forcing._proof_1"
run_cmd liftTermElabM do
  let info ← getConstInfo "Poincare.ParabolicHolderMultiplier.forcing._proof_10".toName
  unless info.levelParams.map Name.toString == [] do
    throwError "frozen universe parameter names mismatch for {info.name}"
  unless (← isProp info.type) == true do
    throwError "original Prop status mismatch for {info.name}"
  let levels : List Level := []
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "∀ {α T : Real} (b : Fin (OfNat.ofNat.{0} (nat_lit 3)) → Fin (OfNat.ofNat.{0} (nat_lit 3)) → Poincare.ParabolicHolder.Y.{0, 0} (E := Poincare.ClosedSmoothModel (3 : Nat)) α T Real) (G : Poincare.ParabolicSolutionGraph.Graph.{0} (E := Poincare.ClosedSmoothModel (3 : Nat)) α T) (p : Prod.{0, 0} Real (Poincare.ClosedSmoothModel (OfNat.ofNat.{0} (nat_lit 3)))), Eq.{1} (Subtype.val.{1} (WithLp.fst.{0, 0} (Subtype.val.{1} (∑ i : Fin (OfNat.ofNat.{0} (nat_lit 3)), ∑ j : Fin (OfNat.ofNat.{0} (nat_lit 3)), HMul.hMul.{0, 0, 0} (b i j) (Poincare.ParabolicHolderMultiplier.entry (Poincare.ParabolicSolutionGraph.Graph.ddu.{0} G) (DFunLike.coe.{1, 1, 1} (EuclideanSpace.basisFun.{0, 0} (Fin (OfNat.ofNat.{0} (nat_lit 3))) Real) i) (DFunLike.coe.{1, 1, 1} (EuclideanSpace.basisFun.{0, 0} (Fin (OfNat.ofNat.{0} (nat_lit 3))) Real) j) (Poincare.ParabolicHolderMultiplier.forcing._proof_3 i) (Poincare.ParabolicHolderMultiplier.forcing._proof_3 j))))) p) (∑ i : Fin (OfNat.ofNat.{0} (nat_lit 3)), ∑ j : Fin (OfNat.ofNat.{0} (nat_lit 3)), HMul.hMul.{0, 0, 0} (Subtype.val.{1} (WithLp.fst.{0, 0} (Subtype.val.{1} (b i j))) p) (DFunLike.coe.{1, 1, 1} (DFunLike.coe.{1, 1, 1} (Subtype.val.{1} (WithLp.fst.{0, 0} (Subtype.val.{1} (Poincare.ParabolicSolutionGraph.Graph.ddu.{0} G))) p) (DFunLike.coe.{1, 1, 1} (EuclideanSpace.basisFun.{0, 0} (Fin (OfNat.ofNat.{0} (nat_lit 3))) Real) i)) (DFunLike.coe.{1, 1, 1} (EuclideanSpace.basisFun.{0, 0} (Fin (OfNat.ofNat.{0} (nat_lit 3))) Real) j)))" with
    | .ok parsedType => pure parsedType
    | .error error => throwError error
  let expected ← Term.elabType parsedType
  Term.synthesizeSyntheticMVarsNoPostponing
  let expected ← instantiateMVars expected
  if expected.hasMVar || expected.hasLevelMVar then
    throwError "unresolved metavariables in frozen type for {info.name}"
  let actual := info.type.instantiateLevelParams info.levelParams levels
  if actual.hasMVar || actual.hasLevelMVar then
    throwError "metavariables in actual constant type for {info.name}"
  unless (← isProp actual) == (← isProp expected) do
    throwError "frozen Prop status mismatch for {info.name}"
  unless ← isDefEq actual expected do
    throwError "frozen type mismatch for {info.name}: actual {actual}, expected {expected}"
  logInfo "FROZEN_CONTRACT_OK: Poincare.ParabolicHolderMultiplier.forcing._proof_10"
run_cmd liftTermElabM do
  let info ← getConstInfo "Poincare.ParabolicHolderMultiplier.forcing._proof_11".toName
  unless info.levelParams.map Name.toString == [] do
    throwError "frozen universe parameter names mismatch for {info.name}"
  unless (← isProp info.type) == true do
    throwError "original Prop status mismatch for {info.name}"
  let levels : List Level := []
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "∀ {α T : Real} (b : Fin (OfNat.ofNat.{0} (nat_lit 3)) → Fin (OfNat.ofNat.{0} (nat_lit 3)) → Poincare.ParabolicHolder.Y.{0, 0} (E := Poincare.ClosedSmoothModel (3 : Nat)) α T Real) (G : Poincare.ParabolicSolutionGraph.Graph.{0} (E := Poincare.ClosedSmoothModel (3 : Nat)) α T), (∀ (p : Prod.{0, 0} Real (Poincare.ClosedSmoothModel (OfNat.ofNat.{0} (nat_lit 3)))), Eq.{1} (Subtype.val.{1} (WithLp.fst.{0, 0} (Subtype.val.{1} (∑ i : Fin (OfNat.ofNat.{0} (nat_lit 3)), ∑ j : Fin (OfNat.ofNat.{0} (nat_lit 3)), HMul.hMul.{0, 0, 0} (b i j) (Poincare.ParabolicHolderMultiplier.entry (Poincare.ParabolicSolutionGraph.Graph.ddu.{0} G) (DFunLike.coe.{1, 1, 1} (EuclideanSpace.basisFun.{0, 0} (Fin (OfNat.ofNat.{0} (nat_lit 3))) Real) i) (DFunLike.coe.{1, 1, 1} (EuclideanSpace.basisFun.{0, 0} (Fin (OfNat.ofNat.{0} (nat_lit 3))) Real) j) (Poincare.ParabolicHolderMultiplier.forcing._proof_3 i) (Poincare.ParabolicHolderMultiplier.forcing._proof_3 j))))) p) (∑ i : Fin (OfNat.ofNat.{0} (nat_lit 3)), ∑ j : Fin (OfNat.ofNat.{0} (nat_lit 3)), HMul.hMul.{0, 0, 0} (Subtype.val.{1} (WithLp.fst.{0, 0} (Subtype.val.{1} (b i j))) p) (DFunLike.coe.{1, 1, 1} (DFunLike.coe.{1, 1, 1} (Subtype.val.{1} (WithLp.fst.{0, 0} (Subtype.val.{1} (Poincare.ParabolicSolutionGraph.Graph.ddu.{0} G))) p) (DFunLike.coe.{1, 1, 1} (EuclideanSpace.basisFun.{0, 0} (Fin (OfNat.ofNat.{0} (nat_lit 3))) Real) i)) (DFunLike.coe.{1, 1, 1} (EuclideanSpace.basisFun.{0, 0} (Fin (OfNat.ofNat.{0} (nat_lit 3))) Real) j)))) → ∀ p ∉ Poincare.ParabolicHolder.cylinder.{0} (E := Poincare.ClosedSmoothModel (3 : Nat)) T, Eq.{1} (∑ i : Fin (OfNat.ofNat.{0} (nat_lit 3)), ∑ j : Fin (OfNat.ofNat.{0} (nat_lit 3)), HMul.hMul.{0, 0, 0} (Subtype.val.{1} (WithLp.fst.{0, 0} (Subtype.val.{1} (b i j))) p) (DFunLike.coe.{1, 1, 1} (DFunLike.coe.{1, 1, 1} (Subtype.val.{1} (WithLp.fst.{0, 0} (Subtype.val.{1} (Poincare.ParabolicSolutionGraph.Graph.ddu.{0} G))) p) (DFunLike.coe.{1, 1, 1} (EuclideanSpace.basisFun.{0, 0} (Fin (OfNat.ofNat.{0} (nat_lit 3))) Real) i)) (DFunLike.coe.{1, 1, 1} (EuclideanSpace.basisFun.{0, 0} (Fin (OfNat.ofNat.{0} (nat_lit 3))) Real) j))) (OfNat.ofNat.{0} (nat_lit 0))" with
    | .ok parsedType => pure parsedType
    | .error error => throwError error
  let expected ← Term.elabType parsedType
  Term.synthesizeSyntheticMVarsNoPostponing
  let expected ← instantiateMVars expected
  if expected.hasMVar || expected.hasLevelMVar then
    throwError "unresolved metavariables in frozen type for {info.name}"
  let actual := info.type.instantiateLevelParams info.levelParams levels
  if actual.hasMVar || actual.hasLevelMVar then
    throwError "metavariables in actual constant type for {info.name}"
  unless (← isProp actual) == (← isProp expected) do
    throwError "frozen Prop status mismatch for {info.name}"
  unless ← isDefEq actual expected do
    throwError "frozen type mismatch for {info.name}: actual {actual}, expected {expected}"
  logInfo "FROZEN_CONTRACT_OK: Poincare.ParabolicHolderMultiplier.forcing._proof_11"
run_cmd liftTermElabM do
  let info ← getConstInfo "Poincare.ParabolicHolderMultiplier.forcing._proof_12".toName
  unless info.levelParams.map Name.toString == [] do
    throwError "frozen universe parameter names mismatch for {info.name}"
  unless (← isProp info.type) == true do
    throwError "original Prop status mismatch for {info.name}"
  let levels : List Level := []
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "∀ {α T : Real} (b : Fin (OfNat.ofNat.{0} (nat_lit 3)) → Fin (OfNat.ofNat.{0} (nat_lit 3)) → Poincare.ParabolicHolder.Y.{0, 0} (E := Poincare.ClosedSmoothModel (3 : Nat)) α T Real) (G : Poincare.ParabolicSolutionGraph.Graph.{0} (E := Poincare.ClosedSmoothModel (3 : Nat)) α T), (∀ (p : Prod.{0, 0} Real (Poincare.ClosedSmoothModel (OfNat.ofNat.{0} (nat_lit 3)))), Eq.{1} (Subtype.val.{1} (WithLp.fst.{0, 0} (Subtype.val.{1} (∑ i : Fin (OfNat.ofNat.{0} (nat_lit 3)), ∑ j : Fin (OfNat.ofNat.{0} (nat_lit 3)), HMul.hMul.{0, 0, 0} (b i j) (Poincare.ParabolicHolderMultiplier.entry (Poincare.ParabolicSolutionGraph.Graph.ddu.{0} G) (DFunLike.coe.{1, 1, 1} (EuclideanSpace.basisFun.{0, 0} (Fin (OfNat.ofNat.{0} (nat_lit 3))) Real) i) (DFunLike.coe.{1, 1, 1} (EuclideanSpace.basisFun.{0, 0} (Fin (OfNat.ofNat.{0} (nat_lit 3))) Real) j) (Poincare.ParabolicHolderMultiplier.forcing._proof_3 i) (Poincare.ParabolicHolderMultiplier.forcing._proof_3 j))))) p) (∑ i : Fin (OfNat.ofNat.{0} (nat_lit 3)), ∑ j : Fin (OfNat.ofNat.{0} (nat_lit 3)), HMul.hMul.{0, 0, 0} (Subtype.val.{1} (WithLp.fst.{0, 0} (Subtype.val.{1} (b i j))) p) (DFunLike.coe.{1, 1, 1} (DFunLike.coe.{1, 1, 1} (Subtype.val.{1} (WithLp.fst.{0, 0} (Subtype.val.{1} (Poincare.ParabolicSolutionGraph.Graph.ddu.{0} G))) p) (DFunLike.coe.{1, 1, 1} (EuclideanSpace.basisFun.{0, 0} (Fin (OfNat.ofNat.{0} (nat_lit 3))) Real) i)) (DFunLike.coe.{1, 1, 1} (EuclideanSpace.basisFun.{0, 0} (Fin (OfNat.ofNat.{0} (nat_lit 3))) Real) j)))) → ∃ (M : Real), ∀ (p : Prod.{0, 0} Real (Poincare.ClosedSmoothModel (OfNat.ofNat.{0} (nat_lit 3)))), Membership.mem.{0, 0} (Poincare.ParabolicHolder.cylinder.{0} (E := Poincare.ClosedSmoothModel (3 : Nat)) T) p → LE.le.{0} (Norm.norm.{0} (∑ i : Fin (OfNat.ofNat.{0} (nat_lit 3)), ∑ j : Fin (OfNat.ofNat.{0} (nat_lit 3)), HMul.hMul.{0, 0, 0} (Subtype.val.{1} (WithLp.fst.{0, 0} (Subtype.val.{1} (b i j))) p) (DFunLike.coe.{1, 1, 1} (DFunLike.coe.{1, 1, 1} (Subtype.val.{1} (WithLp.fst.{0, 0} (Subtype.val.{1} (Poincare.ParabolicSolutionGraph.Graph.ddu.{0} G))) p) (DFunLike.coe.{1, 1, 1} (EuclideanSpace.basisFun.{0, 0} (Fin (OfNat.ofNat.{0} (nat_lit 3))) Real) i)) (DFunLike.coe.{1, 1, 1} (EuclideanSpace.basisFun.{0, 0} (Fin (OfNat.ofNat.{0} (nat_lit 3))) Real) j)))) M" with
    | .ok parsedType => pure parsedType
    | .error error => throwError error
  let expected ← Term.elabType parsedType
  Term.synthesizeSyntheticMVarsNoPostponing
  let expected ← instantiateMVars expected
  if expected.hasMVar || expected.hasLevelMVar then
    throwError "unresolved metavariables in frozen type for {info.name}"
  let actual := info.type.instantiateLevelParams info.levelParams levels
  if actual.hasMVar || actual.hasLevelMVar then
    throwError "metavariables in actual constant type for {info.name}"
  unless (← isProp actual) == (← isProp expected) do
    throwError "frozen Prop status mismatch for {info.name}"
  unless ← isDefEq actual expected do
    throwError "frozen type mismatch for {info.name}: actual {actual}, expected {expected}"
  logInfo "FROZEN_CONTRACT_OK: Poincare.ParabolicHolderMultiplier.forcing._proof_12"
run_cmd liftTermElabM do
  let info ← getConstInfo "Poincare.ParabolicHolderMultiplier.forcing._proof_13".toName
  unless info.levelParams.map Name.toString == [] do
    throwError "frozen universe parameter names mismatch for {info.name}"
  unless (← isProp info.type) == true do
    throwError "original Prop status mismatch for {info.name}"
  let levels : List Level := []
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "∀ {α T : Real} (b : Fin (OfNat.ofNat.{0} (nat_lit 3)) → Fin (OfNat.ofNat.{0} (nat_lit 3)) → Poincare.ParabolicHolder.Y.{0, 0} (E := Poincare.ClosedSmoothModel (3 : Nat)) α T Real) (G : Poincare.ParabolicSolutionGraph.Graph.{0} (E := Poincare.ClosedSmoothModel (3 : Nat)) α T), (∀ (p : Prod.{0, 0} Real (Poincare.ClosedSmoothModel (OfNat.ofNat.{0} (nat_lit 3)))), Eq.{1} (Subtype.val.{1} (WithLp.fst.{0, 0} (Subtype.val.{1} (∑ i : Fin (OfNat.ofNat.{0} (nat_lit 3)), ∑ j : Fin (OfNat.ofNat.{0} (nat_lit 3)), HMul.hMul.{0, 0, 0} (b i j) (Poincare.ParabolicHolderMultiplier.entry (Poincare.ParabolicSolutionGraph.Graph.ddu.{0} G) (DFunLike.coe.{1, 1, 1} (EuclideanSpace.basisFun.{0, 0} (Fin (OfNat.ofNat.{0} (nat_lit 3))) Real) i) (DFunLike.coe.{1, 1, 1} (EuclideanSpace.basisFun.{0, 0} (Fin (OfNat.ofNat.{0} (nat_lit 3))) Real) j) (Poincare.ParabolicHolderMultiplier.forcing._proof_3 i) (Poincare.ParabolicHolderMultiplier.forcing._proof_3 j))))) p) (∑ i : Fin (OfNat.ofNat.{0} (nat_lit 3)), ∑ j : Fin (OfNat.ofNat.{0} (nat_lit 3)), HMul.hMul.{0, 0, 0} (Subtype.val.{1} (WithLp.fst.{0, 0} (Subtype.val.{1} (b i j))) p) (DFunLike.coe.{1, 1, 1} (DFunLike.coe.{1, 1, 1} (Subtype.val.{1} (WithLp.fst.{0, 0} (Subtype.val.{1} (Poincare.ParabolicSolutionGraph.Graph.ddu.{0} G))) p) (DFunLike.coe.{1, 1, 1} (EuclideanSpace.basisFun.{0, 0} (Fin (OfNat.ofNat.{0} (nat_lit 3))) Real) i)) (DFunLike.coe.{1, 1, 1} (EuclideanSpace.basisFun.{0, 0} (Fin (OfNat.ofNat.{0} (nat_lit 3))) Real) j)))) → ∃ (K : Real), Poincare.ParabolicHolder.HasHolderBound.{0, 0} α (Poincare.ParabolicHolder.cylinder.{0} (E := Poincare.ClosedSmoothModel (3 : Nat)) T) (fun (p : Prod.{0, 0} Real (Poincare.ClosedSmoothModel (OfNat.ofNat.{0} (nat_lit 3)))) => ∑ i : Fin (OfNat.ofNat.{0} (nat_lit 3)), ∑ j : Fin (OfNat.ofNat.{0} (nat_lit 3)), HMul.hMul.{0, 0, 0} (Subtype.val.{1} (WithLp.fst.{0, 0} (Subtype.val.{1} (b i j))) p) (DFunLike.coe.{1, 1, 1} (DFunLike.coe.{1, 1, 1} (Subtype.val.{1} (WithLp.fst.{0, 0} (Subtype.val.{1} (Poincare.ParabolicSolutionGraph.Graph.ddu.{0} G))) p) (DFunLike.coe.{1, 1, 1} (EuclideanSpace.basisFun.{0, 0} (Fin (OfNat.ofNat.{0} (nat_lit 3))) Real) i)) (DFunLike.coe.{1, 1, 1} (EuclideanSpace.basisFun.{0, 0} (Fin (OfNat.ofNat.{0} (nat_lit 3))) Real) j))) K" with
    | .ok parsedType => pure parsedType
    | .error error => throwError error
  let expected ← Term.elabType parsedType
  Term.synthesizeSyntheticMVarsNoPostponing
  let expected ← instantiateMVars expected
  if expected.hasMVar || expected.hasLevelMVar then
    throwError "unresolved metavariables in frozen type for {info.name}"
  let actual := info.type.instantiateLevelParams info.levelParams levels
  if actual.hasMVar || actual.hasLevelMVar then
    throwError "metavariables in actual constant type for {info.name}"
  unless (← isProp actual) == (← isProp expected) do
    throwError "frozen Prop status mismatch for {info.name}"
  unless ← isDefEq actual expected do
    throwError "frozen type mismatch for {info.name}: actual {actual}, expected {expected}"
  logInfo "FROZEN_CONTRACT_OK: Poincare.ParabolicHolderMultiplier.forcing._proof_13"
run_cmd liftTermElabM do
  let info ← getConstInfo "Poincare.ParabolicHolderMultiplier.forcing._proof_2".toName
  unless info.levelParams.map Name.toString == [] do
    throwError "frozen universe parameter names mismatch for {info.name}"
  unless (← isProp info.type) == true do
    throwError "original Prop status mismatch for {info.name}"
  let levels : List Level := []
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "∀ {T : Real} (i : Poincare.ParabolicHolder.Pairs.{0} (Poincare.ParabolicHolder.cylinder.{0} (E := Poincare.ClosedSmoothModel (3 : Nat)) T)), IsBoundedSMul.{0, 0} Real Real" with
    | .ok parsedType => pure parsedType
    | .error error => throwError error
  let expected ← Term.elabType parsedType
  Term.synthesizeSyntheticMVarsNoPostponing
  let expected ← instantiateMVars expected
  if expected.hasMVar || expected.hasLevelMVar then
    throwError "unresolved metavariables in frozen type for {info.name}"
  let actual := info.type.instantiateLevelParams info.levelParams levels
  if actual.hasMVar || actual.hasLevelMVar then
    throwError "metavariables in actual constant type for {info.name}"
  unless (← isProp actual) == (← isProp expected) do
    throwError "frozen Prop status mismatch for {info.name}"
  unless ← isDefEq actual expected do
    throwError "frozen type mismatch for {info.name}: actual {actual}, expected {expected}"
  logInfo "FROZEN_CONTRACT_OK: Poincare.ParabolicHolderMultiplier.forcing._proof_2"
run_cmd liftTermElabM do
  let info ← getConstInfo "Poincare.ParabolicHolderMultiplier.forcing._proof_3".toName
  unless info.levelParams.map Name.toString == [] do
    throwError "frozen universe parameter names mismatch for {info.name}"
  unless (← isProp info.type) == true do
    throwError "original Prop status mismatch for {info.name}"
  let levels : List Level := []
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "∀ (i : Fin (OfNat.ofNat.{0} (nat_lit 3))), Eq.{1} (Norm.norm.{0} (DFunLike.coe.{1, 1, 1} (EuclideanSpace.basisFun.{0, 0} (Fin (OfNat.ofNat.{0} (nat_lit 3))) Real) i)) (OfNat.ofNat.{0} (nat_lit 1))" with
    | .ok parsedType => pure parsedType
    | .error error => throwError error
  let expected ← Term.elabType parsedType
  Term.synthesizeSyntheticMVarsNoPostponing
  let expected ← instantiateMVars expected
  if expected.hasMVar || expected.hasLevelMVar then
    throwError "unresolved metavariables in frozen type for {info.name}"
  let actual := info.type.instantiateLevelParams info.levelParams levels
  if actual.hasMVar || actual.hasLevelMVar then
    throwError "metavariables in actual constant type for {info.name}"
  unless (← isProp actual) == (← isProp expected) do
    throwError "frozen Prop status mismatch for {info.name}"
  unless ← isDefEq actual expected do
    throwError "frozen type mismatch for {info.name}: actual {actual}, expected {expected}"
  logInfo "FROZEN_CONTRACT_OK: Poincare.ParabolicHolderMultiplier.forcing._proof_3"
run_cmd liftTermElabM do
  let info ← getConstInfo "Poincare.ParabolicHolderMultiplier.forcing._proof_4".toName
  unless info.levelParams.map Name.toString == [] do
    throwError "frozen universe parameter names mismatch for {info.name}"
  unless (← isProp info.type) == true do
    throwError "original Prop status mismatch for {info.name}"
  let levels : List Level := []
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "SMulCommClass.{0, 0, 0} Real Real Real" with
    | .ok parsedType => pure parsedType
    | .error error => throwError error
  let expected ← Term.elabType parsedType
  Term.synthesizeSyntheticMVarsNoPostponing
  let expected ← instantiateMVars expected
  if expected.hasMVar || expected.hasLevelMVar then
    throwError "unresolved metavariables in frozen type for {info.name}"
  let actual := info.type.instantiateLevelParams info.levelParams levels
  if actual.hasMVar || actual.hasLevelMVar then
    throwError "metavariables in actual constant type for {info.name}"
  unless (← isProp actual) == (← isProp expected) do
    throwError "frozen Prop status mismatch for {info.name}"
  unless ← isDefEq actual expected do
    throwError "frozen type mismatch for {info.name}: actual {actual}, expected {expected}"
  logInfo "FROZEN_CONTRACT_OK: Poincare.ParabolicHolderMultiplier.forcing._proof_4"
run_cmd liftTermElabM do
  let info ← getConstInfo "Poincare.ParabolicHolderMultiplier.forcing._proof_5".toName
  unless info.levelParams.map Name.toString == [] do
    throwError "frozen universe parameter names mismatch for {info.name}"
  unless (← isProp info.type) == true do
    throwError "original Prop status mismatch for {info.name}"
  let levels : List Level := []
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "ContinuousConstSMul.{0, 0} Real Real" with
    | .ok parsedType => pure parsedType
    | .error error => throwError error
  let expected ← Term.elabType parsedType
  Term.synthesizeSyntheticMVarsNoPostponing
  let expected ← instantiateMVars expected
  if expected.hasMVar || expected.hasLevelMVar then
    throwError "unresolved metavariables in frozen type for {info.name}"
  let actual := info.type.instantiateLevelParams info.levelParams levels
  if actual.hasMVar || actual.hasLevelMVar then
    throwError "metavariables in actual constant type for {info.name}"
  unless (← isProp actual) == (← isProp expected) do
    throwError "frozen Prop status mismatch for {info.name}"
  unless ← isDefEq actual expected do
    throwError "frozen type mismatch for {info.name}: actual {actual}, expected {expected}"
  logInfo "FROZEN_CONTRACT_OK: Poincare.ParabolicHolderMultiplier.forcing._proof_5"
run_cmd liftTermElabM do
  let info ← getConstInfo "Poincare.ParabolicHolderMultiplier.forcing._proof_6".toName
  unless info.levelParams.map Name.toString == [] do
    throwError "frozen universe parameter names mismatch for {info.name}"
  unless (← isProp info.type) == true do
    throwError "original Prop status mismatch for {info.name}"
  let levels : List Level := []
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "ContinuousConstSMul.{0, 0} Real Real" with
    | .ok parsedType => pure parsedType
    | .error error => throwError error
  let expected ← Term.elabType parsedType
  Term.synthesizeSyntheticMVarsNoPostponing
  let expected ← instantiateMVars expected
  if expected.hasMVar || expected.hasLevelMVar then
    throwError "unresolved metavariables in frozen type for {info.name}"
  let actual := info.type.instantiateLevelParams info.levelParams levels
  if actual.hasMVar || actual.hasLevelMVar then
    throwError "metavariables in actual constant type for {info.name}"
  unless (← isProp actual) == (← isProp expected) do
    throwError "frozen Prop status mismatch for {info.name}"
  unless ← isDefEq actual expected do
    throwError "frozen type mismatch for {info.name}: actual {actual}, expected {expected}"
  logInfo "FROZEN_CONTRACT_OK: Poincare.ParabolicHolderMultiplier.forcing._proof_6"
run_cmd liftTermElabM do
  let info ← getConstInfo "Poincare.ParabolicHolderMultiplier.forcing._proof_7".toName
  unless info.levelParams.map Name.toString == [] do
    throwError "frozen universe parameter names mismatch for {info.name}"
  unless (← isProp info.type) == true do
    throwError "original Prop status mismatch for {info.name}"
  let levels : List Level := []
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "SMulCommClass.{0, 0, 0} Real Real (ContinuousLinearMap.{0, 0, 0, 0} (RingHom.id.{0} Real) (Poincare.ClosedSmoothModel (OfNat.ofNat.{0} (nat_lit 3))) Real)" with
    | .ok parsedType => pure parsedType
    | .error error => throwError error
  let expected ← Term.elabType parsedType
  Term.synthesizeSyntheticMVarsNoPostponing
  let expected ← instantiateMVars expected
  if expected.hasMVar || expected.hasLevelMVar then
    throwError "unresolved metavariables in frozen type for {info.name}"
  let actual := info.type.instantiateLevelParams info.levelParams levels
  if actual.hasMVar || actual.hasLevelMVar then
    throwError "metavariables in actual constant type for {info.name}"
  unless (← isProp actual) == (← isProp expected) do
    throwError "frozen Prop status mismatch for {info.name}"
  unless ← isDefEq actual expected do
    throwError "frozen type mismatch for {info.name}: actual {actual}, expected {expected}"
  logInfo "FROZEN_CONTRACT_OK: Poincare.ParabolicHolderMultiplier.forcing._proof_7"
run_cmd liftTermElabM do
  let info ← getConstInfo "Poincare.ParabolicHolderMultiplier.forcing._proof_8".toName
  unless info.levelParams.map Name.toString == [] do
    throwError "frozen universe parameter names mismatch for {info.name}"
  unless (← isProp info.type) == true do
    throwError "original Prop status mismatch for {info.name}"
  let levels : List Level := []
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "∀ (i : Prod.{0, 0} Real (Poincare.ClosedSmoothModel (OfNat.ofNat.{0} (nat_lit 3)))), IsBoundedSMul.{0, 0} Real (ContinuousLinearMap.{0, 0, 0, 0} (RingHom.id.{0} Real) (Poincare.ClosedSmoothModel (OfNat.ofNat.{0} (nat_lit 3))) (ContinuousLinearMap.{0, 0, 0, 0} (RingHom.id.{0} Real) (Poincare.ClosedSmoothModel (OfNat.ofNat.{0} (nat_lit 3))) Real))" with
    | .ok parsedType => pure parsedType
    | .error error => throwError error
  let expected ← Term.elabType parsedType
  Term.synthesizeSyntheticMVarsNoPostponing
  let expected ← instantiateMVars expected
  if expected.hasMVar || expected.hasLevelMVar then
    throwError "unresolved metavariables in frozen type for {info.name}"
  let actual := info.type.instantiateLevelParams info.levelParams levels
  if actual.hasMVar || actual.hasLevelMVar then
    throwError "metavariables in actual constant type for {info.name}"
  unless (← isProp actual) == (← isProp expected) do
    throwError "frozen Prop status mismatch for {info.name}"
  unless ← isDefEq actual expected do
    throwError "frozen type mismatch for {info.name}: actual {actual}, expected {expected}"
  logInfo "FROZEN_CONTRACT_OK: Poincare.ParabolicHolderMultiplier.forcing._proof_8"
run_cmd liftTermElabM do
  let info ← getConstInfo "Poincare.ParabolicHolderMultiplier.forcing._proof_9".toName
  unless info.levelParams.map Name.toString == [] do
    throwError "frozen universe parameter names mismatch for {info.name}"
  unless (← isProp info.type) == true do
    throwError "original Prop status mismatch for {info.name}"
  let levels : List Level := []
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "∀ {T : Real} (i : Poincare.ParabolicHolder.Pairs.{0} (Poincare.ParabolicHolder.cylinder.{0} (E := Poincare.ClosedSmoothModel (3 : Nat)) T)), IsBoundedSMul.{0, 0} Real (ContinuousLinearMap.{0, 0, 0, 0} (RingHom.id.{0} Real) (Poincare.ClosedSmoothModel (OfNat.ofNat.{0} (nat_lit 3))) (ContinuousLinearMap.{0, 0, 0, 0} (RingHom.id.{0} Real) (Poincare.ClosedSmoothModel (OfNat.ofNat.{0} (nat_lit 3))) Real))" with
    | .ok parsedType => pure parsedType
    | .error error => throwError error
  let expected ← Term.elabType parsedType
  Term.synthesizeSyntheticMVarsNoPostponing
  let expected ← instantiateMVars expected
  if expected.hasMVar || expected.hasLevelMVar then
    throwError "unresolved metavariables in frozen type for {info.name}"
  let actual := info.type.instantiateLevelParams info.levelParams levels
  if actual.hasMVar || actual.hasLevelMVar then
    throwError "metavariables in actual constant type for {info.name}"
  unless (← isProp actual) == (← isProp expected) do
    throwError "frozen Prop status mismatch for {info.name}"
  unless ← isDefEq actual expected do
    throwError "frozen type mismatch for {info.name}: actual {actual}, expected {expected}"
  logInfo "FROZEN_CONTRACT_OK: Poincare.ParabolicHolderMultiplier.forcing._proof_9"
run_cmd liftTermElabM do
  let info ← getConstInfo "Poincare.ParabolicHolderMultiplier.forcing_apply".toName
  unless info.levelParams.map Name.toString == [] do
    throwError "frozen universe parameter names mismatch for {info.name}"
  unless (← isProp info.type) == true do
    throwError "original Prop status mismatch for {info.name}"
  let levels : List Level := []
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "∀ {α T : Real} (b : Fin (OfNat.ofNat.{0} (nat_lit 3)) → Fin (OfNat.ofNat.{0} (nat_lit 3)) → Poincare.ParabolicHolder.Y.{0, 0} (E := Poincare.ClosedSmoothModel (3 : Nat)) α T Real) (G : Poincare.ParabolicSolutionGraph.Graph.{0} (E := Poincare.ClosedSmoothModel (3 : Nat)) α T) (p : Prod.{0, 0} Real (Poincare.ClosedSmoothModel (OfNat.ofNat.{0} (nat_lit 3)))), Eq.{1} (Subtype.val.{1} (WithLp.fst.{0, 0} (Subtype.val.{1} (Poincare.ParabolicHolderMultiplier.forcing b G))) p) (∑ i : Fin (OfNat.ofNat.{0} (nat_lit 3)), ∑ j : Fin (OfNat.ofNat.{0} (nat_lit 3)), HMul.hMul.{0, 0, 0} (Subtype.val.{1} (WithLp.fst.{0, 0} (Subtype.val.{1} (b i j))) p) (DFunLike.coe.{1, 1, 1} (DFunLike.coe.{1, 1, 1} (Subtype.val.{1} (WithLp.fst.{0, 0} (Subtype.val.{1} (Poincare.ParabolicSolutionGraph.Graph.ddu.{0} G))) p) (DFunLike.coe.{1, 1, 1} (EuclideanSpace.basisFun.{0, 0} (Fin (OfNat.ofNat.{0} (nat_lit 3))) Real) i)) (DFunLike.coe.{1, 1, 1} (EuclideanSpace.basisFun.{0, 0} (Fin (OfNat.ofNat.{0} (nat_lit 3))) Real) j)))" with
    | .ok parsedType => pure parsedType
    | .error error => throwError error
  let expected ← Term.elabType parsedType
  Term.synthesizeSyntheticMVarsNoPostponing
  let expected ← instantiateMVars expected
  if expected.hasMVar || expected.hasLevelMVar then
    throwError "unresolved metavariables in frozen type for {info.name}"
  let actual := info.type.instantiateLevelParams info.levelParams levels
  if actual.hasMVar || actual.hasLevelMVar then
    throwError "metavariables in actual constant type for {info.name}"
  unless (← isProp actual) == (← isProp expected) do
    throwError "frozen Prop status mismatch for {info.name}"
  unless ← isDefEq actual expected do
    throwError "frozen type mismatch for {info.name}: actual {actual}, expected {expected}"
  logInfo "FROZEN_CONTRACT_OK: Poincare.ParabolicHolderMultiplier.forcing_apply"
run_cmd liftTermElabM do
  let info ← getConstInfo "Poincare.ParabolicHolderMultiplier.forcing_eq_sum".toName
  unless info.levelParams.map Name.toString == [] do
    throwError "frozen universe parameter names mismatch for {info.name}"
  unless (← isProp info.type) == true do
    throwError "original Prop status mismatch for {info.name}"
  let levels : List Level := []
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "∀ {α T : Real} (b : Fin (OfNat.ofNat.{0} (nat_lit 3)) → Fin (OfNat.ofNat.{0} (nat_lit 3)) → Poincare.ParabolicHolder.Y.{0, 0} (E := Poincare.ClosedSmoothModel (3 : Nat)) α T Real) (G : Poincare.ParabolicSolutionGraph.Graph.{0} (E := Poincare.ClosedSmoothModel (3 : Nat)) α T), Eq.{1} (Poincare.ParabolicHolderMultiplier.forcing b G) (∑ i : Fin (OfNat.ofNat.{0} (nat_lit 3)), ∑ j : Fin (OfNat.ofNat.{0} (nat_lit 3)), HMul.hMul.{0, 0, 0} (b i j) (Poincare.ParabolicHolderMultiplier.entry (Poincare.ParabolicSolutionGraph.Graph.ddu.{0} G) (DFunLike.coe.{1, 1, 1} (EuclideanSpace.basisFun.{0, 0} (Fin (OfNat.ofNat.{0} (nat_lit 3))) Real) i) (DFunLike.coe.{1, 1, 1} (EuclideanSpace.basisFun.{0, 0} (Fin (OfNat.ofNat.{0} (nat_lit 3))) Real) j) (OrthonormalBasis.norm_eq_one.{0, 0, 0} (EuclideanSpace.basisFun.{0, 0} (Fin (OfNat.ofNat.{0} (nat_lit 3))) Real) i) (OrthonormalBasis.norm_eq_one.{0, 0, 0} (EuclideanSpace.basisFun.{0, 0} (Fin (OfNat.ofNat.{0} (nat_lit 3))) Real) j)))" with
    | .ok parsedType => pure parsedType
    | .error error => throwError error
  let expected ← Term.elabType parsedType
  Term.synthesizeSyntheticMVarsNoPostponing
  let expected ← instantiateMVars expected
  if expected.hasMVar || expected.hasLevelMVar then
    throwError "unresolved metavariables in frozen type for {info.name}"
  let actual := info.type.instantiateLevelParams info.levelParams levels
  if actual.hasMVar || actual.hasLevelMVar then
    throwError "metavariables in actual constant type for {info.name}"
  unless (← isProp actual) == (← isProp expected) do
    throwError "frozen Prop status mismatch for {info.name}"
  unless ← isDefEq actual expected do
    throwError "frozen type mismatch for {info.name}: actual {actual}, expected {expected}"
  logInfo "FROZEN_CONTRACT_OK: Poincare.ParabolicHolderMultiplier.forcing_eq_sum"
run_cmd liftTermElabM do
  let info ← getConstInfo "Poincare.ParabolicHolderMultiplier.norm_entry_le".toName
  unless info.levelParams.map Name.toString == [] do
    throwError "frozen universe parameter names mismatch for {info.name}"
  unless (← isProp info.type) == true do
    throwError "original Prop status mismatch for {info.name}"
  let levels : List Level := []
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "∀ {α T : Real} (H : Poincare.ParabolicHolder.Y.{0, 0} (E := Poincare.ClosedSmoothModel (3 : Nat)) α T (ContinuousLinearMap.{0, 0, 0, 0} (RingHom.id.{0} Real) (Poincare.ClosedSmoothModel (OfNat.ofNat.{0} (nat_lit 3))) (ContinuousLinearMap.{0, 0, 0, 0} (RingHom.id.{0} Real) (Poincare.ClosedSmoothModel (OfNat.ofNat.{0} (nat_lit 3))) Real))) (v w : Poincare.ClosedSmoothModel (OfNat.ofNat.{0} (nat_lit 3))) (hv : Eq.{1} (Norm.norm.{0} v) (OfNat.ofNat.{0} (nat_lit 1))) (hw : Eq.{1} (Norm.norm.{0} w) (OfNat.ofNat.{0} (nat_lit 1))), LE.le.{0} (Norm.norm.{0} (Poincare.ParabolicHolderMultiplier.entry H v w hv hw)) (Norm.norm.{0} H)" with
    | .ok parsedType => pure parsedType
    | .error error => throwError error
  let expected ← Term.elabType parsedType
  Term.synthesizeSyntheticMVarsNoPostponing
  let expected ← instantiateMVars expected
  if expected.hasMVar || expected.hasLevelMVar then
    throwError "unresolved metavariables in frozen type for {info.name}"
  let actual := info.type.instantiateLevelParams info.levelParams levels
  if actual.hasMVar || actual.hasLevelMVar then
    throwError "metavariables in actual constant type for {info.name}"
  unless (← isProp actual) == (← isProp expected) do
    throwError "frozen Prop status mismatch for {info.name}"
  unless ← isDefEq actual expected do
    throwError "frozen type mismatch for {info.name}: actual {actual}, expected {expected}"
  logInfo "FROZEN_CONTRACT_OK: Poincare.ParabolicHolderMultiplier.norm_entry_le"
run_cmd liftTermElabM do
  let info ← getConstInfo "Poincare.ParabolicHolderMultiplier.norm_error_le".toName
  unless info.levelParams.map Name.toString == [] do
    throwError "frozen universe parameter names mismatch for {info.name}"
  unless (← isProp info.type) == true do
    throwError "original Prop status mismatch for {info.name}"
  let levels : List Level := []
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "∀ {α T : Real} (b : Fin (OfNat.ofNat.{0} (nat_lit 3)) → Fin (OfNat.ofNat.{0} (nat_lit 3)) → Poincare.ParabolicHolder.Y.{0, 0} (E := Poincare.ClosedSmoothModel (3 : Nat)) α T Real) (S : ContinuousLinearMap.{0, 0, 0, 0} (RingHom.id.{0} Real) (Poincare.ParabolicHolder.Y.{0, 0} (E := Poincare.ClosedSmoothModel (3 : Nat)) α T Real) (Poincare.ParabolicSolutionGraph.Graph.{0} (E := Poincare.ClosedSmoothModel (3 : Nat)) α T)), LT.lt.{0} (OfNat.ofNat.{0} (nat_lit 0)) α → LT.lt.{0} (OfNat.ofNat.{0} (nat_lit 0)) T → ∀ {ε Λ C_S : Real}, (∀ (i j : Fin (OfNat.ofNat.{0} (nat_lit 3))), LE.le.{0} (Poincare.ParabolicHolder.supNorm.{0, 0} (Poincare.ParabolicHolder.cylinder.{0} (E := Poincare.ClosedSmoothModel (3 : Nat)) T) (Subtype.val.{1} (WithLp.fst.{0, 0} (Subtype.val.{1} (b i j))))) ε) → (∀ (i j : Fin (OfNat.ofNat.{0} (nat_lit 3))), LE.le.{0} (Poincare.ParabolicHolder.holderSeminorm.{0, 0} α (Poincare.ParabolicHolder.cylinder.{0} (E := Poincare.ClosedSmoothModel (3 : Nat)) T) (Subtype.val.{1} (WithLp.fst.{0, 0} (Subtype.val.{1} (b i j))))) Λ) → LE.le.{0} (Norm.norm.{0} S) C_S → ∀ (f : Poincare.ParabolicHolder.Y.{0, 0} (E := Poincare.ClosedSmoothModel (3 : Nat)) α T Real), LE.le.{0} (Norm.norm.{0} (Poincare.ParabolicHolderMultiplier.forcing b (DFunLike.coe.{1, 1, 1} S f))) (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (OfNat.ofNat.{0} (nat_lit 9)) C_S) (HAdd.hAdd.{0, 0, 0} ε (HMul.hMul.{0, 0, 0} Λ (HPow.hPow.{0, 0, 0} T (HDiv.hDiv.{0, 0, 0} α (OfNat.ofNat.{0} (nat_lit 2))))))) (Norm.norm.{0} f))" with
    | .ok parsedType => pure parsedType
    | .error error => throwError error
  let expected ← Term.elabType parsedType
  Term.synthesizeSyntheticMVarsNoPostponing
  let expected ← instantiateMVars expected
  if expected.hasMVar || expected.hasLevelMVar then
    throwError "unresolved metavariables in frozen type for {info.name}"
  let actual := info.type.instantiateLevelParams info.levelParams levels
  if actual.hasMVar || actual.hasLevelMVar then
    throwError "metavariables in actual constant type for {info.name}"
  unless (← isProp actual) == (← isProp expected) do
    throwError "frozen Prop status mismatch for {info.name}"
  unless ← isDefEq actual expected do
    throwError "frozen type mismatch for {info.name}: actual {actual}, expected {expected}"
  logInfo "FROZEN_CONTRACT_OK: Poincare.ParabolicHolderMultiplier.norm_error_le"
run_cmd liftTermElabM do
  let info ← getConstInfo "Poincare.ParabolicHolderMultiplier.norm_forcing_le".toName
  unless info.levelParams.map Name.toString == [] do
    throwError "frozen universe parameter names mismatch for {info.name}"
  unless (← isProp info.type) == true do
    throwError "original Prop status mismatch for {info.name}"
  let levels : List Level := []
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "∀ {α T : Real} (b : Fin (OfNat.ofNat.{0} (nat_lit 3)) → Fin (OfNat.ofNat.{0} (nat_lit 3)) → Poincare.ParabolicHolder.Y.{0, 0} (E := Poincare.ClosedSmoothModel (3 : Nat)) α T Real) (G : Poincare.ParabolicSolutionGraph.Graph.{0} (E := Poincare.ClosedSmoothModel (3 : Nat)) α T), LT.lt.{0} (OfNat.ofNat.{0} (nat_lit 0)) α → LT.lt.{0} (OfNat.ofNat.{0} (nat_lit 0)) T → ∀ {ε Λ : Real}, (∀ (i j : Fin (OfNat.ofNat.{0} (nat_lit 3))), LE.le.{0} (Poincare.ParabolicHolder.supNorm.{0, 0} (Poincare.ParabolicHolder.cylinder.{0} (E := Poincare.ClosedSmoothModel (3 : Nat)) T) (Subtype.val.{1} (WithLp.fst.{0, 0} (Subtype.val.{1} (b i j))))) ε) → (∀ (i j : Fin (OfNat.ofNat.{0} (nat_lit 3))), LE.le.{0} (Poincare.ParabolicHolder.holderSeminorm.{0, 0} α (Poincare.ParabolicHolder.cylinder.{0} (E := Poincare.ClosedSmoothModel (3 : Nat)) T) (Subtype.val.{1} (WithLp.fst.{0, 0} (Subtype.val.{1} (b i j))))) Λ) → LE.le.{0} (Norm.norm.{0} (Poincare.ParabolicHolderMultiplier.forcing b G)) (HMul.hMul.{0, 0, 0} (OfNat.ofNat.{0} (nat_lit 9)) (HAdd.hAdd.{0, 0, 0} (HMul.hMul.{0, 0, 0} ε (Norm.norm.{0} G)) (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} Λ (HPow.hPow.{0, 0, 0} T (HDiv.hDiv.{0, 0, 0} α (OfNat.ofNat.{0} (nat_lit 2))))) (Norm.norm.{0} G))))" with
    | .ok parsedType => pure parsedType
    | .error error => throwError error
  let expected ← Term.elabType parsedType
  Term.synthesizeSyntheticMVarsNoPostponing
  let expected ← instantiateMVars expected
  if expected.hasMVar || expected.hasLevelMVar then
    throwError "unresolved metavariables in frozen type for {info.name}"
  let actual := info.type.instantiateLevelParams info.levelParams levels
  if actual.hasMVar || actual.hasLevelMVar then
    throwError "metavariables in actual constant type for {info.name}"
  unless (← isProp actual) == (← isProp expected) do
    throwError "frozen Prop status mismatch for {info.name}"
  unless ← isDefEq actual expected do
    throwError "frozen type mismatch for {info.name}: actual {actual}, expected {expected}"
  logInfo "FROZEN_CONTRACT_OK: Poincare.ParabolicHolderMultiplier.norm_forcing_le"
run_cmd liftTermElabM do
  let info ← getConstInfo "Poincare.ParabolicHolderMultiplier.norm_mul_ddu_entry_le".toName
  unless info.levelParams.map Name.toString == [] do
    throwError "frozen universe parameter names mismatch for {info.name}"
  unless (← isProp info.type) == true do
    throwError "original Prop status mismatch for {info.name}"
  let levels : List Level := []
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "∀ {α T : Real} (b : Poincare.ParabolicHolder.Y.{0, 0} (E := Poincare.ClosedSmoothModel (3 : Nat)) α T Real) (G : Poincare.ParabolicSolutionGraph.Graph.{0} (E := Poincare.ClosedSmoothModel (3 : Nat)) α T), LT.lt.{0} (OfNat.ofNat.{0} (nat_lit 0)) α → LT.lt.{0} (OfNat.ofNat.{0} (nat_lit 0)) T → ∀ {ε Λ : Real}, LE.le.{0} (Poincare.ParabolicHolder.supNorm.{0, 0} (Poincare.ParabolicHolder.cylinder.{0} (E := Poincare.ClosedSmoothModel (3 : Nat)) T) (Subtype.val.{1} (WithLp.fst.{0, 0} (Subtype.val.{1} b)))) ε → LE.le.{0} (Poincare.ParabolicHolder.holderSeminorm.{0, 0} α (Poincare.ParabolicHolder.cylinder.{0} (E := Poincare.ClosedSmoothModel (3 : Nat)) T) (Subtype.val.{1} (WithLp.fst.{0, 0} (Subtype.val.{1} b)))) Λ → ∀ (v w : Poincare.ClosedSmoothModel (OfNat.ofNat.{0} (nat_lit 3))) (hv : Eq.{1} (Norm.norm.{0} v) (OfNat.ofNat.{0} (nat_lit 1))) (hw : Eq.{1} (Norm.norm.{0} w) (OfNat.ofNat.{0} (nat_lit 1))), LE.le.{0} (Norm.norm.{0} (HMul.hMul.{0, 0, 0} b (Poincare.ParabolicHolderMultiplier.entry (Poincare.ParabolicSolutionGraph.Graph.ddu.{0} G) v w hv hw))) (HAdd.hAdd.{0, 0, 0} (HMul.hMul.{0, 0, 0} ε (Norm.norm.{0} G)) (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} Λ (HPow.hPow.{0, 0, 0} T (HDiv.hDiv.{0, 0, 0} α (OfNat.ofNat.{0} (nat_lit 2))))) (Norm.norm.{0} G)))" with
    | .ok parsedType => pure parsedType
    | .error error => throwError error
  let expected ← Term.elabType parsedType
  Term.synthesizeSyntheticMVarsNoPostponing
  let expected ← instantiateMVars expected
  if expected.hasMVar || expected.hasLevelMVar then
    throwError "unresolved metavariables in frozen type for {info.name}"
  let actual := info.type.instantiateLevelParams info.levelParams levels
  if actual.hasMVar || actual.hasLevelMVar then
    throwError "metavariables in actual constant type for {info.name}"
  unless (← isProp actual) == (← isProp expected) do
    throwError "frozen Prop status mismatch for {info.name}"
  unless ← isDefEq actual expected do
    throwError "frozen type mismatch for {info.name}: actual {actual}, expected {expected}"
  logInfo "FROZEN_CONTRACT_OK: Poincare.ParabolicHolderMultiplier.norm_mul_ddu_entry_le"
run_cmd liftTermElabM do
  let info ← getConstInfo "Poincare.ParabolicHolderMultiplier.norm_mul_split".toName
  unless info.levelParams.map Name.toString == [] do
    throwError "frozen universe parameter names mismatch for {info.name}"
  unless (← isProp info.type) == true do
    throwError "original Prop status mismatch for {info.name}"
  let levels : List Level := []
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "∀ {α T : Real} (b h : Poincare.ParabolicHolder.Y.{0, 0} (E := Poincare.ClosedSmoothModel (3 : Nat)) α T Real), LE.le.{0} (Norm.norm.{0} (HMul.hMul.{0, 0, 0} b h)) (HAdd.hAdd.{0, 0, 0} (HMul.hMul.{0, 0, 0} (Poincare.ParabolicHolder.supNorm.{0, 0} (Poincare.ParabolicHolder.cylinder.{0} (E := Poincare.ClosedSmoothModel (3 : Nat)) T) (Subtype.val.{1} (WithLp.fst.{0, 0} (Subtype.val.{1} b)))) (Norm.norm.{0} h)) (HMul.hMul.{0, 0, 0} (Poincare.ParabolicHolder.holderSeminorm.{0, 0} α (Poincare.ParabolicHolder.cylinder.{0} (E := Poincare.ClosedSmoothModel (3 : Nat)) T) (Subtype.val.{1} (WithLp.fst.{0, 0} (Subtype.val.{1} b)))) (Poincare.ParabolicHolder.supNorm.{0, 0} (Poincare.ParabolicHolder.cylinder.{0} (E := Poincare.ClosedSmoothModel (3 : Nat)) T) (Subtype.val.{1} (WithLp.fst.{0, 0} (Subtype.val.{1} h))))))" with
    | .ok parsedType => pure parsedType
    | .error error => throwError error
  let expected ← Term.elabType parsedType
  Term.synthesizeSyntheticMVarsNoPostponing
  let expected ← instantiateMVars expected
  if expected.hasMVar || expected.hasLevelMVar then
    throwError "unresolved metavariables in frozen type for {info.name}"
  let actual := info.type.instantiateLevelParams info.levelParams levels
  if actual.hasMVar || actual.hasLevelMVar then
    throwError "metavariables in actual constant type for {info.name}"
  unless (← isProp actual) == (← isProp expected) do
    throwError "frozen Prop status mismatch for {info.name}"
  unless ← isDefEq actual expected do
    throwError "frozen type mismatch for {info.name}: actual {actual}, expected {expected}"
  logInfo "FROZEN_CONTRACT_OK: Poincare.ParabolicHolderMultiplier.norm_mul_split"
run_cmd liftTermElabM do
  let info ← getConstInfo "Poincare.ParabolicHolderMultiplier.sum_apply".toName
  unless info.levelParams.map Name.toString == ["u_1"] do
    throwError "frozen universe parameter names mismatch for {info.name}"
  unless (← isProp info.type) == true do
    throwError "original Prop status mismatch for {info.name}"
  let levels : List Level := [Level.param "u_1".toName]
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "∀ {α T : Real} {ι : Type u_1} (s : Finset.{u_1} ι) (f : ι → Poincare.ParabolicHolder.Y.{0, 0} (E := Poincare.ClosedSmoothModel (3 : Nat)) α T Real) (p : Prod.{0, 0} Real (Poincare.ClosedSmoothModel (OfNat.ofNat.{0} (nat_lit 3)))), Eq.{1} (Subtype.val.{1} (WithLp.fst.{0, 0} (Subtype.val.{1} (∑ i ∈ s, f i))) p) (∑ i ∈ s, Subtype.val.{1} (WithLp.fst.{0, 0} (Subtype.val.{1} (f i))) p)" with
    | .ok parsedType => pure parsedType
    | .error error => throwError error
  let expected ← Term.elabType parsedType
  Term.synthesizeSyntheticMVarsNoPostponing
  let expected ← instantiateMVars expected
  if expected.hasMVar || expected.hasLevelMVar then
    throwError "unresolved metavariables in frozen type for {info.name}"
  let actual := info.type.instantiateLevelParams info.levelParams levels
  if actual.hasMVar || actual.hasLevelMVar then
    throwError "metavariables in actual constant type for {info.name}"
  unless (← isProp actual) == (← isProp expected) do
    throwError "frozen Prop status mismatch for {info.name}"
  unless ← isDefEq actual expected do
    throwError "frozen type mismatch for {info.name}: actual {actual}, expected {expected}"
  logInfo "FROZEN_CONTRACT_OK: Poincare.ParabolicHolderMultiplier.sum_apply"
run_cmd liftTermElabM do
  let info ← getConstInfo "Poincare.ParabolicHolderMultiplier.supNorm_ddu_le".toName
  unless info.levelParams.map Name.toString == [] do
    throwError "frozen universe parameter names mismatch for {info.name}"
  unless (← isProp info.type) == true do
    throwError "original Prop status mismatch for {info.name}"
  let levels : List Level := []
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "∀ {α T : Real} (G : Poincare.ParabolicSolutionGraph.Graph.{0} (E := Poincare.ClosedSmoothModel (3 : Nat)) α T), LT.lt.{0} (OfNat.ofNat.{0} (nat_lit 0)) α → LT.lt.{0} (OfNat.ofNat.{0} (nat_lit 0)) T → LE.le.{0} (Poincare.ParabolicHolder.supNorm.{0, 0} (Poincare.ParabolicHolder.cylinder.{0} (E := Poincare.ClosedSmoothModel (3 : Nat)) T) (Subtype.val.{1} (WithLp.fst.{0, 0} (Subtype.val.{1} (Poincare.ParabolicSolutionGraph.Graph.ddu.{0} G))))) (HMul.hMul.{0, 0, 0} (HPow.hPow.{0, 0, 0} T (HDiv.hDiv.{0, 0, 0} α (OfNat.ofNat.{0} (nat_lit 2)))) (Norm.norm.{0} G))" with
    | .ok parsedType => pure parsedType
    | .error error => throwError error
  let expected ← Term.elabType parsedType
  Term.synthesizeSyntheticMVarsNoPostponing
  let expected ← instantiateMVars expected
  if expected.hasMVar || expected.hasLevelMVar then
    throwError "unresolved metavariables in frozen type for {info.name}"
  let actual := info.type.instantiateLevelParams info.levelParams levels
  if actual.hasMVar || actual.hasLevelMVar then
    throwError "metavariables in actual constant type for {info.name}"
  unless (← isProp actual) == (← isProp expected) do
    throwError "frozen Prop status mismatch for {info.name}"
  unless ← isDefEq actual expected do
    throwError "frozen type mismatch for {info.name}: actual {actual}, expected {expected}"
  logInfo "FROZEN_CONTRACT_OK: Poincare.ParabolicHolderMultiplier.supNorm_ddu_le"
run_cmd liftTermElabM do
  let info ← getConstInfo "Poincare.ParabolicHolderMultiplier.supNorm_entry_le".toName
  unless info.levelParams.map Name.toString == [] do
    throwError "frozen universe parameter names mismatch for {info.name}"
  unless (← isProp info.type) == true do
    throwError "original Prop status mismatch for {info.name}"
  let levels : List Level := []
  unless info.levelParams.length == levels.length do
    throwError "frozen universe arity mismatch for {info.name}"
  let parsedType ← match Parser.runParserCategory (← getEnv) `term "∀ {α T : Real} (H : Poincare.ParabolicHolder.Y.{0, 0} (E := Poincare.ClosedSmoothModel (3 : Nat)) α T (ContinuousLinearMap.{0, 0, 0, 0} (RingHom.id.{0} Real) (Poincare.ClosedSmoothModel (OfNat.ofNat.{0} (nat_lit 3))) (ContinuousLinearMap.{0, 0, 0, 0} (RingHom.id.{0} Real) (Poincare.ClosedSmoothModel (OfNat.ofNat.{0} (nat_lit 3))) Real))) (v w : Poincare.ClosedSmoothModel (OfNat.ofNat.{0} (nat_lit 3))) (hv : Eq.{1} (Norm.norm.{0} v) (OfNat.ofNat.{0} (nat_lit 1))) (hw : Eq.{1} (Norm.norm.{0} w) (OfNat.ofNat.{0} (nat_lit 1))), LE.le.{0} (Poincare.ParabolicHolder.supNorm.{0, 0} (Poincare.ParabolicHolder.cylinder.{0} (E := Poincare.ClosedSmoothModel (3 : Nat)) T) (Subtype.val.{1} (WithLp.fst.{0, 0} (Subtype.val.{1} (Poincare.ParabolicHolderMultiplier.entry H v w hv hw))))) (Poincare.ParabolicHolder.supNorm.{0, 0} (Poincare.ParabolicHolder.cylinder.{0} (E := Poincare.ClosedSmoothModel (3 : Nat)) T) (Subtype.val.{1} (WithLp.fst.{0, 0} (Subtype.val.{1} H))))" with
    | .ok parsedType => pure parsedType
    | .error error => throwError error
  let expected ← Term.elabType parsedType
  Term.synthesizeSyntheticMVarsNoPostponing
  let expected ← instantiateMVars expected
  if expected.hasMVar || expected.hasLevelMVar then
    throwError "unresolved metavariables in frozen type for {info.name}"
  let actual := info.type.instantiateLevelParams info.levelParams levels
  if actual.hasMVar || actual.hasLevelMVar then
    throwError "metavariables in actual constant type for {info.name}"
  unless (← isProp actual) == (← isProp expected) do
    throwError "frozen Prop status mismatch for {info.name}"
  unless ← isDefEq actual expected do
    throwError "frozen type mismatch for {info.name}: actual {actual}, expected {expected}"
  logInfo "FROZEN_CONTRACT_OK: Poincare.ParabolicHolderMultiplier.supNorm_entry_le"
run_cmd do
  let env ← getEnv
  let mut names : Array Name := #[]
  for (name, _) in env.constants.toList do
    if !isPrivateName name then
      if let some idx := env.getModuleIdxFor? name then
        if env.header.moduleNames[idx]! == `Poincare.Global.ParabolicHolderMultiplier then
          names := names.push name
  names := names.qsort (fun a b => a.toString < b.toString)
  let expected : List Name := ["Poincare.ParabolicHolderMultiplier.ddu_time_bound".toName, "Poincare.ParabolicHolderMultiplier.ddu_zero_trace".toName, "Poincare.ParabolicHolderMultiplier.du_zero_trace".toName, "Poincare.ParabolicHolderMultiplier.entry".toName, "Poincare.ParabolicHolderMultiplier.entry._proof_1".toName, "Poincare.ParabolicHolderMultiplier.entry._proof_10".toName, "Poincare.ParabolicHolderMultiplier.entry._proof_11".toName, "Poincare.ParabolicHolderMultiplier.entry._proof_12".toName, "Poincare.ParabolicHolderMultiplier.entry._proof_13".toName, "Poincare.ParabolicHolderMultiplier.entry._proof_2".toName, "Poincare.ParabolicHolderMultiplier.entry._proof_3".toName, "Poincare.ParabolicHolderMultiplier.entry._proof_4".toName, "Poincare.ParabolicHolderMultiplier.entry._proof_5".toName, "Poincare.ParabolicHolderMultiplier.entry._proof_6".toName, "Poincare.ParabolicHolderMultiplier.entry._proof_7".toName, "Poincare.ParabolicHolderMultiplier.entry._proof_8".toName, "Poincare.ParabolicHolderMultiplier.entry._proof_9".toName, "Poincare.ParabolicHolderMultiplier.entry.congr_simp".toName, "Poincare.ParabolicHolderMultiplier.entry_apply".toName, "Poincare.ParabolicHolderMultiplier.entry_holderBound".toName, "Poincare.ParabolicHolderMultiplier.error_small".toName, "Poincare.ParabolicHolderMultiplier.eval_norm_le".toName, "Poincare.ParabolicHolderMultiplier.forcing".toName, "Poincare.ParabolicHolderMultiplier.forcing._proof_1".toName, "Poincare.ParabolicHolderMultiplier.forcing._proof_10".toName, "Poincare.ParabolicHolderMultiplier.forcing._proof_11".toName, "Poincare.ParabolicHolderMultiplier.forcing._proof_12".toName, "Poincare.ParabolicHolderMultiplier.forcing._proof_13".toName, "Poincare.ParabolicHolderMultiplier.forcing._proof_2".toName, "Poincare.ParabolicHolderMultiplier.forcing._proof_3".toName, "Poincare.ParabolicHolderMultiplier.forcing._proof_4".toName, "Poincare.ParabolicHolderMultiplier.forcing._proof_5".toName, "Poincare.ParabolicHolderMultiplier.forcing._proof_6".toName, "Poincare.ParabolicHolderMultiplier.forcing._proof_7".toName, "Poincare.ParabolicHolderMultiplier.forcing._proof_8".toName, "Poincare.ParabolicHolderMultiplier.forcing._proof_9".toName, "Poincare.ParabolicHolderMultiplier.forcing_apply".toName, "Poincare.ParabolicHolderMultiplier.forcing_eq_sum".toName, "Poincare.ParabolicHolderMultiplier.norm_entry_le".toName, "Poincare.ParabolicHolderMultiplier.norm_error_le".toName, "Poincare.ParabolicHolderMultiplier.norm_forcing_le".toName, "Poincare.ParabolicHolderMultiplier.norm_mul_ddu_entry_le".toName, "Poincare.ParabolicHolderMultiplier.norm_mul_split".toName, "Poincare.ParabolicHolderMultiplier.sum_apply".toName, "Poincare.ParabolicHolderMultiplier.supNorm_ddu_le".toName, "Poincare.ParabolicHolderMultiplier.supNorm_entry_le".toName]
  unless names.toList == expected do
    throwError "frozen public inventory mismatch: actual {names}, expected {expected}"
  logInfo "FROZEN_PUBLIC_INVENTORY_OK: 46 declarations"
