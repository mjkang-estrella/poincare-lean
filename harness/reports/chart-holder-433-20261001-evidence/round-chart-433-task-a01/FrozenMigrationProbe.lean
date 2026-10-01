import Lean
import Poincare.Global.RoundSphereChart
open Lean Elab Command Meta
set_option autoImplicit false
universe u_1
namespace FrozenRoundChartSafety
-- Projection names and computational metadata are explicit closure edges.
def usedConstants (e : Expr) (seen : NameSet := {}) : NameSet :=
  match e with
  | .const n _ => seen.insert n
  | .proj n _ e => usedConstants e (seen.insert n)
  | .app f a => usedConstants a (usedConstants f seen)
  | .lam _ t b _ | .forallE _ t b _ => usedConstants b (usedConstants t seen)
  | .letE _ t v b _ => usedConstants b (usedConstants v (usedConstants t seen))
  | .mdata _ e => usedConstants e seen
  | _ => seen
end FrozenRoundChartSafety
run_cmd liftTermElabM do
  let name := "Poincare.stereoInvFunAuxConformalFactor".toName
  let info ← getConstInfo name
  let levelNames : List Name := ["u_1".toName]
  let levels : List Level := [Level.param "u_1".toName]
  unless info.levelParams == levelNames do
    throwError "frozen universe parameters mismatch for {name}: {info.levelParams}"
  unless info.isTheorem == false do
    throwError "frozen declaration kind mismatch for {name}"
  let parsed ← match Parser.runParserCategory (← getEnv) `term "{E : Type u_1} → [NormedAddCommGroup.{u_1} E] → E → Real" with
    | .ok stx => pure stx
    | .error err => throwError err
  let expected ← Term.elabType parsed
  Term.synthesizeSyntheticMVarsNoPostponing
  let expected ← instantiateMVars expected
  let actual := info.type.instantiateLevelParams info.levelParams levels
  if expected.hasMVar || expected.hasLevelMVar || actual.hasMVar || actual.hasLevelMVar then
    throwError "unresolved metavariables in frozen type for {name}"
  unless (← isProp expected) == false && (← isProp actual) == false do
    throwError "frozen Prop classification mismatch for {name}"
  unless ← isDefEq actual expected do
    throwError "rigid frozen type mismatch for {name}: actual {actual}, expected {expected}"
  logInfo m!"FROZEN_CONTRACT_OK: {name}"
run_cmd liftTermElabM do
  let name := "Poincare.stereoInvFunAuxFDeriv".toName
  let info ← getConstInfo name
  let levelNames : List Name := ["u_1".toName]
  let levels : List Level := [Level.param "u_1".toName]
  unless info.levelParams == levelNames do
    throwError "frozen universe parameters mismatch for {name}: {info.levelParams}"
  unless info.isTheorem == false do
    throwError "frozen declaration kind mismatch for {name}"
  let parsed ← match Parser.runParserCategory (← getEnv) `term "{E : Type u_1} → [inst : NormedAddCommGroup.{u_1} E] → [inst_1 : InnerProductSpace.{0, u_1} Real E] → E → E → ContinuousLinearMap.{0, 0, u_1, u_1} (RingHom.id.{0} Real) E E" with
    | .ok stx => pure stx
    | .error err => throwError err
  let expected ← Term.elabType parsed
  Term.synthesizeSyntheticMVarsNoPostponing
  let expected ← instantiateMVars expected
  let actual := info.type.instantiateLevelParams info.levelParams levels
  if expected.hasMVar || expected.hasLevelMVar || actual.hasMVar || actual.hasLevelMVar then
    throwError "unresolved metavariables in frozen type for {name}"
  unless (← isProp expected) == false && (← isProp actual) == false do
    throwError "frozen Prop classification mismatch for {name}"
  unless ← isDefEq actual expected do
    throwError "rigid frozen type mismatch for {name}: actual {actual}, expected {expected}"
  logInfo m!"FROZEN_CONTRACT_OK: {name}"
run_cmd liftTermElabM do
  let name := "Poincare.stereoInvFunAuxFDeriv_apply".toName
  let info ← getConstInfo name
  let levelNames : List Name := ["u_1".toName]
  let levels : List Level := [Level.param "u_1".toName]
  unless info.levelParams == levelNames do
    throwError "frozen universe parameters mismatch for {name}: {info.levelParams}"
  unless info.isTheorem == true do
    throwError "frozen declaration kind mismatch for {name}"
  let parsed ← match Parser.runParserCategory (← getEnv) `term "∀ {E : Type u_1} [inst : NormedAddCommGroup.{u_1} E] [inst_1 : InnerProductSpace.{0, u_1} Real E] (v z u : E), Eq.{u_1 + 1} ((Poincare.stereoInvFunAuxFDeriv.{u_1} v z) u) (HAdd.hAdd.{u_1, u_1, u_1} (HSub.hSub.{u_1, u_1, u_1} (HSMul.hSMul.{0, u_1, u_1} (HMul.hMul.{0, 0, 0} (4 : Real) (Inv.inv.{0} (HAdd.hAdd.{0, 0, 0} (HPow.hPow.{0, 0, 0} (Norm.norm.{u_1} z) (2 : Nat)) (4 : Real)))) u) (HSMul.hSMul.{0, u_1, u_1} (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (8 : Real) (HPow.hPow.{0, 0, 0} (Inv.inv.{0} (HAdd.hAdd.{0, 0, 0} (HPow.hPow.{0, 0, 0} (Norm.norm.{u_1} z) (2 : Nat)) (4 : Real))) (2 : Nat))) (Inner.inner.{0, u_1} Real z u)) z)) (HSMul.hSMul.{0, u_1, u_1} (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (16 : Real) (HPow.hPow.{0, 0, 0} (Inv.inv.{0} (HAdd.hAdd.{0, 0, 0} (HPow.hPow.{0, 0, 0} (Norm.norm.{u_1} z) (2 : Nat)) (4 : Real))) (2 : Nat))) (Inner.inner.{0, u_1} Real z u)) v))" with
    | .ok stx => pure stx
    | .error err => throwError err
  let expected ← Term.elabType parsed
  Term.synthesizeSyntheticMVarsNoPostponing
  let expected ← instantiateMVars expected
  let actual := info.type.instantiateLevelParams info.levelParams levels
  if expected.hasMVar || expected.hasLevelMVar || actual.hasMVar || actual.hasLevelMVar then
    throwError "unresolved metavariables in frozen type for {name}"
  unless (← isProp expected) == true && (← isProp actual) == true do
    throwError "frozen Prop classification mismatch for {name}"
  unless ← isDefEq actual expected do
    throwError "rigid frozen type mismatch for {name}: actual {actual}, expected {expected}"
  logInfo m!"FROZEN_CONTRACT_OK: {name}"
run_cmd liftTermElabM do
  let name := "Poincare.hasFDerivAt_stereoInvFunAuxFDeriv".toName
  let info ← getConstInfo name
  let levelNames : List Name := ["u_1".toName]
  let levels : List Level := [Level.param "u_1".toName]
  unless info.levelParams == levelNames do
    throwError "frozen universe parameters mismatch for {name}: {info.levelParams}"
  unless info.isTheorem == true do
    throwError "frozen declaration kind mismatch for {name}"
  let parsed ← match Parser.runParserCategory (← getEnv) `term "∀ {E : Type u_1} [inst : NormedAddCommGroup.{u_1} E] [inst_1 : InnerProductSpace.{0, u_1} Real E] (v z : E), HasFDerivAt.{0, u_1, u_1} (stereoInvFunAux.{u_1} v) (Poincare.stereoInvFunAuxFDeriv.{u_1} v z) z" with
    | .ok stx => pure stx
    | .error err => throwError err
  let expected ← Term.elabType parsed
  Term.synthesizeSyntheticMVarsNoPostponing
  let expected ← instantiateMVars expected
  let actual := info.type.instantiateLevelParams info.levelParams levels
  if expected.hasMVar || expected.hasLevelMVar || actual.hasMVar || actual.hasLevelMVar then
    throwError "unresolved metavariables in frozen type for {name}"
  unless (← isProp expected) == true && (← isProp actual) == true do
    throwError "frozen Prop classification mismatch for {name}"
  unless ← isDefEq actual expected do
    throwError "rigid frozen type mismatch for {name}: actual {actual}, expected {expected}"
  logInfo m!"FROZEN_CONTRACT_OK: {name}"
run_cmd liftTermElabM do
  let name := "Poincare.fderiv_stereoInvFunAux".toName
  let info ← getConstInfo name
  let levelNames : List Name := ["u_1".toName]
  let levels : List Level := [Level.param "u_1".toName]
  unless info.levelParams == levelNames do
    throwError "frozen universe parameters mismatch for {name}: {info.levelParams}"
  unless info.isTheorem == true do
    throwError "frozen declaration kind mismatch for {name}"
  let parsed ← match Parser.runParserCategory (← getEnv) `term "∀ {E : Type u_1} [inst : NormedAddCommGroup.{u_1} E] [inst_1 : InnerProductSpace.{0, u_1} Real E] (v z : E), Eq.{u_1 + 1} (fderiv.{0, u_1, u_1} Real (stereoInvFunAux.{u_1} v) z) (Poincare.stereoInvFunAuxFDeriv.{u_1} v z)" with
    | .ok stx => pure stx
    | .error err => throwError err
  let expected ← Term.elabType parsed
  Term.synthesizeSyntheticMVarsNoPostponing
  let expected ← instantiateMVars expected
  let actual := info.type.instantiateLevelParams info.levelParams levels
  if expected.hasMVar || expected.hasLevelMVar || actual.hasMVar || actual.hasLevelMVar then
    throwError "unresolved metavariables in frozen type for {name}"
  unless (← isProp expected) == true && (← isProp actual) == true do
    throwError "frozen Prop classification mismatch for {name}"
  unless ← isDefEq actual expected do
    throwError "rigid frozen type mismatch for {name}: actual {actual}, expected {expected}"
  logInfo m!"FROZEN_CONTRACT_OK: {name}"
run_cmd liftTermElabM do
  let name := "Poincare.fderiv_stereoInvFunAux_comp_subtype".toName
  let info ← getConstInfo name
  let levelNames : List Name := ["u_1".toName]
  let levels : List Level := [Level.param "u_1".toName]
  unless info.levelParams == levelNames do
    throwError "frozen universe parameters mismatch for {name}: {info.levelParams}"
  unless info.isTheorem == true do
    throwError "frozen declaration kind mismatch for {name}"
  let parsed ← match Parser.runParserCategory (← getEnv) `term "∀ {E : Type u_1} [inst : NormedAddCommGroup.{u_1} E] [inst_1 : InnerProductSpace.{0, u_1} Real E] (v : E) (z : ↥(Submodule.orthogonal.{0, u_1} (Submodule.span.{0, u_1} Real (Singleton.singleton.{u_1, u_1} v)))), Eq.{u_1 + 1} (fderiv.{0, u_1, u_1} Real (Function.comp.{u_1 + 1, u_1 + 1, u_1 + 1} (stereoInvFunAux.{u_1} v) Subtype.val.{u_1 + 1}) z) (ContinuousLinearMap.comp.{0, 0, 0, u_1, u_1, u_1} (Poincare.stereoInvFunAuxFDeriv.{u_1} v ↑z) (Submodule.subtypeL.{0, u_1} (Submodule.orthogonal.{0, u_1} (Submodule.span.{0, u_1} Real (Singleton.singleton.{u_1, u_1} v)))))" with
    | .ok stx => pure stx
    | .error err => throwError err
  let expected ← Term.elabType parsed
  Term.synthesizeSyntheticMVarsNoPostponing
  let expected ← instantiateMVars expected
  let actual := info.type.instantiateLevelParams info.levelParams levels
  if expected.hasMVar || expected.hasLevelMVar || actual.hasMVar || actual.hasLevelMVar then
    throwError "unresolved metavariables in frozen type for {name}"
  unless (← isProp expected) == true && (← isProp actual) == true do
    throwError "frozen Prop classification mismatch for {name}"
  unless ← isDefEq actual expected do
    throwError "rigid frozen type mismatch for {name}: actual {actual}, expected {expected}"
  logInfo m!"FROZEN_CONTRACT_OK: {name}"
run_cmd liftTermElabM do
  let name := "Poincare.inner_stereoInvFunAuxFDeriv_of_mem_orthogonal".toName
  let info ← getConstInfo name
  let levelNames : List Name := ["u_1".toName]
  let levels : List Level := [Level.param "u_1".toName]
  unless info.levelParams == levelNames do
    throwError "frozen universe parameters mismatch for {name}: {info.levelParams}"
  unless info.isTheorem == true do
    throwError "frozen declaration kind mismatch for {name}"
  let parsed ← match Parser.runParserCategory (← getEnv) `term "∀ {E : Type u_1} [inst : NormedAddCommGroup.{u_1} E] [inst_1 : InnerProductSpace.{0, u_1} Real E] {v z u w : E}, Eq.{1} (Norm.norm.{u_1} v) (1 : Real) → Membership.mem.{u_1, u_1} (Submodule.orthogonal.{0, u_1} (Submodule.span.{0, u_1} Real (Singleton.singleton.{u_1, u_1} v))) z → Membership.mem.{u_1, u_1} (Submodule.orthogonal.{0, u_1} (Submodule.span.{0, u_1} Real (Singleton.singleton.{u_1, u_1} v))) u → Membership.mem.{u_1, u_1} (Submodule.orthogonal.{0, u_1} (Submodule.span.{0, u_1} Real (Singleton.singleton.{u_1, u_1} v))) w → Eq.{1} (Inner.inner.{0, u_1} Real ((Poincare.stereoInvFunAuxFDeriv.{u_1} v z) u) ((Poincare.stereoInvFunAuxFDeriv.{u_1} v z) w)) (HMul.hMul.{0, 0, 0} (Poincare.stereoInvFunAuxConformalFactor.{u_1} z) (Inner.inner.{0, u_1} Real u w))" with
    | .ok stx => pure stx
    | .error err => throwError err
  let expected ← Term.elabType parsed
  Term.synthesizeSyntheticMVarsNoPostponing
  let expected ← instantiateMVars expected
  let actual := info.type.instantiateLevelParams info.levelParams levels
  if expected.hasMVar || expected.hasLevelMVar || actual.hasMVar || actual.hasLevelMVar then
    throwError "unresolved metavariables in frozen type for {name}"
  unless (← isProp expected) == true && (← isProp actual) == true do
    throwError "frozen Prop classification mismatch for {name}"
  unless ← isDefEq actual expected do
    throwError "rigid frozen type mismatch for {name}: actual {actual}, expected {expected}"
  logInfo m!"FROZEN_CONTRACT_OK: {name}"
run_cmd liftTermElabM do
  let name := "Poincare.inner_fderiv_stereoInvFunAux_comp_subtype".toName
  let info ← getConstInfo name
  let levelNames : List Name := ["u_1".toName]
  let levels : List Level := [Level.param "u_1".toName]
  unless info.levelParams == levelNames do
    throwError "frozen universe parameters mismatch for {name}: {info.levelParams}"
  unless info.isTheorem == true do
    throwError "frozen declaration kind mismatch for {name}"
  let parsed ← match Parser.runParserCategory (← getEnv) `term "∀ {E : Type u_1} [inst : NormedAddCommGroup.{u_1} E] [inst_1 : InnerProductSpace.{0, u_1} Real E] (v : E), Eq.{1} (Norm.norm.{u_1} v) (1 : Real) → ∀ (z u w : ↥(Submodule.orthogonal.{0, u_1} (Submodule.span.{0, u_1} Real (Singleton.singleton.{u_1, u_1} v)))), Eq.{1} (Inner.inner.{0, u_1} Real ((fderiv.{0, u_1, u_1} Real (Function.comp.{u_1 + 1, u_1 + 1, u_1 + 1} (stereoInvFunAux.{u_1} v) Subtype.val.{u_1 + 1}) z) u) ((fderiv.{0, u_1, u_1} Real (Function.comp.{u_1 + 1, u_1 + 1, u_1 + 1} (stereoInvFunAux.{u_1} v) Subtype.val.{u_1 + 1}) z) w)) (HMul.hMul.{0, 0, 0} (Poincare.stereoInvFunAuxConformalFactor.{u_1} ↑z) (Inner.inner.{0, u_1} Real u w))" with
    | .ok stx => pure stx
    | .error err => throwError err
  let expected ← Term.elabType parsed
  Term.synthesizeSyntheticMVarsNoPostponing
  let expected ← instantiateMVars expected
  let actual := info.type.instantiateLevelParams info.levelParams levels
  if expected.hasMVar || expected.hasLevelMVar || actual.hasMVar || actual.hasLevelMVar then
    throwError "unresolved metavariables in frozen type for {name}"
  unless (← isProp expected) == true && (← isProp actual) == true do
    throwError "frozen Prop classification mismatch for {name}"
  unless ← isDefEq actual expected do
    throwError "rigid frozen type mismatch for {name}: actual {actual}, expected {expected}"
  logInfo m!"FROZEN_CONTRACT_OK: {name}"
run_cmd do
  let names : List Name := ["Poincare.stereoInvFunAuxConformalFactor".toName, "Poincare.stereoInvFunAuxFDeriv".toName, "Poincare.stereoInvFunAuxFDeriv_apply".toName, "Poincare.hasFDerivAt_stereoInvFunAuxFDeriv".toName, "Poincare.fderiv_stereoInvFunAux".toName, "Poincare.fderiv_stereoInvFunAux_comp_subtype".toName, "Poincare.inner_stereoInvFunAuxFDeriv_of_mem_orthogonal".toName, "Poincare.inner_fderiv_stereoInvFunAux_comp_subtype".toName]
  let environment := (← getEnv).setExporting false
  let allowed : List Name := ["propext".toName, "Classical.choice".toName, "Quot.sound".toName]
  let mut pending := names
  let mut seen : NameSet := {}
  let mut closureAxioms : NameSet := {}
  let mut recursorRules : Nat := 0
  let mut inductiveConstructors : Nat := 0
  while !pending.isEmpty do
    let current := pending.head!
    pending := pending.tail!
    if !seen.contains current then
      seen := seen.insert current
      let some info := environment.find? current |
        throwError "missing transitive dependency {current}"
      if info.isUnsafe || info.isPartial then
        throwError "unsafe or partial transitive declaration {current}"
      pending := (FrozenRoundChartSafety.usedConstants info.type).toList ++ pending
      if let some value := info.value? (allowOpaque := true) then
        pending := (FrozenRoundChartSafety.usedConstants value).toList ++ pending
      match info with
      | .axiomInfo _ =>
        unless allowed.contains current do
          throwError "forbidden transitive axiom {current}"
        closureAxioms := closureAxioms.insert current
      | .recInfo value =>
        pending := value.all ++ pending
        for rule in value.rules do
          recursorRules := recursorRules + 1
          pending := rule.ctor :: (FrozenRoundChartSafety.usedConstants rule.rhs).toList ++ pending
      | .inductInfo value =>
        inductiveConstructors := inductiveConstructors + value.ctors.length
        pending := value.all ++ value.ctors ++ pending
      | .ctorInfo value => pending := value.induct :: pending
      | _ => pure ()
  logInfo m!"TRANSITIVE_SAFETY_OK: visited={seen.toList.length}, recursor_rules={recursorRules}, inductive_constructors={inductiveConstructors}, axioms={closureAxioms.toList}"
  for name in names do
    let footprint ← collectAxioms name
    for dependency in footprint do
      unless allowed.contains dependency do
        throwError "forbidden axiom {dependency} in {name}"
    logInfo m!"AXIOM_CONTRACT_OK: {name} {footprint}"
