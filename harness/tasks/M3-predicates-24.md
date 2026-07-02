Read harness/worker_contract.md first and obey it strictly.

# Task M3-predicates-24: the divergence-side assembly (replay of the contraction-side close)

The contraction-side chain is CLOSED on main: `deltaGammaEntryDerivativeBridgeAt_of_deltaGammaFieldMDifferentiableAt` → `deltaGammaFirstSlotTraceFieldCovariantDerivativeAt_of_entryBridge` → `DeltaGammaContractionTraceHessianDerivativeAt` discharged from honest classes. Read that full chain in Global/ScalarVariation.lean FIRST — your task is its structural replay for the divergence side.

Target: discharge `DeltaGammaDivergenceTraceInnerHessianDerivativeAt` (its adapter `deltaGammaDivergenceTraceInnerHessianDerivativeAt_of_innerTraceField` waits on `DeltaGammaInnerTraceFieldCovariantDerivativeAt`).

Replay steps (each its own commit):
1. **Anchored Gram identity for the inner-trace field** (`deltaGammaInnerTraceFieldAt`): the analogue of `deltaGammaFirstSlotTraceFieldAt_eq_sum_gram_inv` (on main — mirror its proof; the inner trace contracts different slots, so the Gram expression differs in index placement only).
2. **Entry bridge reuse**: the inner-trace field's entries are the SAME `g(δΓ(ext,ext),ext)` scalars — the proven entry bridge applies as-is (possibly with slots permuted; if a permuted variant is needed, derive it from the proven one + δΓ symmetry/slot lemmas rather than reproving).
3. **Field covariant derivative**: `DeltaGammaInnerTraceFieldCovariantDerivativeAt` via the same Gram product rule + `gramMatrix_inv_extDerivFun_eq_neg_sum` + slot-cancellation (`deltaGammaFirstSlotTrace_leviCivita_slot_cancel` has the pattern; an inner-slot variant may be needed — same proof shape).
4. **Cascade + consolidation**: `DeltaGammaDivergenceTraceInnerHessianDerivativeAt` discharged → BOTH Hessian assemblies now closed → state the consolidated theorem: `scalarVariation_lichnerowicz` (and the Hamilton wrappers) from honest regularity classes + ClosedContractedBianchiAt + the two substitution predicates ONLY. Update notes with the exact remaining predicate list.

Exact-goal-state rule. No sorry/axiom. `lake build Poincare.Global.ScalarVariation Poincare.Global.ScalarEvolution`, report names.
