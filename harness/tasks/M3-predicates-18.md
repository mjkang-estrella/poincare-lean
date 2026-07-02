Read harness/worker_contract.md first and obey it strictly.

# Task M3-predicates-18: prove the two trace-field derivative predicates (first-order proof, replayed)

Read `harness/reports/M3-scalar-variation_notes.md` latest status. On main: `deltaGammaFirstSlotTraceFieldAt` / `deltaGammaInnerTraceFieldAt` (the two fields), their adapters into the frozen bridges, the C² regularity vocabulary (`CovTensor2ExtSecondDifferentiableAt` etc.), and — crucially — the COMPLETE first-order proof to replay: `traceMetricVariationAt_eq_sum_gram_inv` → `traceMetricVariationAt_extDerivFun_eq_gram_rhs` → `gram_rhs_extDerivFun_eq_sum_product` → `gramMatrix_inv_extDerivFun_eq_neg_sum` → `gram_inv_deriv_contraction_eq_leviCivita_corrections` → `traceMetricVariationDerivAt_of_covTensor2ExtDifferentiableAt` (read this chain in ScalarVariation.lean end-to-end BEFORE writing anything — your task is its structural copy for the new fields).

Deliverable: for EACH field (contraction-side first, its own commits):
1. Gram formula for the field near x (the field is a δΓ trace = combination of Gram-inverse entries × first-derivative scalar entries — derive its `= Σ Gram⁻¹ · ∂-entries` form from the existing pointwise identities, promoted to y near x; the two-point `gramMatrix g x y` machinery supports this).
2. Differentiability of the field at x from the C² classes (finite sums/products/inverses of C¹ entries — the entries are now ∂-of-C² = C¹).
3. `extDerivFun` of the field at x: product rule + `gramMatrix_inv_extDerivFun_eq_neg_sum` + the Levi-Civita cancellation (`gram_inv_deriv_contraction_eq_leviCivita_corrections` pattern — a second application, possibly needing the mixed-derivative symmetry of the C² entries: Schwarz for extDerivFun∘extDerivFun of scalar entries; if a Schwarz lemma for the closed extDerivFun is missing, Mathlib's `isSymmSndFDerivAt` + the entries being plain scalar functions on M through charts... if THAT stalls, name it honestly as the single Schwarz obligation with a witness).
4. Identify with the frozen field-predicate statement → the adapters fire → `DeltaGammaContractionTraceHessianDerivativeAt` / `...DivergenceTraceInner...` discharged.

One field fully closed > both half-done. Exact-goal-state rule. No sorry/axiom. `lake build Poincare.Global.ScalarVariation Poincare.Global.ScalarEvolution`, report names.
