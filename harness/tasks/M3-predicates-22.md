Read harness/worker_contract.md first and obey it strictly.

# Task M3-predicates-22: the δΓ-entry derivative bridge → close the contraction assembly

Read `harness/reports/M3-predicates-21_blocked.md`. ONE derivative bridge remains before the contraction-side cascade fires: the spatial derivative formula for the scalar entries
`y ↦ g.inner y (deltaGammaAt gt t₀ y (extend E p y) (extend E q y)) (extend E w y)`
identified as `g(covDeltaGammaDerivAt ..., ...)` + Levi-Civita correction terms.

This is the δΓ-slot analogue of `spatialMetricDerivAt_eq_leviCivita` (on main). Route:
1. Product rule on the triple pairing: ∂[g(A(y), B(y))] = (∂g)(A,B) + g(∂A, B) + g(A, ∂B) — the ∂g term via `spatialMetricDerivAt_eq_leviCivita`, the extend-section derivatives via the extend-derivative lemmas (`extDerivFun_h_extend_eq_covTensor2DerivAt_add_corrections`-family and the extend-section Christoffel calculus used in predicates-13's `covariant extension-slot derivative bridge` — mine `9cd80995`'s lemmas, on main).
2. The ∂(δΓ)-term: `covDeltaGammaDerivAt`'s DEFINITION is the covariant derivative of deltaGammaAt = flat derivative + Christoffel slot corrections (read its exact definition) — so ∂(δΓ-values) = covDeltaGammaDerivAt − corrections, definitionally or by a small rearrangement. Differentiability side conditions from the C²/ContMDiff classes (on main; if a δΓ-specific differentiability field is genuinely missing, add it honestly to the vocabulary with static witness — δΓ of a static family is 0, trivially regular).
3. Assemble the bridge lemma in exactly the shape `M3-predicates-21_blocked.md` requests; then execute the 4-step plan already recorded there (anchored rewrite → product rule + inverse-Gram → slot-cancellation → identify with `deltaGammaContractionDerivAt`) → **`DeltaGammaFirstSlotTraceFieldCovariantDerivativeAt` proven** → cascade → **`DeltaGammaContractionTraceHessianDerivativeAt` discharged**.
4. Notes + Hamilton wrapper cleanup.

Exact-goal-state rule. No sorry/axiom. `lake build Poincare.Global.ScalarVariation Poincare.Global.ScalarEvolution`, report names.
