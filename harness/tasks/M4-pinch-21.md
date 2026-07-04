Read harness/worker_contract.md first and obey it strictly.

# Task M4-pinch-21: the spatial expansion → the quotient evolution UNCONDITIONAL

Read `harness/reports/M4-pinch-19_progress.md` — the remaining boundary is fully specified. On main: the completed-square orthogonal-frame expansion (proven), the wrapper reducing `PinchingQuotientCompletedSquareIdentityAt` to the explicit spatial expansion, `satisfiesPinchingQuotientEvolutionAt_of_ricciFlow_of_spatial_expansion`, the quotient product-rule lemmas (pinch-18), and (from parallel pinch-20, merged) the eigenvalue reaction-sign lemmas in RicciNorm.lean.

Deliverables (each its own commit):
1. **The two Gram bridges** (per the report): (a) `cross = covRicciRicciPairingAt g x (g.gradientAt scalarAt x)` — the mixed-gradient contraction identified with the covRicci pairing evaluated at the gradient direction (the pinch-12/14 anchored machinery); (b) `rawProduct = scalarGradNormSqAt g x * ricciNormSqAt g x` — the ∇R⊗Ric norm factorization (Gram bilinearity + the orthonormal frame sum).
2. **The spatial expansion**: `ΔQ + (2/R)⟨∇R,∇Q⟩ = ΔN/R² − 2N·ΔR/R³ − 4·cross/R³ + 2·rawProduct/R⁴` at scalarAt x > 0 — from the quotient product-rule lemmas + the bridges + `field_simp`/`ring`.
3. **Fire**: `satisfiesPinchingQuotientEvolutionAt_of_ricciFlow_of_spatial_expansion` + step 2 → **`satisfiesPinchingQuotientEvolutionAt_of_ricciFlow` UNCONDITIONAL** (honest regularity classes only). Done-report + step-6 outlook (manifold-level reaction sign via the eigenvalue lemmas + spectral decomposition, then the maximum principle).

BUILD NOTE: ScalarVariation.lean elaborates ~10+ min/check; use `lake env lean` per-file, be patient with the final build — do not kill silent builds. Standing protocols. No sorry/axiom. `lake build Poincare.Global.ScalarVariation Poincare.Global.ScalarEvolution Poincare.Global.RicciNorm`, report names.
