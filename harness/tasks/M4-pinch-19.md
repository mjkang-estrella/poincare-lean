Read harness/worker_contract.md first and obey it strictly.

# Task M4-pinch-19: the completed-square identity (the quotient assembly's one obligation)

On main: `satisfiesPinchingQuotientEvolutionAt_of_ricciFlow` holds modulo ONE named hypothesis, `PinchingQuotientCompletedSquareIdentityAt` (ScalarEvolution.lean ~line 129). Read its exact statement and `harness/reports/M4-pinch-18_done`/status report — the identity is displayed there:

`ΔN/R² − 2N·ΔR/R³ − 2|∇Ric|²/R² = ΔQ + (2/R)⟨∇R, ∇Q⟩ − (2/R⁴)|R·∇Ric − ∇R⊗Ric|²`, with N = |Ric|², Q = N/R².

This is spatial calculus + algebra at a point with R > 0. Route:
1. Expand ΔQ and ∇Q via the quotient product-rule lemmas ON MAIN (pinch-18's `laplacianAt`/`gradientAt` quotient lemmas — reuse, don't rederive).
2. Define the mixed-gradient pairing `⟨∇Ric, ∇R⊗Ric⟩`-shape vocabulary honestly if missing (the contraction of covRicci with gradient⊗Ric — the Gram machinery; note `covRicciNormSqAt` and `scalarGradNormSqAt` exist; the CROSS term is the one possibly-new object — check first, pinch-18 may have added it).
3. Expand the completed square `|R·∇Ric − ∇R⊗Ric|² = R²|∇Ric|² − 2R⟨∇Ric, ∇R⊗Ric⟩ + |∇R|²·N` (bilinearity of the Gram inner product — sum algebra).
4. The identity then reduces to matching the ⟨∇R,∇Q⟩ and |∇R|² coefficient groups — `field_simp`/`ring` at R ≠ 0. PIN on a diagonal pattern with nonzero gradients if feasible (or verify the coefficient match symbolically in the report).
5. Land `pinchingQuotientCompletedSquareIdentityAt_of_...` (honest regularity hypotheses) → the quotient evolution holds unconditionally → restate `satisfiesPinchingQuotientEvolutionAt_of_ricciFlow'` discharged. Done-report.

BUILD NOTE: ScalarVariation.lean elaborates ~10+ min/check; use `lake env lean` per-file, be patient with the final build. Standing protocols. No sorry/axiom. `lake build Poincare.Global.ScalarVariation Poincare.Global.ScalarEvolution`, report names.
