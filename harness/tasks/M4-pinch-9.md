Read harness/worker_contract.md first and obey it strictly.

# Task M4-pinch-9: the Ricci-norm Bochner bridge (4-step plan) → the parabolic |Ric|² inequality

Read `harness/reports/M4-pinch-8_blocked.md` — its 4-step "next proof unit" is this task (each step its own commit):

1. The closed rough-Ricci pairing term: define the metric trace pairing of `roughTensorLaplacianAt g (ricciVariationField g)` with `ricciVariationField g` (the ⟨ΔRic, Ric⟩ scalar).
2. First spatial derivative of `ricciNormSqAt`: from the derivative of `ricciVariationField` entries (the CANONICAL curvature/Ricci entry machinery — all on main from the goal-4 campaign) + the raise/lower metric-compatibility cancellation (the Gram playbook, run for the ~6th time — `traceMetricVariationDerivAt`'s proof is the direct template with h = the Ricci field itself, FIXED metric so no time subtleties).
3. Second-derivative trace identity: `laplacianAt (ricciNormSqAt) = 2·⟨rough-Lap Ric, Ric⟩ + 2·covRicciNormSqAt` — differentiate step 2 once more (the second-order machinery: the C² canonical instances, the closed Schwarz lemmas, the covTensor2SecondDeriv trace tools). PIN the two coefficients on the diagonal test pattern.
4. Combine with `covRicciNormSqAt_nonneg` + `hasDerivAt_ricciNormSqAt_of_satisfiesRicciEvolutionAt` (both on main) → **the parabolic |Ric|² inequality**: `d/dt |Ric|² ≤ Δ|Ric|² + 2⟨reaction-remainder, Ric⟩ + motion-terms` (state with the pinned reaction/motion traces from M4-pinch-6). This + the scalar-square parabolic form (on main) = both inputs of the quotient rule.

Standing protocols. No sorry/axiom. `lake build Poincare.Global.ScalarVariation Poincare.Global.RicciNorm Poincare.Global.ScalarEvolution`, report names.
