Read harness/worker_contract.md first and obey it strictly.

# Task M4-pinch-11: EXECUTE the quadratic expansion recipe (two lemmas, fully specified)

Read `harness/reports/M4-pinch-10_blocked.md` — it contains the two lemmas of this task FULLY SPECIFIED (statement + proof recipe with every named ingredient). Do not re-derive; execute:

1. **The anchored quadratic expansion** (the displayed 4-index sum): `metricVariationRicciPairingAt g (ricciVariationField g) y = Σₐᵦ𝒸𝒹 Gram⁻¹ₐ𝒸·Gram⁻¹ᵦ𝒹·Ric(frameₐ,frameᵦ)·Ric(frame𝒸,frame𝒹)` near x under `gramMatrix_eventually_isUnit`. Proof: the pairing's definition + the anchored-frame basis expansion applied to both raised slots (the `_eq_sum_gram_inv` proof pattern doubled — mirror `traceMetricVariationAt_eq_sum_gram_inv`'s proof with two frame expansions).
2. **The 4-factor product-rule derivative at x** (the recipe's four bullets): `gramMatrix_inv_extDerivFun_eq_neg_sum` + `spatialMetricDerivAt_eq_leviCivita` on both inverse-Gram factors; `closedRicciDerivativeExpansionAt_canonical` on both Ricci factors; the four Levi-Civita groups cancel the two inverse-Gram groups; `covTensor2DerivAt_ricciVariationField_symm` + `ricciAt_symm` merge the survivors → `extDerivFun (|Ric|²-pairing) x v = 2·covRicciRicciPairingAt g x v`. Diagonal-pattern pin.

Then (if budget): the second derivative + trace → the Bochner identity per the pinch-9 chain.

Standing protocols. No sorry/axiom. `lake build Poincare.Global.ScalarVariation Poincare.Global.RicciNorm`, report names.
