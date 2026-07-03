Read harness/worker_contract.md first and obey it strictly.

# Task M4-pinch-12: the 4-factor derivative — FIVE COMMITS, one per recipe step

Read `harness/reports/M4-pinch-11_blocked.md`. Lemma 1 (the anchored expansion `metricVariationRicciPairingAt_ricci_eq_sum_gram_inv`) is PROVEN on main. This task: lemma 2, executed as FIVE SEPARATE COMMITS matching the recipe's five steps exactly — commit each step's lemma as its own named theorem even if intermediate (granularity is the point; each step is individually small):

1. Commit 1 — `pairing_gram_product_rule_expand`: the extDerivFun of the 4-index sum = the four product-rule groups (two ∂(Gram⁻¹) groups + two ∂(Ric-entry) groups), via `HasFDerivAt.mul`-chains on the finite sum (differentiability of every factor is on main). Pure calculus, no geometry.
2. Commit 2 — rewrite the two inverse-Gram derivative groups via `gramMatrix_inv_extDerivFun_eq_neg_sum` + `spatialMetricDerivAt_eq_leviCivita` (per-group lemma).
3. Commit 3 — rewrite the two Ricci-entry derivative groups via `closedRicciDerivativeExpansionAt_canonical` (per-group lemma).
4. Commit 4 — the cancellation: the two inverse-Gram groups cancel the four Levi-Civita correction groups (the `gram_inv_deriv_contraction_eq_leviCivita_corrections` pattern doubled — sum reindexing + `ring`).
5. Commit 5 — merge the surviving covariant-Ricci groups via `covTensor2DerivAt_ricciVariationField_symm` + `ricciAt_symm` → **`extDerivFun_ricciPairing_eq_two_covRicciRicciPairingAt`** (the target). Diagonal pin.

If ANY single step fails: commit the prior steps + paste the literal goal. No sorry/axiom. `lake build Poincare.Global.ScalarVariation`, report names.
