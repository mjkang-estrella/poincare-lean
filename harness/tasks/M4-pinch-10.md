Read harness/worker_contract.md first and obey it strictly.

# Task M4-pinch-10: the quadratic Gram cancellation → the |Ric|² first-derivative theorem

Read `harness/reports/M4-pinch-9_blocked.md` — ONE theorem:
`extDerivFun (fun y => metricVariationRicciPairingAt g (ricciVariationField g) y) x v = 2 * covRicciRicciPairingAt g x v`

Route — the anchored Gram expansion with a TRIPLE product rule (the quadratic extension of the six-times-proven linear playbook):
1. Expand the pairing near x in the anchored frame: `|Ric|²(y) = Σᵢⱼₖₗ Gram⁻¹(y)ᵢₖ · Gram⁻¹(y)ⱼₗ · Ric(y)(ext bᵢ, ext bⱼ) · Ric(y)(ext bₖ, ext bₗ)`-shape (the double-raised trace — derive from the `traceMetricVariationAt_eq_sum_gram_inv` pattern applied twice, or via the `ricciNormSqAt_eq_trace` endomorphism form with two Gram-inverse factors; pick the cleaner).
2. Differentiate: four factor groups — TWO Ric-entry derivatives (identical by symmetry → the factor 2, each = the canonical Ricci entry derivative machinery, on main) and TWO Gram-inverse derivatives (each cancels its Christoffel corrections via `gramMatrix_inv_extDerivFun_eq_neg_sum` + `spatialMetricDerivAt_eq_leviCivita` — the standard cancellation, run per factor).
3. Recognize `2·covRicciRicciPairingAt` (the covariant-derivative-of-Ric paired with Ric — its definition on main from pinch-9). PIN on the diagonal pattern.
4. Then the chain per the pinch-9 report: differentiate once more + trace (the second-order machinery) → `laplacianAt |Ric|² = 2·roughRicciLaplacianPairingAt + 2·covRicciNormSqAt` → combine with nonnegativity + the evolution layer → **the parabolic |Ric|² inequality** (as far as budget allows; the first-derivative theorem is the minimum).

Standing protocols. No sorry/axiom. `lake build Poincare.Global.ScalarVariation Poincare.Global.RicciNorm`, report names.
