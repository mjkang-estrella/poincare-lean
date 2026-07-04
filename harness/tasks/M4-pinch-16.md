Read harness/worker_contract.md first and obey it strictly.

# Task M4-pinch-16: the six-group cancellation → Bochner → THE PARABOLIC |Ric|² INEQUALITY

Read `harness/reports/M4-pinch-15_blocked.md` — its "Literal next goal" displays THE theorem of this task verbatim (`covRicciPairing_gram_inv_deriv_groups_cancel_leviCorrections`: two inverse-Gram derivative groups + four Levi slot-correction groups sum to 0) with the four-bullet recipe. Everything it references is on main (the pinch-14/15 group definitions and split theorems; the pinch-12 cancellation discipline lemmas).

Deliverables (each its own commit):
1. **The cancellation** per the recipe: covariant-Ricci analogues of the two inverse-Gram contraction tensors; rewrite via `gram_inv_deriv_contraction_eq_leviCivita_corrections` (or `gramMatrix_inv_extDerivFun_eq_neg_sum` + `spatialMetricDerivAt_eq_leviCivita`); identify the four produced slot-correction sums with the four named groups; `ring`.
2. **Assemble**: the full moving covRicci pairing derivative = [second-covariant Ricci ⊗ Ric group] + [∇Ric ⊗ ∇Ric group] (the two survivors; the assembly chain from pinch-14 is on main and waiting).
3. **Bochner**: substitute into `laplacianAt_ricciNormSqAt_eq_sum_extDerivFun_covRicciRicciPairingAt_sub` → identify traced survivors with `roughRicciLaplacianPairingAt` and `covRicciNormSqAt` → `laplacianAt_ricciNormSqAt_eq_two_roughPairing_add_two_covNormSq`. Diagonal-pattern pin.
4. **THE PARABOLIC |Ric|² INEQUALITY**: + `covRicciNormSqAt_nonneg` + `hasDerivAt_ricciNormSqAt_...reaction3` → `d/dt |Ric|² ≤ Δ|Ric|² + [reaction/motion traces]`. Historic done-report.

BUILD NOTE: ScalarVariation.lean elaborates slowly (~10+ min single-module); prefer `lake env lean` on the file for iteration and be patient with the final `lake build` — silence is normal, do not kill it early.

If any step stalls: commit priors + paste the literal goal. Standing protocols. No sorry/axiom. `lake build Poincare.Global.ScalarVariation Poincare.Global.RicciNorm Poincare.Global.ScalarEvolution`, report names.
