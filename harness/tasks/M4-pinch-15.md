Read harness/worker_contract.md first and obey it strictly.

# Task M4-pinch-15: finish the cancellation → the Bochner identity → THE PARABOLIC |Ric|² INEQUALITY

Read `harness/reports/M4-pinch-14_blocked.md` — it contains the EXACT remaining work, with the group definitions PRE-DRAFTED in the report. On main: the full 12-commit moving covRicci expansion (target bridged to `covRicciPairingGramProductRuleRHS`; covariant-Ricci derivative group → second-derivative expansion; second-derivative group → second-covariant + Levi corrections; direction correction identified cancel-ready).

Deliverables (each its own commit; the pinch-12 discipline verbatim):
1. **The Ricci-entry derivative group split**: implement the report's drafted `covRicciPairingRicciCovariantGroup` / `...FirstSlotLeviCorrectionGroup` / `...SecondSlotLeviCorrectionGroup` definitions + `covRicciPairingRicciDerivGroup_eq_covariant_plus_leviCorrections` (via `closedRicciDerivativeExpansionAt_canonical` — same as pinch-12 step 3).
2. **The six-group cancellation** (the report's displayed `= 0` statement): the two inverse-Gram derivative groups + four Levi-correction groups sum to zero — the moving Gram inverse correction discipline (pinch-12 step 4 doubled; `gramMatrix_inv_extDerivFun_eq_neg_sum` + `spatialMetricDerivAt_eq_leviCivita` + reindex + `ring`).
3. **Assemble the expansion**: `extDerivFun (fun y => covRicciRicciPairingAt g y (extend E w y)) x u = [second-covariant Ricci ⊗ Ric group] + [∇Ric ⊗ ∇Ric group]` (the two survivors).
4. **Diagonal identification + Bochner**: substitute into `laplacianAt_ricciNormSqAt_eq_sum_extDerivFun_covRicciRicciPairingAt_sub` (on main); identify the traced second-covariant term = `roughRicciLaplacianPairingAt` and the traced ∇Ric⊗∇Ric term = `covRicciNormSqAt` → **`laplacianAt_ricciNormSqAt_eq_two_roughPairing_add_two_covNormSq`** (pin coefficients on the diagonal pattern).
5. **THE PARABOLIC |Ric|² INEQUALITY**: combine with `covRicciNormSqAt_nonneg` + `hasDerivAt_ricciNormSqAt_...reaction3` → `d/dt |Ric|² ≤ Δ|Ric|² + [reaction/motion traces]`. Historic done-report (both quotient-rule inputs complete).

If any step stalls: commit priors + paste the literal goal. Standing protocols. No sorry/axiom. `lake build Poincare.Global.ScalarVariation Poincare.Global.RicciNorm Poincare.Global.ScalarEvolution`, report names.
