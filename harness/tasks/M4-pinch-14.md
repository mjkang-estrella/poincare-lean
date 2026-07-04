Read harness/worker_contract.md first and obey it strictly.

# Task M4-pinch-14: the covRicciRicciPairing moving-frame product rule → Bochner → THE PARABOLIC INEQUALITY

Read `harness/reports/M4-pinch-13_blocked.md` — ONE expansion remains:
`extDerivFun (fun y => covRicciRicciPairingAt g y (extend E w y)) x u` = [second-covariant Ricci term paired with Ric] + [covariant-Ricci paired with covariant-Ricci].

METHOD — this is the pinch-12 playbook ONE DERIVATIVE UP, with every tool already on main:
1. Unfold `covRicciRicciPairingAt`'s definition (its Gram/anchored form from pinch-9/12) at the moving point y with the moving direction `extend E w y`; the moving-anchor expansion machinery (the K-slot bridges + moving Gram lemmas from the M4-prep campaign, the anchored expansions from pinch-11/12) covers every factor.
2. Product-rule differentiate: the ∂(covTensor2Deriv-entry) group → `covTensor2SecondDerivAt` entries paired with Ric (via `closedRicciDerivativeExpansionAt_canonical` + the second-deriv entry machinery); the ∂(Ric-entry) group → covariant-Ricci paired with covariant-Ricci; the Gram-inverse and extend-frame correction groups cancel per the standard discipline (pinch-12 commits 2+4 are the literal template).
3. Commit granularity: SAME five-step split as pinch-12 (expansion / group rewrites / cancellation / merge). If any step stalls, commit priors + paste the literal goal.
4. **Then the payoff chain** (on main, waiting): substitute into `laplacianAt_ricciNormSqAt_eq_sum_extDerivFun_covRicciRicciPairingAt_sub` → the traced Bochner identity `Δ|Ric|² = 2·roughRicciLaplacianPairingAt + 2·covRicciNormSqAt` (pin coefficients on the diagonal pattern) → combine with `covRicciNormSqAt_nonneg` + `hasDerivAt_ricciNormSqAt_...reaction3` → **THE PARABOLIC |Ric|² INEQUALITY** (the rough-pairing cancellation between the two sides — verify shape informally first). Done-report.

Standing protocols. No sorry/axiom. `lake build Poincare.Global.ScalarVariation Poincare.Global.RicciNorm Poincare.Global.ScalarEvolution`, report names.
