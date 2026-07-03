Read harness/worker_contract.md first and obey it strictly.

# Task M4-pinch-13: second derivative + trace → the Bochner identity → THE PARABOLIC |Ric|² INEQUALITY

On main (all gate PASS): `extDerivFun_ricciPairing_eq_two_covRicciRicciPairingAt` (the |Ric|² first derivative = 2·⟨∇Ric, Ric⟩, with its full 5-step lemma chain), `covRicciRicciPairingAt` + `covRicciNormSqAt` (+nonneg), `roughRicciLaplacianPairingAt`, the second-order machinery (canonical C² instances, closed Schwarz, the covTensor2SecondDeriv trace tools), `hasDerivAt_ricciNormSqAt_of_satisfiesRicciEvolutionAt` (+`_reaction3`), and the M4-pinch-6 pinned reaction/motion traces.

Deliverables (each its own commit; per the pinch-9/10 plans):
1. **Differentiate the first-derivative theorem once more**: `extDerivFun (fun y => covRicciRicciPairingAt g y ·)`-shape at x — product rule on ⟨∇Ric, Ric⟩: the ∇Ric-derivative term (second covariant derivative paired with Ric) + the Ric-derivative term (∇Ric paired with ∇Ric — the |∇Ric|² shape). Same anchored playbook, now with the pinch-12 lemma chain as the template (the hard part — the quadratic Gram discipline — is already proven; this is its derivative).
2. **Trace over the direction slot** (the laplacianAt definition): `laplacianAt (fun y => ricciNormSqAt y) x = 2·roughRicciLaplacianPairingAt g x + 2·covRicciNormSqAt g x` — recognize the traced second-covariant term as the rough Laplacian pairing (definition match / trace-commute) and the traced ∇Ric⊗∇Ric term as covRicciNormSqAt. PIN both coefficients on the diagonal pattern.
3. **THE PARABOLIC |Ric|² INEQUALITY**: combine with `covRicciNormSqAt_nonneg` + the evolution layer → `d/dt ricciNormSqAt ≤ laplacianAt(ricciNormSqAt) + 2·⟨reaction-remainder, Ric⟩ + motion-terms` (exact RHS per the reaction3-substituted derivative on main; the rough-pairing terms cancel between the two sides — verify the cancellation shape informally first). Done-report: this + the scalar-square parabolic form = both quotient-rule inputs; note the step-4/5 outlook.

Standing protocols. No sorry/axiom. `lake build Poincare.Global.ScalarVariation Poincare.Global.RicciNorm Poincare.Global.ScalarEvolution`, report names.
