Read harness/worker_contract.md first and obey it strictly.

# Task M3-predicates-36: native closed contracted Bianchi — the extend-frame replay

Pivot verdict from `harness/reports/M3-predicates-35_blocked.md`: the transport route stalls at the derivative-level Ricci chart bridge (extDerivFun-on-extend vs flat fderiv — the known pathology). Go NATIVE: prove `ClosedContractedBianchiOneFormAt g y` (∀ᶠ y near x) — `div Ric = ½ dR` — directly in the closed vocabulary, replaying the model's computation with the established extend-frame toolkit.

Model template: `coord_twice_contracted_bianchi` + `coord_second_bianchi` (ModelLaplacian.lean — READ these proofs first; they are the computation to replay). The toolkit (all on main, all battle-tested through 20+ tasks): extend-section derivative calculus, entry bridges, `covDeltaGamma_koszul`-style identity differentiation, closed Schwarz lemmas, Gram/dual-basis contraction machinery, `sum_metricDualVectorAt_contraction_swap`, slot cancellations, `ricciAt_symm`, `laplacianAt`/Hessian identifications.

Suggested decomposition (each its own commit; adjust to the actual definitions):
1. **Closed curvature derivative expansion**: the spatial derivative of the closed Ricci entries `y ↦ g.ricciAt y (ext p)(ext q)` in terms of second connection derivatives — via the entry-bridge technology (the Ricci is a curvature trace; curvature is built from the connection; the `DeltaGammaEntryDerivativeBridgeAt` proof pattern differentiates connection-value pairings — here applied to the connection itself rather than its time-variation).
2. **The cyclic second-Bianchi core**: the alternating sum of the three ∇-curvature slots vanishes — at the anchored point the connection terms cancel pairwise by Schwarz (flat second-derivative symmetry) exactly as in the model's `coord_second_bianchi` (whose proof is the line-by-line guide).
3. **Double contraction** via the Gram machinery → `div Ric = ½ dR` at each y near x (the ∀ᶠ form the consumer needs).
4. **FIRE**: `ClosedContractedBianchiAt.of_oneForm_near` → `ClosedContractedBianchiAt` DISCHARGED → state the FINAL `satisfiesHamiltonScalarEvolutionAt_of_ricciFlow` (regularity classes only) + program form. Milestone done-report.

Multi-session expected — land the expansion + skeleton minimum. Standing sanity checks. Exact-goal-state on failure. No sorry/axiom. `lake build Poincare.Global.ScalarVariation Poincare.Global.ScalarEvolution`, report names.
