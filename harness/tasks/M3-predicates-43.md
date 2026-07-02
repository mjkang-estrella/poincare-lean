Read harness/worker_contract.md first and obey it strictly.

# Task M3-predicates-43: THE CYCLIC CORE — the last identity of the Hamilton theorem

Everything else is done. ONE identity remains for `ClosedContractedBianchiAt` (its consumer `of_closed_trace_contraction_canonical` is on main, hypothesis-light):

`∀ᶠ y in 𝓝 x, ∀ w : TM y, 2 * closedRicciDivergenceTraceAt g y w = closedScalarContractionDerivTraceAt g y w`

This is the twice-contracted SECOND BIANCHI identity in the closed trace vocabulary. Model template: `coord_second_bianchi` → `coord_twice_contracted_bianchi` (ModelLaplacian.lean — read both proofs COMPLETELY first; this is the computation to replay).

Assets on main (everything you need):
- The predicates-36 scaffold: `closedCurvatureCovDerivAt`, `closedRicciDivergenceTraceAt`, `closedScalarContractionDerivTraceAt`, the raw contraction lemmas, Ricci-derivative slot symmetry, divergence slot swap, the raised middle-term contraction notes (M3-predicates-36/37 reports).
- The CANONICAL curvature entry bridge + curvature-field differentiability (C² instance) — differentiating curvature entries is now routine.
- The full swap/cancellation/Schwarz toolkit.

Suggested route:
1. **Second Bianchi (cyclic ∇Rm sum = 0)** at the anchored point: expand `closedCurvatureCovDerivAt` via the curvature entry bridge into flat second-derivative connection terms; the cyclic sum's terms cancel pairwise by the closed Schwarz lemmas (EXACTLY the model's `coord_second_bianchi` cancellation — replay it line by line in the extend frame).
2. **First contraction**: trace one slot pair via the Gram machinery.
3. **Second contraction**: trace again; the slot symmetries (`ricciAt_symm`, the divergence slot swap from the scaffold) reorganize the three cyclic terms into `2·divTrace − scalarContractionTrace = 0`.
4. **FIRE**: → `ClosedContractedBianchiAt` DISCHARGED → state the FINAL `satisfiesHamiltonScalarEvolutionAt_of_ricciFlow` (honest regularity only) + `hamiltonScalarEvolutionProgram` final form. Historic done-report.

Multi-session acceptable — land the second-Bianchi core minimum. Standing sanity checks. Exact-goal-state on failure. No sorry/axiom. `lake build Poincare.Global.ScalarVariation Poincare.Global.ScalarEvolution`, report names.
