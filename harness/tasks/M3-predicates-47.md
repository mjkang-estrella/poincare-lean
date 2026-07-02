Read harness/worker_contract.md first and obey it strictly.

# Task M3-predicates-47: the cyclic cancellation, now with the expansion in hand

On main (NEW): `closedCurvature_koszul` — `closedCurvatureEntryDerivAt` = `closedCurvatureDefExpansionAt` (explicit second-connection-derivative + bracket/product terms), with iterated/bracket entry fields and derivative bridges. Plus (from predicates-44): the cyclic scalar-paired expansion theorem connecting `closedCurvatureCovDerivAt` sums to `closedCurvatureEntryDerivAt` terms + corrections.

Target: the cyclic second Bianchi —
`∀ᶠ y in 𝓝 x, ∀ u v w z, closedCurvatureCovDerivAt g y v u w z + closedCurvatureCovDerivAt g y u w v z + closedCurvatureCovDerivAt g y w v u z = 0`
(the exact hypothesis of `eventually_closed_twice_contracted_bianchi_trace_of_second_bianchi`, on main).

Route (the model's `coord_second_bianchi` endgame, now executable):
1. Substitute the predicates-44 expansion + `closedCurvature_koszul` into each of the three cyclic terms → everything in ∂∂Γ-entry + Γ·∂Γ-entry + correction terms.
2. Cancellation groups (model proof as guide): (i) ∂∂Γ mixed-derivative pairs cancel by the closed Schwarz lemmas; (ii) torsion symmetry (`leviCivita_torsionFreeAt` — the connection's slot symmetry on extend sections) aligns the Γ·∂Γ terms into cancelling pairs; (iii) the metric/bracket corrections cancel cyclically. Close with `ring`/`abel` per group. One commit per cancellation group is fine.
3. Conclude the ∀ᶠ statement.
4. If budget: last-atom #2 — hMiddle (the middle curvature-divergence trace = closedRicciDivergenceTraceAt; a Gram contraction bookkeeping lemma per the predicates-36/37 notes) → then the full chain: `eventually_...of_second_bianchi` → `ClosedContractedBianchiAt.of_closed_trace_contraction_canonical` → **HAMILTON THEOREM COMPLETE** — state `satisfiesHamiltonScalarEvolutionAt_of_ricciFlow` final + program form + historic done-report.

Standing sanity checks. Exact-goal-state on failure. No sorry/axiom. `lake build Poincare.Global.ScalarVariation Poincare.Global.ScalarEvolution`, report names.
