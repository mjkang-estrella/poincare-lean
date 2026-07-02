Read harness/worker_contract.md first and obey it strictly.

# Task M3-predicates-37: the three native Bianchi bridges

Read `harness/reports/M3-predicates-36_progress.md` — it lists the exact three remaining near-x trace bridges for `ClosedContractedBianchiAt` (the LAST predicate of the Hamilton theorem):
1. The curvature/Ricci trace-derivative expansion bridge #1 (closed `covTensor2DerivAt` vocabulary → `closedRicciDivergenceTraceAt`).
2. Expansion bridge #2 (→ `closedScalarContractionDerivTraceAt`).
3. The cyclic identity `2·closedRicciDivergenceTraceAt = closedScalarContractionDerivTraceAt` from the closed second-Bianchi core + the raw contraction lemma + the raised middle-term contraction (scaffold lemmas on main from predicates-36).

For (1)/(2): these are trace-derivative expansions of the SAME shape closed a dozen times now — the Gram/extend entry-derivative machinery (entry bridges, `traceMetricVariationDerivAt` pattern, slot cancellations). For (3): the cyclic core is the second-Bianchi computation — the model's `coord_second_bianchi` proof is the line-by-line template; at the anchored point the connection-derivative cross terms cancel by the closed Schwarz lemmas (the same cancellation as `covDeltaGamma_koszul`'s proof, applied to the connection's own curvature rather than its time variation).

Work in the order (3) → (1) → (2) if the cyclic core is self-contained from the scaffold, else (1) → (2) → (3). Each bridge its own commit(s). If ALL THREE land: `ClosedContractedBianchiOneFormAt` near x → the adapter fires → **`ClosedContractedBianchiAt` DISCHARGED** → state the FINAL `satisfiesHamiltonScalarEvolutionAt_of_ricciFlow` from honest regularity classes only + the program form. Milestone done-report.

Standing sanity checks. Exact-goal-state on failure. No sorry/axiom. `lake build Poincare.Global.ScalarVariation Poincare.Global.ScalarEvolution`, report names.
