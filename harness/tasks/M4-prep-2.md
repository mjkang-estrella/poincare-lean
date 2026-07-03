Read harness/worker_contract.md first and obey it strictly.

# Task M4-prep-2: Ricci-evolution roadmap subtasks 2+3 (trace identities + regularity packaging)

Read `harness/reports/M4-prep-1_done.md` (the 6-subtask roadmap). This task takes the two MECHANICAL subtasks first (2 and 3), deferring the hard commutation (1) until the vocabulary is trace-validated:

1. **Subtask 2 — metric-trace identities**: for `roughTensorLaplacianAt`, `lichnerowiczCurvatureAt`, `ricciActionOnTensorAt`, `ricciQuadraticAt` (read their fresh definitions in ScalarVariation.lean ~13007): the g-trace of each, expressed in the proven scalar vocabulary. Expected results (verify against the classical formulas, sanity-check on flat/static): tr(rough Laplacian of Ric) = Δ(R)-shape via the trace-commute machinery (discharged), tr of the curvature-action terms = |Ric|²-shapes (`ricciNormSqAt`), tr(ricciQuadraticAt) = 2|Ric|²-shape. These validate the vocabulary BEFORE the commutation campaign — if a trace comes out wrong, that's a sign/slot error in the new definitions: report it exactly (this is roadmap subtask 4's check done early and cheaply).
2. **Subtask 3 — canonical regularity packaging**: bundle the canonical Ricci-field first/second spatial regularity (from the C² connection instances + the entry machinery) as instances/lemmas so consumers stop carrying raw `CovTensor2*` hypotheses — the same consolidation done for the curvature entries in predicates-41.
3. **The consistency payoff**: with the traces proven, state and prove the TRACE CONSISTENCY lemma — the g-trace of `SatisfiesRicciEvolutionAt`'s RHS = the proven scalar evolution RHS (ΔR + 2|Ric|²) — roadmap subtask 6's core identity, giving high confidence in the target statement before the proof campaign.

Standing sanity checks. Exact-goal-state on failure. No sorry/axiom. `lake build Poincare.Global.ScalarVariation Poincare.Global.ScalarEvolution`, report names.
