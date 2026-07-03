Read harness/worker_contract.md first and obey it strictly.

# Task M4-prep-4: the two trace obligations → full trace consistency

Read `harness/reports/M4-prep-3_done.md`. On main: the corrected `lichnerowiczCurvatureAt`, sanity gates passed, trace-consistency lemmas wired modulo TWO obligations:

1. **`RoughTensorLaplacianRicciTraceAt`**: metric trace of the rough Laplacian of the Ricci field = the scalar Laplacian of R. This is the SECOND-order trace-commute for the Ricci field — the same shape as the discharged first-order `TraceMetricVariationDerivAt` and its second-order Hessian analogues (predicates-30's `covTensor2SecondDerivAt_timeDeriv_Hslot_trace_eq_hessianAt` pattern, applied to the canonical Ricci field instead of timeDerivAt; the canonical Ricci regularity instances from predicates-41/42 supply the differentiability; the Gram route is the tool).
2. **`RicciActionRicciTraceAt`**: metric trace of the Ricci-endomorphism action on Ric = `2·|Ric|²` — finite-dimensional linear algebra per fiber (`ricciEndoAt` composition traces — `ricciNormSqAt_eq_trace` machinery in RicciNorm.lean; likely short).
3. Chain: both obligations → the wired trace-consistency lemma becomes UNCONDITIONAL (modulo honest classes) → the Ricci-evolution target statement is fully validated against the proven scalar theory. Update the roadmap: subtask 1 (the Ricci-identity commutation campaign) becomes the sole remaining content for `SatisfiesRicciEvolutionAt`.

Do (2) first (short). Standing sanity checks. Exact-goal-state on failure. No sorry/axiom. `lake build Poincare.Global.ScalarVariation Poincare.Global.ScalarEvolution`, report names.
