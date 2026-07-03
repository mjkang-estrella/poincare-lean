Read harness/worker_contract.md first and obey it strictly.

# Task M4-prep-18: SANCTIONED target correction + trace re-validation + fire the chain

Read `harness/reports/M4-prep-17_blocked.md` (the coefficient-pinned re-derivation) and `M4-prep-16_blocked.md`. ORCHESTRATOR RULING: the frozen `RicciSecondDerivCurvatureCommutationAt` / `SatisfiesRicciEvolutionAt` RHS is corrected (they were stated, never proven; the correction history is preserved). The CORRECT RHS per the pinned derivation:
`roughTensorLaplacianAt + 2·lichnerowiczCurvatureAt − ricciActionOnTensorAt` (= rough − A + Q, the classical Hamilton ΔRic + 2Rm(Ric,·) − 2Ric² form; note Q = 2L was verified on the test pattern).

Deliverables (each its own commit):
1. **Correct the two statements** (version the old ones deprecated-with-comment; ledger-honest). Update the assembly wrappers to the corrected RHS.
2. **Trace re-validation with the moving-metric bookkeeping** (CRITICAL — do this INFORMALLY IN THE REPORT FIRST): the corrected tensor RHS traces to ΔR + tr(2L − A) = ΔR + [2|Ric|² − 2|Ric|²] = ΔR; the PROVEN scalar equation is dR/dt = ΔR + 2|Ric|²; the difference is exactly the moving-metric term: d/dt(tr_g Ric) = tr(∂ₜRic) + ⟨−h, Ric⟩-shape = tr(∂ₜRic) + 2|Ric|² under h = −2Ric. VERIFY this reconciliation precisely against the merged `timeDerivAt`/trace-derivative lemmas (the machinery exists: `traceMetricVariationDerivAt`, the scalar-variation chain) — if the bookkeeping does NOT reconcile, STOP and report (it would mean a residual coefficient error).
3. If reconciled: prove the corrected fold in Lean (the CA trace = A − Q identity, per the pinned derivation), complete the M4-prep-15 assembly against the corrected target, fire `satisfiesRicciEvolutionAt_of_ricciFlow_curvatureCommutation` (updated) → **THE RICCI TENSOR EVOLUTION EQUATION (corrected, classical form)**. Historic done-report + formal trace-consistency corollary with the moving-metric term made explicit.

Standing protocols. No sorry/axiom. `lake build Poincare.Global.ScalarVariation Poincare.Global.ScalarEvolution`, report names.
