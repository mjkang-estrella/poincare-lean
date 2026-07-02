Read harness/worker_contract.md first and obey it strictly.

# Task M3-predicates-48: the displayed cyclic cancellation (three groups, pure algebra)

Read `harness/reports/M3-predicates-47_progress.md`. ONE displayed equation remains for the cyclic second Bianchi (then two routine steps to the Hamilton theorem):

`Σ_cyclic closedCurvatureDefExpansionAt g y (v,u,w | u,w,v | w,v,u) z q − Σ_cyclic closedCurvatureCovDerivAtCorrectionAt (...) = 0`

Unfold both definitions (predicates-44/46 — explicit finite combinations of: second-connection-derivative entries, Γ·∂Γ entries, bracket entries, metric corrections) and prove the three named cancellation groups, ONE COMMIT EACH:
1. **Mixed second-connection derivatives**: the ∂∂-entry terms pair across the cyclic sum; each pair cancels by the closed Schwarz lemmas (`extDerivFun` mixed symmetry — on main; the model `coord_second_bianchi` shows which index pairs).
2. **Torsion-free Γ·∂Γ alignment**: `g.leviCivita` slot symmetry on extend sections (`leviCivita_torsionFreeAt` + the extend-calculus) aligns the first-order product terms into cancelling cyclic pairs.
3. **Correction block**: the metric/bracket corrections cancel cyclically (bookkeeping; `ring`/`abel` after the rewrites).

Then assemble the displayed equation, fire `eventually_closed_cyclic_second_bianchi_of_inner_sum` (on main) → the CYCLIC SECOND BIANCHI lands. If budget: hMiddle (Gram-contraction bookkeeping) → the full Hamilton chain → historic done-report.

Per-group partial credit fully accepted — land group 1 minimum. Exact-goal-state (the literal unfolded goal) on failure. No sorry/axiom. `lake build Poincare.Global.ScalarVariation`, report names.
