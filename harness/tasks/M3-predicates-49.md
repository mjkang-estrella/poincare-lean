Read harness/worker_contract.md first and obey it strictly.

# Task M3-predicates-49: cancellation groups 2-3 + wiring → the cyclic Bianchi

Read `harness/reports/M3-predicates-48_progress.md`. On main: group 1 raw form proven (`closedConnectionEntry_mixed_second_cyclic_cancel` — the Schwarz cyclic cancellation). Remaining for the displayed equation:
1. **Wiring**: align group 1's raw mixed-second-derivative form with the `covTensor2DerivAt`-shaped terms inside `closedCurvatureDefExpansionAt` (unfold-and-match bookkeeping — the covTensor2DerivAt terms ARE flat derivative + Christoffel corrections by definition; peel the corrections into group 2's pile).
2. **Group 2**: torsion-free alignment of the first-order Γ·∂Γ/field-slot terms — `leviCivita_torsionFreeAt` on extend sections gives the slot symmetry; the cyclic sum pairs them off (`ring` after the symmetry rewrites).
3. **Group 3**: the metric/bracket correction block cancels cyclically (bookkeeping + `abel`).
4. **Assemble** the displayed equation → fire `eventually_closed_cyclic_second_bianchi_of_inner_sum` (on main) → **CYCLIC SECOND BIANCHI LANDS**.
5. If budget: hMiddle (the middle curvature-divergence trace = `closedRicciDivergenceTraceAt` — Gram contraction bookkeeping) → `eventually_closed_twice_contracted_bianchi_trace_of_second_bianchi` → `ClosedContractedBianchiAt.of_closed_trace_contraction_canonical` → **HAMILTON THEOREM** — final wrappers + historic done-report.

Per-group commits; group-2 minimum. Exact-goal-state (literal unfolded goal) on failure. No sorry/axiom. `lake build Poincare.Global.ScalarVariation Poincare.Global.ScalarEvolution`, report names.
