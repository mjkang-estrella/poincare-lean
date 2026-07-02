Read harness/worker_contract.md first and obey it strictly.

# Task M3-predicates-51: the group-3 residue → cyclic Bianchi → (if budget) THE HAMILTON THEOREM

Read `harness/reports/M3-predicates-50_progress.md` (or `_done`) — it contains the EXACT remaining residue equation (unfolded), everything else of the cyclic cancellation being proven: groups 1-2 done, the Schwarz block cancelled, the reduction theorem `closedCurvatureDefExpansionAt_cyclic_sub_corrections_eq_residue_sub_corrections` on main.

Remaining: the cyclic residue equation —
`Σ_cyclic closedCurvatureDefExpansionResidueAt = Σ_cyclic closedCurvatureCovDerivAtCorrectionAt`

Unfold both (the report shows the unfolded shapes): first-order connection/bracket/metric terms only — NO second derivatives left. Match term groups using: torsion-free slot symmetry (the group-2 alignment wrappers), the slot-cancellation lemmas, metric compatibility (`spatialMetricDerivAt_eq_leviCivita`), and `ring`/`abel`. If a term genuinely survives, paste it exactly (sign/slot mismatch diagnosis — check the correction definition's orientation against the expansion's before concluding anything is wrong).

Then:
1. Assemble → `eventually_closed_cyclic_second_bianchi_of_inner_sum` → **CYCLIC SECOND BIANCHI PROVEN**.
2. **hMiddle**: the middle curvature-divergence trace = `closedRicciDivergenceTraceAt` (Gram-contraction bookkeeping; the raw contraction lemmas from the predicates-36 scaffold).
3. **THE CHAIN**: `eventually_closed_twice_contracted_bianchi_trace_of_second_bianchi` → `ClosedContractedBianchiAt.of_closed_trace_contraction_canonical` (mind its two scalar-regularity side hypotheses — discharge from g's smoothness via the ContMDiff machinery) → **`ClosedContractedBianchiAt` DISCHARGED** → state `satisfiesHamiltonScalarEvolutionAt_of_ricciFlow` FINAL + program form → HISTORIC done-report (this completes the two-day Hamilton campaign).

Standing sanity checks. Exact-goal-state on failure. No sorry/axiom. `lake build Poincare.Global.ScalarVariation Poincare.Global.ScalarEvolution`, report names.
