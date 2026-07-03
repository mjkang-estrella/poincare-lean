Read harness/worker_contract.md first and obey it strictly.

# Task M3-predicates-54: the output-connection product-rule block (route-2 bridge, 4 steps)

Read `harness/reports/M3-predicates-53_blocked.md` — its "Next step" section IS this task's plan. On main: bracket terms are DEAD (neighborhood vanishing), the corrected second-directional cancellation exists, and the residual goal is exactly the output-connection derivative block.

Execute the 4 steps (each its own commit):
1. Expand the six output-connection derivative terms using the existing corrected second-directional cancellation (the report names the tool).
2. Package the resulting cyclic `covTensor2DerivAt (closedIteratedConnectionEntryFieldAt ...)` block.
3. Prove that block equals the remaining correction-side iterated terms (slot symmetry + the alignment wrappers; if a pair genuinely differs, paste the exact pair).
4. `ring_nf`/`abel` closes `closedCurvatureDefExpansionResidueAt_cyclic_eq_correction_cyclic` → the displayed residue equation → `eventually_closed_cyclic_second_bianchi_of_inner_sum` fires → **CYCLIC SECOND BIANCHI**.

Then the endgame chain (if budget): hMiddle (Gram-contraction bookkeeping) → `eventually_closed_twice_contracted_bianchi_trace_of_second_bianchi` → `ClosedContractedBianchiAt.of_closed_trace_contraction_canonical` (discharge its two scalar side hypotheses from g's smoothness) → **`satisfiesHamiltonScalarEvolutionAt_of_ricciFlow` — THE HAMILTON THEOREM** + historic done-report.

Standing sanity checks. Exact-goal-state on failure. No sorry/axiom. `lake build Poincare.Global.ScalarVariation Poincare.Global.ScalarEvolution`, report names.
