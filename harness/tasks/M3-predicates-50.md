Read harness/worker_contract.md first and obey it strictly.

# Task M3-predicates-50: group-1 wiring + group-3 → assemble the cyclic Bianchi

Read `harness/reports/M3-predicates-49_progress.md` (contains the exact displayed remaining cancellation). On main: group 1 raw (`closedConnectionEntry_mixed_second_cyclic_cancel`), group 2 (torsion-free bracket alignment + cyclic output-slot wrapper), the Koszul expansion + correction definitions, and the assembly consumers.

Remaining, per the report (each its own commit):
1. **Group-1 wiring**: connect the raw mixed-second-derivative cancellation through the `covTensor2DerivAt`-shaped terms inside `closedCurvatureDefExpansionAt` — unfold covTensor2DerivAt (flat derivative + Christoffel corrections BY DEFINITION), route the flat parts to the raw group-1 lemma and push the Christoffel corrections into the group-2/3 piles (pure bookkeeping: `simp only [covTensor2DerivAt]`-style unfolds + sum reorganization + the already-proven alignment wrappers).
2. **Group 3**: the metric/bracket correction block cancels cyclically — after groups 1-2 absorb their pieces, the residue should close by the slot-cancellation lemmas + `ring`/`abel` (the model's endgame; if a residue term genuinely doesn't cancel, PASTE THE EXACT RESIDUE in the report — at this granularity a non-cancelling term likely signals a sign/slot bookkeeping mismatch in one of the definitions, worth exact diagnosis).
3. **Assemble** the displayed equation → `eventually_closed_cyclic_second_bianchi_of_inner_sum` fires → **CYCLIC SECOND BIANCHI**.
4. If budget: hMiddle → the full chain → **HAMILTON THEOREM** + historic done-report.

Standing sanity checks. Exact-goal-state (literal residues) on failure. No sorry/axiom. `lake build Poincare.Global.ScalarVariation Poincare.Global.ScalarEvolution`, report names.
