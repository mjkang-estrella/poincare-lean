Read harness/worker_contract.md first and obey it strictly.

# Task M3-predicates-53: extend-bracket vanishing at the anchor (route 1) → eliminate the nine-term block

Read `harness/reports/M3-predicates-52_blocked.md` (the exact nine-term derivative block + the CONFIRMED re-anchoring observation). Route 1, the cheap decisive atom:

**Lemma A**: `VectorField.mlieBracket I (extend E p) (extend E q) x = 0` at the ANCHOR x (and/or the corresponding statement for whatever bracket-entry fields appear in the nine-term block — read their definitions; the needed vanishing is of the bracket-entries and their pairings AT the anchor, which the re-anchoring observation makes sufficient).

Proof sketch: `extend E p` is (by construction — READ its definition in the repo/Mathlib: likely `fun y => tangent-coordinate-change from x to y applied to p` or the trivialization-constant section) a field whose chart representative in the ANCHOR chart is constant (or has vanishing derivative at the anchor point). mlieBracket in the chart = flat bracket of the representatives = D(rep q)·(rep p) − D(rep p)·(rep q); at the anchor both derivative factors vanish (or cancel) → bracket = 0 at x. Mathlib's `VectorField.mlieBracket_apply`/chart-representation lemmas + the repo's `chartTransportedLeviCivitaSection_mlieBracket_apply_chart` (goal-1 chain — the bracket-through-chart machinery exists!) are the tools.

Then:
1. **Lemma A** (own commit) + any pairing-corollaries the nine-term block needs.
2. **Eliminate the block**: substitute A into the differentiated bracket-entry fields at the re-anchored point → the nine-term block collapses (per the report's confirmed observation) → the displayed residue closes → **CYCLIC SECOND BIANCHI**.
3. Chain (if budget): hMiddle → contracted Bianchi → **HAMILTON THEOREM** + historic done-report.

CAUTION: if the differentiated fields need the bracket to vanish on a NEIGHBORHOOD (not just at the anchor) for their derivative to vanish, that's false in general — check whether the block's derivative terms evaluate the bracket-entries at the anchor only (re-anchoring should ensure this; if not, fall back to route 2 per the report — the coord_second_bianchi replay — and say so precisely).

Standing sanity checks. Exact-goal-state on failure. No sorry/axiom. `lake build Poincare.Global.ScalarVariation Poincare.Global.ScalarEvolution`, report names.
