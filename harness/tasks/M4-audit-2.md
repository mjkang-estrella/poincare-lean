Read harness/worker_contract.md first and obey it strictly.

# Task M4-audit-2: witness the regularity bundles (audit gap items 1 + 6)

Read `harness/reports/M4-audit-1_report.md`. The audit found the M4 chain conditional on regularity bundles, most suspiciously `ClosedRicciFlowExtensionRegularAt` (global C² of canonical extension fields) with NO named witness. This task discharges the two highest-value honesty items:

1. **Item 1 — the static witness**: prove `ClosedRicciFlowExtensionRegularAt` (and the other bundle members the audit lists: hRaise, scalar/Ricci-norm C², quotient/gradient differentiability) for the STATIC RICCI-FLAT flow (`gt t = g` with g Ricci-flat — the `isClosedRicciFlowSolutionAt` static instance from the goal-2 campaign). On a static flow the time-regularity is trivial (constant families) and the spatial regularity reduces to the canonical instances ALREADY ON MAIN (the C²-canonical machinery from the M4-prep campaign — `closedLeviCivitaConnection_contMDiff₂`, the CovTensor2ExtContMDiffAt canonical lemmas). Deliver `closedRicciFlowExtensionRegularAt_static_ricciFlat` (or per-member witnesses) — proving the bundles are INHABITED, hence the headline theorems non-vacuous.
2. **Item 6 — the ε hygiene**: add the `0 < ε` guard variant of `hamilton_eigenvalue_pinching_floor_preserved` (or document why the unguarded form is preferred) — one small commit.
3. If budget allows, item 2: bundle the repeated hypotheses into a named `RicciFlowRegularityPackage` structure + constructor from the static witness (reduces future task-spec noise).
4. Report: the updated honest-strength assessment (which headline theorems are now witnessed-non-vacuous).

Standing protocols. No sorry/axiom. BUILD NOTE: patience. `lake build Poincare.Global.ScalarEvolution Poincare.Global.ScalarVariation`, report names.
