Read harness/worker_contract.md first and obey it strictly.

# Task M4-audit-4b: CONTINUE the bump-globalization (prior worker died mid-task)

You are continuing in a worktree with WIP from a worker that died on a network error. State: commit `87269318` (bump-globalized tangent extensions, BUILDS) + salvage commit `5523b0f8` (in-progress, DOES NOT BUILD: BumpExtend.lean has a typeclass-resolution failure, and MetricVariation.lean's edits depend on it).

1. Run `lake env lean Poincare/Global/BumpExtend.lean`, read the actual error, and FIX or — if the in-progress direction is wrong — `git revert`/rework the salvage commit (keeping `87269318`).
2. Then complete the ORIGINAL task (read `harness/tasks/M4-audit-4.md`): the global C² cutoff field agreeing with `extend E v` near the anchor, the transferred flow bridge `isClosedRicciFlowSolutionAt_timeDerivAt_eq_neg_two_ricciAt` without global-extend hypotheses, and the static non-vacuity witness. Commit per deliverable.

Standing protocols. No sorry/axiom. BUILD NOTE: patience. `lake build Poincare.Global.MetricVariation Poincare.Global.ScalarVariation Poincare.Global.ScalarEvolution` must pass before done. Report names.
