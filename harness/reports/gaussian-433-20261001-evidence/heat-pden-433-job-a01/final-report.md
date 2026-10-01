# HeatKernelPDEn proof-only worker result

Worker result: blocked under the frozen three-distinct-attempt stop condition. No commit, acceptance, or merge was performed.

Base commit: `681e24e8fedf59c21b71747e90835567dc790e43`.
Worktree: `/Users/mjkang/.codex/worktrees/heat-pden-433/poincare`.
Branch: `codex/heat-pden-433-a01`.

Only the approved proof bodies of `hasFDerivAt_neg_norm_sq_div` and `iteratedFDeriv_two_exp_neg_norm_sq_div_apply` differ. Scope guard passed with `PRESERVED_GAUSSIAN_TYPES_DATA_PRIVATE_OTHER_PROOFS`; all surrounding imports, headers, private proofs, data, and other public proofs remain byte-identical to the task snapshot.

The first derivative repair changes `convert` to `convert!`. Its exact import/header/body compile in `strongest-partial.lean`, exit 0. This partial check does not verify the full module or all six frozen declarations.

The remaining resisting goal after continuous linear-map evaluation is:

```lean
Real.exp (-‖x‖ ^ 2 / (4 * t)) * (-(1 / (2 * t)) * ((innerSL ℝ) v) v) +
  Real.exp (-‖x‖ ^ 2 / (4 * t)) * (-(1 / (2 * t)) * ((innerSL ℝ) x) v) *
    (-(1 / (2 * t)) * ((innerSL ℝ) x) v) =
  Real.exp (-‖x‖ ^ 2 / (4 * t)) *
    (⟪x, v⟫_ℝ ^ 2 / (4 * t ^ 2) - ‖v‖ ^ 2 / (2 * t))
```

`rw [real_inner_self_eq_norm_sq]` cannot match the left-hand `innerSL` evaluation. The original `innerSL_apply_apply` rewrite remained unused in a01 and a02; `simp!` in a03 removes the unused-argument warning but leaves this goal.

Attempts were distinct:

- a01 used `convert!` and the canonical map-application simp list, retaining the old `ring_nf/change` structure. The second body failed at `change` after scalar normalization.
- a02 used `dsimp only`, the same simp list, and direct inner-self/field/ring arithmetic. The vector evaluations and `innerSL` evaluations remained.
- a03 used `dsimp` and `simp! only`; vectors reduced, but `innerSL` evaluations remained. The third attempt reached the frozen stop condition.

Each failed compiler transcript and source is preserved. Each edited attempt also passed `git diff --check` and the no-hit token scan, whose exit 1 is the intended pass. The final scope guard and those scans pass. The final patch is `final-worker.patch`.

Scoped Lake build and frozen declaration probe were not run because direct full-module compilation fails. A probe without a successful build would inspect stale compiled output.

Exact next action: independently inspect `attempt-a03/stdout.log`, the map/coercion instance arguments, and `final-worker.patch`; freeze a successor attempt if additional proof search is appropriate. This result makes no independent universal Hamilton-input or convergence claim and no project completion claim.
