# HeatKernelPDEn proof-only successor worker result

Verified commit: `eae832136f97f5aa34a4fd7484d203b55503dd6e`.
Base commit: `681e24e8fedf59c21b71747e90835567dc790e43`.
Worktree: `/Users/mjkang/.codex/worktrees/heat-pden-433/poincare`.
Branch: `codex/heat-pden-433-a01`, clean after commit.
Task `heat-pden-433-preserve`, immutable revision 2. Worker completion is ready for independent orchestrator review; no acceptance or merge was performed.

Only the two approved proof bodies changed. The first derivative uses `convert!` to normalize the conversion instances. The Hessian proof evaluates the continuous linear maps, then uses direct scalar `change` to reduce the actual `innerSL` evaluations to inner products before inner-self and field/ring arithmetic. This successor route succeeds in its first compiler attempt.

All six ordered frozen gates pass:

- Direct full-module Lean elaboration, exit 0.
- Scoped `lake build Poincare.Global.HeatKernelPDEn`, exit 0.
- Frozen exact six public types/universes plus allowed foundational axioms and transitive unsafe/partial checks, exit 0.
- Full surrounding-source guard, exit 0 with `PRESERVED_GAUSSIAN_TYPES_DATA_PRIVATE_OTHER_PROOFS`.
- Token scan, exit 1 with no output, intended pass.
- `git diff --check`, exit 0.

All four frozen definition-file hashes match. All 38 previously sealed job-a01 evidence files remain unchanged. The earlier failed compiler attempts and strongest-partial result are retained there.

The final source, patch, complete compiler/build/probe logs, gate exit codes and timings, commit command output, clean status receipt, context hashes and evidence manifest are preserved in this directory. Patch SHA256: `cb4cc59c84c5b4efb17d8e32c3c5edcde3fc193362a7467ce7a43bd7cb9fbbaf`.

No root/full build or completion audit was run by this worker. The Gaussian data, operators, norms, time and dimension assumptions, all private proofs, and every other source byte are preserved by the source guard. This compatibility repair makes no independent universal Hamilton-flow/convergence or Poincare completion claim.

Exact first action for the orchestrator: independently rerun the revision-2 frozen acceptance commands from the recorded base/commit and inspect the two-proof-body diff before acceptance or serial integration.
