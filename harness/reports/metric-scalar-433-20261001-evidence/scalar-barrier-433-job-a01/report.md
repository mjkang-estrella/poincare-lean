# Scalar Riccati barrier Lean 4.33 compatibility Job

Status: ready for orchestrator review. No merge or task acceptance performed.

Base: `757d0dda020470783afef7b0edfe1601da00274c`.
Commit: `a15e50291dfb2d7cbf026ce129ca37bc07ecf4ab`.
Branch: `codex/scalar-barrier-433-a01`.
Cwd: `/Users/mjkang/.codex/worktrees/scalar-barrier-433/poincare`.

The two approved proof bodies are repaired. `hasDerivWithinAt_neg_inv` uses `convert!` to resolve the original real derivative instances. In `negative_reciprocal_growth_bound`, the negative-reciprocal continuity proof uses only local-definition and pointwise inverse/negation simplification, with expected-type elaboration via `using!`. No public type, hypothesis, import, data, norm, time domain, right-derivative scope, sign requirement, initial bound or junction-jump condition changed.

Attempt 01 passes every frozen gate. Its source, diff, exact argv/cwd/base SHA, outputs, exit statuses and phase timings are preserved under `attempt-01`.

Passed gates:

- Scoped Lean elaboration, exit 0.
- `lake build Poincare.Global.ScalarCurvatureBarrier`, exit 0.
- `FrozenMigrationProbe.lean`, exit 0. All sixteen exact original declaration types/universe arities pass. Every named declaration's dependency closure passes safe/total and allowed-foundational-axiom checks.
- Whole-file byte guard, exit 0: `PRESERVED_SCALAR_BARRIER_ALL_TYPES_DATA_OTHER_PROOFS`.
- Scoped forbidden-token scan, exit 1 with no matches.
- `git diff --check`, exit 0.

Final worktree is clean. Final source bytes equal the successful attempt snapshot. The commit changes one file with 3 insertions and 2 deletions, confined to the two approved proof bodies. Every other source byte is preserved.

This restores the original scalar and segmented Riccati comparison APIs for their supplied scalar-minimum/surgery consumers. It constructs no geometric maximum-principle, physical flow, surgery history or independent Hamilton input. The smoothability core is unchanged. No retained-root or final completion gate was run here.

Next action: the orchestrator independently replays this commit from the recorded base and reruns the frozen acceptance gate before deciding acceptance or integration.
