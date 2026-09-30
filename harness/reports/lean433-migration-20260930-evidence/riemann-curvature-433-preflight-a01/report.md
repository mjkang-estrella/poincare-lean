# Riemann curvature Lean 4.33.1 preflight

Result: unchanged success. No Lean API/proof obstruction.

- Cwd: `/Users/mjkang/.codex/worktrees/upstream-integration-433/poincare`
- Base SHA before and after: `18e6d0225ba98f9aa4cf706f41e0daaf9ef4c46f`
- Toolchain: `leanprover/lean4:v4.33.1`
- Mathlib: `0df444a360eaa60ab8c11dca51a86af692955474`
- Command: `LEAN_NUM_THREADS=1 lake env lean Poincare/RiemannCurvatureOperator.lean`
- Lean exit: 0; elapsed: 9.06 seconds
- Lean warnings: deprecated `extDerivFun`, replacement `mvfderiv`, and unused simp argument at source lines 129 and 154.
- Corrected scoped scan: exit 1, no matches if exit 1. Exact argv is preserved in `forbidden-token-scan-corrected.result.json`.
- Initial scan used an invalid escaped pattern. Its original files are retained and superseded by the corrected scan.
- `git diff --check`: exit 0
- Checkout status before/after: clean branch `codex/upstream-integration-433`.
- Scoped source SHA256 before/after identical: `6dc3e6d0d30e708bf288c31d46f7b225139b98a0e797de13ecbf9279c4bd67cc`.
- `scoped.diff` is empty. No source edits, proof repair, full build, dependency/server operations, or endpoint checks occurred.

This scoped compatibility check does not discharge independent Hamilton or smoothing obligations and does not certify root integration or final theorem completion.

Stop condition reached. Root may review this preserved result before selecting any further gate.
