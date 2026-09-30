# Riemann curvature Lean 4.33.1 preflight

Result: unchanged success. No Lean API/proof obstruction.

Cwd: `/Users/mjkang/.codex/worktrees/upstream-integration-433/poincare`

Base SHA before and after: `18e6d0225ba98f9aa4cf706f41e0daaf9ef4c46f`

Toolchain: `leanprover/lean4:v4.33.1`. Mathlib: `0df444a360eaa60ab8c11dca51a86af692955474`.

Command: `LEAN_NUM_THREADS=1 lake env lean Poincare/RiemannCurvatureOperator.lean`.

Lean exited 0 in 9.06 seconds. The only diagnostics are warnings at lines 129 and 154: `extDerivFun` is deprecated in favor of `mvfderiv`, and those simp arguments are unused.

The scoped forbidden-token scan exited 1 with no matches. A redundant repeat used the identical valid pattern and also returned no matches. The earlier explanation about an invalid initial pattern was mistaken. It is corrected by `scan-clarification.json`; all original evidence remains preserved.

`git diff --check` exited 0. The checkout was clean before and after, with identical base SHA and scoped source SHA256. `scoped.diff` is empty.

No source edits, proof repairs, full builds, dependency/server operations, or endpoint checks occurred. This scoped compatibility check does not discharge independent Hamilton or smoothing obligations and does not certify root integration or final theorem completion.

Stop condition reached. Root may review this preserved result before selecting any further gate.
