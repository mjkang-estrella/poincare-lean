# MaximumPrinciple Lean 4.33.1 compatibility preflight

Base: `18e6d0225ba98f9aa4cf706f41e0daaf9ef4c46f`

Cwd: `/Users/mjkang/.codex/worktrees/upstream-integration-433/poincare`

Command: `LEAN_NUM_THREADS=1 lake env lean Poincare/MaximumPrinciple.lean`

Compiler exit: 1. Duration: 9.875300 seconds. Working tree clean before and after. HEAD and scoped source SHA256 unchanged.

First obstruction is `Poincare/MaximumPrinciple.lean:37:4`, in `RicciFlow.ode_comparison_nonpos`, at:

```lean
simpa [hv] using h1.mul (hd s hs)
```

Lean reports the resulting `HasDerivAt` uses `Real.normedCommRing.toAddCommGroup` and `(NormedAlgebra.toNormedSpace ℝ).toModule`, while the expected type uses `Real.instAddCommGroup` and `Semiring.toModule`. The full expanded actual and expected types are the first diagnostic in `compiler.log`. This is a concrete proof elaboration obstruction after imports load. No mathematical hypotheses or targets were modified.

The complete transcript contains 13 error diagnostics; later errors are retained but no repair was attempted. Scoped forbidden-token scan found no matches, with rg exit 1. `git diff --check` exited 0. Scoped final diff is empty.

Only evidence artifacts were written. No source edits, lake builds, dependency operations, server operations, or reversions. This preflight does not discharge independent Hamilton convergence or smoothability.
