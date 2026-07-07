# M5-rigid-111 done: scalar Aop bound

## Outcome

Added `Poincare/Global/AopBound.lean`.  No existing Lean files were edited,
including `Poincare.lean`.

The module proves the scalar norm-system operator bound for every
time-independent `Aop : Triple →L[ℝ] Triple` with the speed-generic shape

```lean
Aop x = (2 * x.2.1, x.2.2 - speed ^ 2 * x.1, -2 * speed ^ 2 * x.2.1)
```

using `ContinuousLinearMap.opNorm_le_bound` and componentwise product-norm
estimates.

Exported theorems:

```lean
Poincare.AopBound.speed_normSystem_opNorm_le_of_speed_sq_le
Poincare.AopBound.speed_normSystem_opNorm_le
Poincare.AopBound.speed_normSystem_opNorm_le_of_speed_sq_bound
Poincare.AopBound.unit_normSystem_opNorm_le_four
Poincare.AopBound.exists_speed_normSystem_bound
Poincare.AopBound.speed_normSystem_mul_time_le_half
Poincare.AopBound.speed_normSystem_mul_time_le_half_of_speed_sq_bound
```

The main bound is

```lean
‖Aop‖ ≤ 4 * max (1 : ℝ) (speed ^ 2)
```

and the unit-speed constant-coefficient specialization gives

```lean
‖Aop‖ ≤ 4
```

The time-shrink corollaries produce the selector hypothesis

```lean
‖Aop‖ * T ≤ (1 : ℝ) / 2
```

from an added common-time floor either using the explicit `speed ^ 2` term or
an external upper bound on `speed ^ 2`.

## Verification

- `rg -n '\b(sorry|admit|axiom|native_decide)\b' Poincare/Global/AopBound.lean`
  - Result: no matches.
- `git diff --check -- Poincare/Global/AopBound.lean`
  - Result: success.
- `lake env lean Poincare/Global/AopBound.lean`
  - Result: success.
- `lake build Poincare.Global.AopBound`
  - Result: success.  The build replayed pre-existing imported-module warnings.
  - Final lines:

```text
✔ [3213/3213] Built Poincare.Global.AopBound (2.0s)
Build completed successfully (3213 jobs).
```
