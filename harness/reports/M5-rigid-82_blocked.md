# M5-rigid-82 blocked: uniform linear PL needs a center bound

## Status

Added `Poincare/Global/UniformPL.lean` as the requested new module.  No
existing Lean files were edited, including `Poincare.lean`.

The module proves the linear part that is actually available:

```lean
Poincare.UniformPL.isPicardLindelof_const_linear_uniform_of_center_norm_bound
```

For a time-independent linear vector field `x ↦ A x`, one common
Picard-Lindelöf tuple works for a family of centers once those centers have a
uniform norm bound.  The proof uses the single operator norm for the
Lipschitz field and uses the center bound to discharge `IsPicardLindelof.norm_le`.

It also proves the obstruction for the literal all-scalar oscillator centers:

```lean
Poincare.UniformPL.not_forall_isPicardLindelof_oscillator_scalar_centers
```

At the center `(0,0,c)`, the oscillator vector field
`(2B, C - speed^2 A, -2 speed^2 B)` has middle component `c`.  Therefore the
`norm_le` field cannot be bounded by one finite `LNorm` for all scalar centers
`c`.

## Remaining boundary

The requested hosted package still resists in exactly the same field shape:

```lean
(hplNorm : ∀ w : E3,
  IsPicardLindelof
    (fun _ : ℝ => fun x : ℝ × ℝ × ℝ => Aop x)
    (tmin := tmin) (tmax := tmax) ⟨(0 : ℝ), hzero⟩
    ((0 : ℝ), (0 : ℝ),
      chartGeodesicMetric g x₀ (extChartAt I3 x₀ x₀)
        (T⁻¹ • w) (T⁻¹ • w)) radius rNorm LNorm KNorm)
```

Linearity of the coefficient path supplies a uniform Lipschitz constant, but
Mathlib's `IsPicardLindelof` also contains:

```lean
norm_le : ∀ t ∈ Icc tmin tmax, ∀ x ∈ closedBall x₀ a, ‖f t x‖ ≤ L
```

Since the center in `hplNorm` moves with the quadratic value
`chartGeodesicMetric ... (T⁻¹ • w) (T⁻¹ • w)`, a common finite `LNorm` needs a
uniform bound on those centers, or the scalar ODE must be recentered before
using `IsPicardLindelof`.  I found no exported hosted theorem providing such a
bound for the verbatim `∀ w : E3` package shape, and the all-scalar obstruction
in `UniformPL.lean` shows why coefficient linearity alone is insufficient.

Consequently I did not build the transverse bundle or
`cartanMap_isLocalIsometry` from this package.

## Verification

- `lake build Poincare.Global.UniformPL`
  - Result: success.
  - Final lines:

```text
✔ [3191/3191] Built Poincare.Global.UniformPL (2.3s)
Build completed successfully (3191 jobs).
```

- `rg -n '\b(sorry|admit|axiom|native_decide)\b' Poincare/Global/UniformPL.lean`
  - Result: no matches.
