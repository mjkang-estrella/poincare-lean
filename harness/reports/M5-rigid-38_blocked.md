# M5-rigid-38 blocked: shifted-base strict derivative

## Status

Blocked.  I added `Poincare/Global/ExponentialStrictAtV.lean` with a verified
shifted-base two-point Taylor estimate, including the chart-Christoffel and
`roundSphereMetric3` closed-ball instances.  I did not prove
`expAt_chart_hasStrictFDerivAt_at`, because the remaining endpoint step still
needs a two-variable Gronwall propagation theorem tying the shifted Taylor
estimate to the `linearizedEndpointCLM` family.

## Verified estimate added

The new non-vacuous estimate is:

```lean
chartChristoffel_geodesicFlowField_uniform_two_point_taylor_at_base_norm_le_closedBall
```

In schematic form, on any closed first-order chart ball, for every `ε > 0`
there is `δ > 0` such that if `x` and `y` are both within `δ` of a shifted
base `base`, then

```lean
‖F y - F x - linearizedGeodesicFlowOperator Γ base (y - x)‖
  ≤ ε * ‖y - x‖
```

where `F = geodesicFlowField (chartChristoffelField g x₀)`.  The generic proof
is `uniform_two_point_taylor_at_base_norm_le_on_compact_convex`, proved from
uniform continuity of `fderiv` on a compact convex set and the mean-value
inequality.

The round-sphere instance is:

```lean
roundSphereMetric3_geodesicFlowField_uniform_two_point_taylor_at_base_norm_le_closedBall
```

## Remaining blocker

The next missing theorem is the endpoint residual propagation:

```lean
∀ c > (0 : ℝ), ∀ᶠ p : E × E in 𝓝 (v, v),
  ‖(α (z₀, τ⁻¹ • p.1) τ).1 -
    (α (z₀, τ⁻¹ • p.2) τ).1 -
    D (p.1 - p.2)‖ ≤ c * ‖p.1 - p.2‖
```

with `D` supplied by the shifted linearized endpoint CLM.  This is exactly the
strict two-variable endpoint remainder needed to transfer from the PL flow to
`expAtChartOpenPartialHomeomorph`.

## Verification

Safety scan:

```bash
rg -n "sorry|axiom|native_decide" Poincare/Global/ExponentialStrictAtV.lean
```

Actual result: no matches.

Build command:

```bash
lake build Poincare.Global.ExponentialStrictAtV
```

Actual result: succeeded.

Final build line:

```text
✔ [2983/2983] Built Poincare.Global.ExponentialStrictAtV (3.2s)
Build completed successfully (2983 jobs).
```
