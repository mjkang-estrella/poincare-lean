# M5-rigid-109 blocked: three bounds exported, scalar selector shrink still not curvature-only

## Outcome

Added `Poincare/Global/ThreeBounds.lean`.  No existing Lean files were edited,
including `Poincare.lean`.

The new module proves and exports the non-vacuous pieces that can be obtained
from the current public API:

```lean
Poincare.ThreeBounds.exists_ball_uniform_linearized_coefficient_bound
Poincare.ThreeBounds.target_exists_ball_uniform_linearized_coefficient_bound
Poincare.ThreeBounds.source_exists_qcenter_bound_on_closedBall
Poincare.ThreeBounds.target_exists_qcenter_bound_on_closedBall
Poincare.ThreeBounds.coefficient_bound_self
Poincare.ThreeBounds.coefficient_norm_nonneg
Poincare.ThreeBounds.coefficient_time_shrink_of_le_div
Poincare.ThreeBounds.source_transverseTransverse_of_selector_three_bounds
Poincare.ThreeBounds.target_transverseTransverse_of_selector_three_bounds
```

The coefficient export is the compact bound that `UniformShrink.lean` extracts
internally for the linearized geodesic-flow coefficient:

```lean
∃ C : ℝ, 0 ≤ C ∧
  ∀ q : E3 × E3,
    q ∈ closedBall (extChartAt I3 x₀ x₀, (0 : E3)) (aBase : ℝ) →
      ‖linearizedGeodesicFlowOperator (chartChristoffelField g x₀) q‖ ≤ C
```

The center exports are source/target compact-ball bounds for both the scalar
quadratic value and the norm-system center:

```lean
∃ qmax : ℝ, 0 ≤ qmax ∧
  (∀ w : E3, w ∈ closedBall (0 : E3) (R : ℝ) →
    |chartGeodesicMetric g x₀ (extChartAt I3 x₀ x₀)
      (T⁻¹ • w) (T⁻¹ • w)| ≤ qmax) ∧
  (∀ w : E3, w ∈ closedBall (0 : E3) (R : ℝ) →
    ‖(((0 : ℝ), (0 : ℝ),
      chartGeodesicMetric g x₀ (extChartAt I3 x₀ x₀)
        (T⁻¹ • w) (T⁻¹ • w)) : Triple)‖ ≤ qmax)
```

The source/target continuation theorems choose `Ccoeff := ‖Aop‖`, instantiate
the compact `Q := qmax`, and feed the resulting data through
`CoefficientShrink.source_transverseTransverse_of_selector_coefficient_shrink`
and its target analogue.

## Remaining blocker

The full requested chain

```text
three bounds → tuple → TransverseExport composite → BlockDiagonal → A/B →
cartanMap_isLocalIsometry
```

still cannot be completed from a new file only.  The public selector API does
not yet export the scalar norm-system shrink and final radius implications as
curvature-only facts.

The verbatim remaining scalar shrink hypothesis at the selector continuation is:

```lean
hcoeffTime : ‖Aop‖ * T ≤ (1 : ℝ) / 2
```

The continuation also still requires the constructed radius to satisfy the
Gronwall and speed-pinned membership implications:

```lean
qmax * Real.exp (Cgr * T) + qmax ≤ (radius : ℝ)
```

and

```lean
∀ w : E3, w ∈ closedBall (0 : E3) (R : ℝ) →
  CartanMap.sourceAnchorChartMetric g x₀ v w = 0 →
    (MembershipBound.speedPinnedMembershipRadius speed
      (chartGeodesicMetric g x₀ (extChartAt I3 x₀ x₀)
        (T⁻¹ • w) (T⁻¹ • w)) : ℝ) ≤ (radius : ℝ)
```

with the analogous target statement.

The key mismatch is that `UniformShrink.lean`'s compact coefficient bound is for
the linearized geodesic-flow operator on `E3 × E3`, while
`CoefficientShrink.lean` consumes the scalar norm-system operator
`Aop : Triple →L[ℝ] Triple`.  This file re-exports the former and uses
`Ccoeff := ‖Aop‖` for the latter, but the selector/common-time theorem does not
yet provide the promised radius-min shrink proving `‖Aop‖ * T ≤ 1/2` and the
radius membership implications.

## Verification

- `lake build Poincare.Global.ThreeBounds`
  - Result: success.  The build replayed pre-existing imported-module warnings.
  - Final lines:

```text
✔ [3211/3211] Built Poincare.Global.ThreeBounds (2.0s)
Build completed successfully (3211 jobs).
```

