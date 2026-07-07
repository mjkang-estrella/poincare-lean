# M5-rigid-110 blocked: final selector radius floors close, scalar Aop shrink still missing

## Outcome

Added `Poincare/Global/FinalSelector.lean`.  No existing Lean files were edited,
including `Poincare.lean`.

The new module proves and exports the quantitative selector pieces that can be
closed from a new file using the current public API:

```lean
Poincare.FinalSelector.speedPinnedRadiusBound
Poincare.FinalSelector.speedPinnedMembershipRadius_le_bound_of_abs_le
Poincare.FinalSelector.coeff_mul_time_le_half_of_le_inv_two_mul_add_one
Poincare.FinalSelector.norm_mul_time_le_half_of_le_inv_two_mul_norm_add_one
Poincare.FinalSelector.exists_radius_tuple_of_uniform_center_bound_and_floor
Poincare.FinalSelector.source_transverseTransverse_of_selector_final_bounds
Poincare.FinalSelector.target_transverseTransverse_of_selector_final_bounds
```

The source/target final-bound theorems use the compact center bounds from
`ThreeBounds.lean`, choose a radius floor

```lean
max (qmax * Real.exp (Cgr * T) + qmax)
    (Poincare.FinalSelector.speedPinnedRadiusBound speed qmax)
```

and then feed `TransverseExport` directly.  Therefore the Gronwall radius floor
and speed-pinned membership radius floor are no longer external obligations
once the scalar coefficient-time shrink is supplied.

## Remaining blocker

The full requested curvature-only chain still cannot be completed from the
current public selector API in a new file only.  The remaining scalar short-time
hypothesis is still exactly:

```lean
hcoeffTime : ‖Aop‖ * T ≤ (1 : ℝ) / 2
```

What is missing is a public common-time selector/export for the scalar
norm-system operator, for example a theorem producing:

```lean
∃ Cscalar : ℝ, 0 ≤ Cscalar ∧
  ‖Aop‖ ≤ Cscalar ∧
  Cscalar * T ≤ (1 : ℝ) / 2
```

or equivalently returning `‖Aop‖ * T ≤ 1 / 2` after threading the extra
`T ≤ 1 / (2 * (Cscalar + 1))` min term through the selector.

The coefficient export available from `ThreeBounds.lean` remains:

```lean
∃ C : ℝ, 0 ≤ C ∧
  ∀ q : E3 × E3,
    q ∈ closedBall (extChartAt I3 x₀ x₀, (0 : E3)) (aBase : ℝ) →
      ‖linearizedGeodesicFlowOperator (chartChristoffelField g x₀) q‖ ≤ C
```

That bound is for the linearized geodesic-flow coefficient on `E3 × E3`; the
selector continuation that now has closed radius floors consumes the scalar
norm-system operator:

```lean
Aop : Triple →L[ℝ] Triple
Aop x = (2 * x.2.1, x.2.2 - speed ^ 2 * x.1, -2 * speed ^ 2 * x.2.1)
```

So the remaining obstruction is not the Gronwall/speed-pinned radius
arithmetic.  It is the missing exported bridge from the compact selector
coefficient data to the scalar `Aop` coefficient-time shrink needed by the
final `TransverseExport` continuation.  Consequently, the final
`cartanMap_isLocalIsometry` curvature-only theorem was not stated.

## Verification

- `rg -n '\b(sorry|admit|axiom|native_decide)\b' Poincare/Global/FinalSelector.lean`
  - Result: no matches.
- `git diff --check -- Poincare/Global/FinalSelector.lean`
  - Result: success.
- `lake build Poincare.Global.FinalSelector`
  - Result: success.  The build replayed pre-existing imported-module warnings.
  - Final line from the final rerun:

```text
Build completed successfully (3212 jobs).
```
