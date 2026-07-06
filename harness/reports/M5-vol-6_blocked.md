# M5-vol-6: blocked with verified strict partial

Task: Goal 10, normalized Ricci flow statement plus volume positivity.

## Delivered

Added `Poincare/Global/NormalizedFlow.lean` without editing any existing Lean
module or `Poincare.lean`.

Normalized-flow RHS:

```lean
def normalizedRicciFlowRHSAt
    (g : ClosedSmoothRiemannianMetric n M) (x : M)
    (u w : TangentSpace (closedSmoothModelWithCorners n) x) : ℝ :=
  -2 * g.ricciAt x u w +
    (2 / (n : ℝ)) * meanScalar g * g.inner x u w
```

Proved:

```lean
theorem normalizedRicciFlowRHSAt_symm

theorem normalizedRicciFlowRHSAt_sub_neg_two_ricciAt
```

Added the section-tested normalized-flow predicate:

```lean
structure IsClosedNormalizedRicciFlowSolutionAt
    (gt : ℝ → ClosedSmoothRiemannianMetric n M) (t₀ : ℝ) (x : M) : Prop
```

It mirrors `IsClosedRicciFlowSolutionAt`: it stores the Levi-Civita clause and
tests the time derivative against `ClosedC2TangentField`s and
`CovariantDerivative.DerivRegularAt`, with RHS

```lean
-2 * CovariantDerivative.ricciTraceAt (gt t₀).leviCivita hreg w
  + (2 / (n : ℝ)) * meanScalar (gt t₀) * (gt t₀).inner x (Z x) w
```

Bridge and relation lemmas:

```lean
theorem normalizedRicciFlow_traceRHS_eq_normalizedRicciFlowRHSAt

theorem isClosedNormalizedRicciFlowSolutionAt_timeDerivAt

theorem isClosedNormalizedRicciFlowSolutionAt_timeDerivAt_sub_ricciFlowRHS

theorem isClosedRicciFlowSolutionAt_of_isClosedNormalizedRicciFlowSolutionAt_of_meanScalar_eq_zero
```

Einstein static check:

```lean
theorem isClosedNormalizedRicciFlowSolutionAt_const_of_forall_isEinsteinAt
    (g : ClosedSmoothRiemannianMetric n M) {lam : ℝ}
    (hn : (n : ℝ) ≠ 0)
    (hEin : ∀ y : M, g.IsEinsteinAt lam y)
    (hvol : volumeMeasure g Set.univ ≠ 0)
    (t₀ : ℝ) (x : M) :
    IsClosedNormalizedRicciFlowSolutionAt (fun _ : ℝ ↦ g) t₀ x
```

This proves the intended algebraic cancellation
`-2 * lam + (2 / n) * (n * lam) = 0` under the explicit nonzero-dimension
hypothesis.

## Volume positivity boundary

The unconditional theorem

```lean
volumeMeasure g Set.univ ≠ 0
```

for nonempty closed `M` is not completed.  Mathlib supplies the Hausdorff
lower-bound theorem
`AntilipschitzWith.le_hausdorffMeasure_image`, and the module proves the
downstream nonzero-volume consequence from one isolated missing comparison:

```lean
def LocalChartAntilipschitzLowerBound
    (g : ClosedSmoothRiemannianMetric n M) : Prop :=
  ∀ x : M, ∃ r : ℝ, 0 < r ∧
    ∃ K : ℝ≥0,
      letI : MetricSpace M := g.toMetricSpace
      AntilipschitzWith K
        (fun y :
            {y : ClosedSmoothModel n //
              y ∈ Metric.ball
                ((extChartAt (closedSmoothModelWithCorners n) x) x) r} =>
          (extChartAt (closedSmoothModelWithCorners n) x).symm
            (y : ClosedSmoothModel n))
```

Proved downstream lemmas:

```lean
theorem closedSmoothModel_hausdorffMeasure_ball_pos

theorem volumeMeasure_univ_ne_zero_of_localChartAntilipschitzLowerBound
```

The missing geometric work is the inverse chart lower metric comparison:
Euclidean chart distance is bounded above by a constant times the induced
Riemannian distance on a small chart ball.  The existing
`VolumeFinitenessComparison.lean` machinery proves the opposite Lipschitz
direction for finiteness.

## Verification

Placeholder scan:

```text
rg -n "\b(sorry|admit|axiom|native_decide)\b" Poincare/Global/NormalizedFlow.lean
```

Result: no matches.

Whitespace check:

```text
git diff --check -- Poincare/Global/NormalizedFlow.lean
```

Result: no output.

Direct Lean check:

```text
lake env lean Poincare/Global/NormalizedFlow.lean
```

Result: success, no output.

Required build:

```text
lake build Poincare.Global.NormalizedFlow
```

Result:

```text
✔ [2943/2943] Built Poincare.Global.NormalizedFlow (4.3s)
Build completed successfully (2943 jobs).
```

The build replayed dependencies and emitted pre-existing lint warnings in
earlier modules; `Poincare.Global.NormalizedFlow` built successfully.
