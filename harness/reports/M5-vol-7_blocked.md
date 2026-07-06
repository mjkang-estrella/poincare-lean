# M5-vol-7: blocked on the quantitative lower chart comparison

Task: Goal 10, prove the local anti-Lipschitz inverse-chart lower bound and
derive unconditional volume positivity in a new `Poincare.Global.VolumePositivity`
module.

## Status

No Lean module was added.  I did not edit existing Lean files or add a vacuous
`VolumePositivity.lean`, because the required anti-Lipschitz theorem remains
unproved and the worker contract forbids placeholder proofs.

The downstream payoff is already available from `Poincare.Global.NormalizedFlow`:

```lean
theorem volumeMeasure_univ_ne_zero_of_localChartAntilipschitzLowerBound
    [Nonempty M] (g : ClosedSmoothRiemannianMetric n M)
    (hlower : LocalChartAntilipschitzLowerBound (n := n) (M := M) g) :
    volumeMeasure g Set.univ ≠ 0
```

## Isolated blocker

The single missing statement is the per-anchor quantitative lower comparison
unfolding `LocalChartAntilipschitzLowerBound`:

```lean
theorem exists_extChartAt_symm_antilipschitz_ball
    (g : ClosedSmoothRiemannianMetric n M) (x : M) :
    ∃ r : ℝ, 0 < r ∧
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

This is exactly the finite linear lower bound needed by the Hausdorff-measure
argument.  Mathlib exposes the relevant ingredients:

```lean
eventually_enorm_mfderiv_extChartAt_lt
eventually_enorm_mfderivWithin_symm_extChartAt_lt
setOf_riemannianEDist_lt_subset_nhds
Manifold.exists_lt_locally_constant_of_riemannianEDist_lt
```

but I found no packaged theorem giving the required pairwise finite
anti-Lipschitz constant for inverse charts.  The remaining formal work is to
quantify the lower path-length argument: bound the chart derivative on a closed
chart neighborhood, prove short paths between points of a smaller chart ball
remain in that neighborhood, and combine this with a diameter/margin case split
to get one constant `K`.

## Verification

Required build command:

```text
lake build Poincare.Global.VolumePositivity
```

Actual result:

```text
✖ [2/2] Running Poincare.Global.VolumePositivity
error: no such file or directory (error code: 4294967294)
  file: /Users/mjkang/Develop/poincare-wt-M5-vol-7/Poincare/Global/VolumePositivity.lean
Some required targets logged failures:
- Poincare.Global.VolumePositivity
error: build failed
```
