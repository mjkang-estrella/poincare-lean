# M5-vol-3: blocked strict partial

Task: Goal 10, prove finiteness of `volumeMeasure g` on closed manifolds.

## Result

Strict partial.  I did not prove the frozen target

```lean
theorem volumeMeasure_isFiniteMeasure
    (g : ClosedSmoothRiemannianMetric n M) :
    MeasureTheory.IsFiniteMeasure (volumeMeasure g)
```

because the necessary pairwise local chart-distance comparison is not present
in the repo or in the imported Mathlib Riemannian API.

## Delivered file

Added `Poincare/Global/VolumeFiniteness.lean`.

Proven reductions:

- `hausdorffMeasure_image_lt_top_of_lipschitzOnWith`
  - A Lipschitz image of a set with finite Hausdorff `d`-measure has finite
    Hausdorff `d`-measure.
- `closedSmoothModel_hausdorffMeasure_lt_top`
  - Compact subsets of `ClosedSmoothModel n = EuclideanSpace ℝ (Fin n)` have
    finite `μH[n]`, using Mathlib's finite-dimensional Hausdorff/Haar instance.
- `volumeMeasure_isFiniteMeasure_of_forall_finiteAt_nhds`
  - Local finiteness of `(μH[n] : Measure M)` under `g.toMetricSpace` implies
    `IsFiniteMeasure (volumeMeasure g)` by compactness.
- `volumeMeasure_finiteAt_nhds_of_compact_lipschitz_chart_image`
  - A compact coordinate set whose inverse chart image is a neighborhood and
    whose inverse chart is Lipschitz gives finite measure at that neighborhood.
- `volumeMeasure_isFiniteMeasure_of_compact_lipschitz_chart_images`
  - The final theorem follows from the local compact inverse-chart Lipschitz
    input at every point.

## Existing Mathlib support found

Measure side:

- `LipschitzOnWith.hausdorffMeasure_image_le`
- `LipschitzWith.hausdorffMeasure_image_le`
- finite-dimensional `IsAddHaarMeasure (μH[finrank ℝ E])`, giving finite
  `μH[finrank ℝ E]` on compact subsets of finite-dimensional normed spaces
- `IsLocallyFiniteMeasure` -> `IsFiniteMeasureOnCompacts`
- `CompactSpace.isFiniteMeasure`

Riemannian path-length side:

- `Manifold.eventually_riemannianEDist_le_edist_extChartAt`
  gives a one-point estimate
  `riemannianEDist I x y ≤ C * edist (extChartAt I x x) (extChartAt I x y)`
  near `x`.
- `Manifold.eventually_enorm_mfderivWithin_symm_extChartAt_lt`
  gives the derivative bound for inverse extended charts used inside the
  proof of the one-point estimate.

The one-point estimate is not enough for Hausdorff image control.  The
Hausdorff Lipschitz API needs a pairwise bound for all pairs in one coordinate
set.

## Single missing comparison lemma

Precise target input:

```lean
theorem exists_compact_lipschitz_extChartAt_symm_image_nhds
    (g : ClosedSmoothRiemannianMetric n M) (x : M) :
    ∃ s : Set (ClosedSmoothModel n),
      IsCompact s ∧
      (extChartAt (closedSmoothModelWithCorners n) x).symm '' s ∈ 𝓝 x ∧
      ∃ K : ℝ≥0,
        letI : MetricSpace M := g.toMetricSpace
        LipschitzOnWith K
          (extChartAt (closedSmoothModelWithCorners n) x).symm s
```

Suggested route:

1. Install `g.toRiemannianBundle`, `g.toIsContinuousRiemannianBundle`, and the
   induced emetric/metric context as in `RiemannianContext.lean`.
2. Use `eventually_enorm_mfderivWithin_symm_extChartAt_lt` to choose a small
   convex coordinate ball around `extChartAt I x x` on which the derivative of
   `(extChartAt I x).symm` is bounded.
3. For arbitrary coordinate points `u v` in that ball, push the Euclidean line
   segment from `u` to `v` through `(extChartAt I x).symm`.
4. Bound the resulting `pathELength` by the derivative bound times
   `edist u v`, following the internal proof pattern of
   `eventually_riemannianEDist_le_edist_extChartAt`.
5. Convert `edist`/`riemannianEDist` to the `g.toMetricSpace` Lipschitz
   statement needed by `LipschitzOnWith.hausdorffMeasure_image_le`.

## Verification

Command:

```text
lake build Poincare.Global.VolumeFiniteness
```

Result:

```text
✔ [2715/2715] Built Poincare.Global.VolumeFiniteness (2.8s)
Build completed successfully (2715 jobs).
```
