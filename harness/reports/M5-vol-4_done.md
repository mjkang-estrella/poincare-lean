# M5-vol-4: done

Task: Goal 10, inverse-chart Lipschitz comparison and volume finiteness.

## Delivered

Added `Poincare/Global/VolumeFinitenessComparison.lean`.

Proven:

- `exists_compact_lipschitz_extChartAt_symm_image_nhds`
  - This is the comparison lemma isolated in `M5-vol-3_blocked.md`.
  - It uses a compact closed coordinate ball around
    `(extChartAt (closedSmoothModelWithCorners n) x) x`.
  - The proof follows the Mathlib segment-path pattern from
    `eventually_riemannianEDist_le_edist_extChartAt`: derivative bound for the
    inverse chart, line segment in the chart, `pathELength` bound, and
    conversion through the induced Riemannian metric.
- `volumeMeasure_isFiniteMeasure`
  - Feeds the comparison lemma into
    `volumeMeasure_isFiniteMeasure_of_compact_lipschitz_chart_images`.

Spelling adaptation: the comparison lemma keeps the exact public name and
statement shape from the blocked report.  A private helper additionally exposes
the closed-ball radius and Lipschitz constant used to build the compact witness.

## Verification

Command:

```text
lake build Poincare.Global.VolumeFinitenessComparison
```

Result:

```text
✔ [2716/2716] Built Poincare.Global.VolumeFinitenessComparison (3.2s)
Build completed successfully (2716 jobs).
```
