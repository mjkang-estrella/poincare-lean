# M5-geo-36 done

Added `Poincare/Global/UniformNormalRadius.lean` only.  No existing Lean
source file or root import was edited.

## What closed

The module packages the completed per-anchor normal-neighborhood theorem into
actual chosen data:

- `normalCoordinateRadius`
- `normalCoordinateImage`
- `normalCoordinateRadius_pos`
- `injOn_expAt_normalCoordinateRadius`
- `isOpen_normalCoordinateImage`
- `normalCoordinateImage_mem_nhds`
- `mem_normalCoordinateImage_self`

The compact uniformization is the route-(b) Lebesgue-number form:

```lean
theorem exists_uniform_ball_subset_normalCoordinateImage
    [T2Space M] [CompactSpace M] [ConnectedSpace M]
    (g : ClosedSmoothRiemannianMetric n M) :
    letI : MetricSpace M := g.toMetricSpace
    ∃ r > (0 : ℝ), ∀ x : M, ∃ x₀ : M,
      Metric.ball x r ⊆ normalCoordinateImage g x₀
```

The payoff lemma reuses the same uniform radius:

```lean
theorem exists_uniform_common_normalCoordinateImage_of_dist_lt
    [T2Space M] [CompactSpace M] [ConnectedSpace M]
    (g : ClosedSmoothRiemannianMetric n M) :
    letI : MetricSpace M := g.toMetricSpace
    ∃ r > (0 : ℝ), ∀ x y : M, dist x y < r →
      ∃ x₀ : M,
        x ∈ normalCoordinateImage g x₀ ∧
          y ∈ normalCoordinateImage g x₀
```

## Honest boundary

This proves the compact open-cover/Lebesgue-number statement: every sufficiently
small metric ball is contained in some normal-coordinate image, and any two
points at distance `< r` are in one common normal-coordinate image.

It does not claim the stronger same-anchor statement
`Metric.ball x r ⊆ normalCoordinateImage g x` for all `x`.  That stronger form
does not follow from arbitrary per-anchor neighborhood data by compactness
alone; it would need an additional continuity-in-anchor or lower-semicontinuity
statement for the chosen normal radii/images.

## Verification

Command run:

```text
lake build Poincare.Global.UniformNormalRadius
```

Result: success.

Lean reported existing upstream warnings while replaying dependencies, then:

```text
✔ [2845/2845] Built Poincare.Global.UniformNormalRadius (13s)
Build completed successfully (2845 jobs).
```
