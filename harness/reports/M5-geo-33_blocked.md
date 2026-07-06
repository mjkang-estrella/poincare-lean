# M5-geo-33: blocked on the pairwise path-length lower bound

## Status

Added the requested new Lean module:

```text
Poincare/Global/AntilipschitzBallFinal.lean
```

No existing Lean file was edited, including `Poincare.lean`.

## Verified Lean payload

The new module proves the chart-staying half of the final argument:

```lean
theorem edist_extChartAt_endpoints_le_mul_pathELength_of_forall_mem_source_of_enorm_mfderiv_le
```

If a `C¹` path stays in the fixed chart source and the forward chart derivative
is bounded along that path by `C`, then the Euclidean chart displacement of its
endpoints is at most `C * pathELength`.

It also proves the exact lower-bound corollary:

```lean
theorem ofReal_inv_mul_dist_extChartAt_endpoints_le_pathELength_of_forall_mem_source_of_enorm_mfderiv_le
```

This rewrites the same estimate as:

```lean
ENNReal.ofReal (((C : ℝ)⁻¹) *
  dist ((extChartAt I x₀) (γ 0)) ((extChartAt I x₀) (γ 1))) ≤
    Manifold.pathELength I γ 0 1
```

## Remaining blocker

```lean
theorem exists_chart_ball_pairwise_pathELength_lower_bound
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M) :
    letI : RiemannianBundle
        (ClosedSmoothRiemannianMetric.tangentBundle (n := n) (M := M)) :=
      g.toRiemannianBundle
    ∃ r : ℝ, 0 < r ∧
      ∃ K : ℝ≥0, 0 < K ∧
        ∀ (u v :
            {y : ClosedSmoothModel n //
              y ∈ Metric.ball
                ((extChartAt (closedSmoothModelWithCorners n) x₀) x₀) r})
          {γ : ℝ → M},
          ContMDiffOn 𝓘(ℝ) (closedSmoothModelWithCorners n) 1 γ (Icc (0 : ℝ) 1) →
          γ 0 =
            (extChartAt (closedSmoothModelWithCorners n) x₀).symm
              (u : ClosedSmoothModel n) →
          γ 1 =
            (extChartAt (closedSmoothModelWithCorners n) x₀).symm
              (v : ClosedSmoothModel n) →
          ENNReal.ofReal
              (((K : ℝ)⁻¹) *
                dist (u : ClosedSmoothModel n) (v : ClosedSmoothModel n)) ≤
            Manifold.pathELength
              (closedSmoothModelWithCorners n) γ 0 1
```

The missing part is the uniform arbitrary-path two-case assembly: prove that
every path between endpoints in the small chart ball either stays in a larger
controlled chart ball, where the new chart-staying theorem applies, or exits
and the existing exit lower bound gives a radius-margin lower bound strong
enough to dominate the endpoint chart distance.

## Verification

Required command:

```text
lake build Poincare.Global.AntilipschitzBallFinal
```

Actual result:

```text
Build completed successfully (2991 jobs).
```

The build replayed pre-existing upstream warnings; the new module itself
compiled successfully with no `sorry`, `axiom`, or `native_decide`.
