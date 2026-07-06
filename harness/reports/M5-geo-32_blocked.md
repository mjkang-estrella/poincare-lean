# M5-geo-32: blocked on the uniform pairwise path-length lower bound

## Status

Added the new Lean module requested by the task:

```text
Poincare/Global/AntilipschitzBall.lean
```

No existing Lean file was edited, including `Poincare.lean`.

## Verified Lean payload

The new module proves the path-infimum assembly:

```lean
theorem ofReal_le_riemannianEDist_of_forall_pathELength_lower
```

If every `C¹` path from `x` to `y` has `pathELength` at least `L`, this proves

```lean
ENNReal.ofReal L ≤ Manifold.riemannianEDist I x y
```

It also proves the induced real-distance form:

```lean
theorem le_induced_dist_of_forall_pathELength_lower
```

After installing `g.toMetricSpace`, the same path lower bound gives

```lean
L ≤ dist x y
```

Finally, it proves the anti-Lipschitz ball assembly conditional on the missing
uniform pairwise path lower bound:

```lean
theorem antilipschitzWith_extChartAt_symm_of_forall_pathELength_lower
```

This theorem turns the pairwise path-length lower bound on a chart ball into
the exact `AntilipschitzWith K` statement used by
`LocalChartAntilipschitzLowerBound`.

## Remaining blocker

The single missing statement is:

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

Once this exists, `antilipschitzWith_extChartAt_symm_of_forall_pathELength_lower`
discharges the per-anchor `AntilipschitzWith` clause.  I did not add wrappers
for `LocalChartAntilipschitzLowerBound`, `volumeMeasure_univ_ne_zero`, or the
`dist x₀ (expAt g x₀ v) ≥ c * ‖v‖` payoff because they would still depend on
this undischarged pairwise path statement.

## Verification

Required command:

```text
lake build Poincare.Global.AntilipschitzBall
```

Actual result:

```text
Build completed successfully (2990 jobs).
```

The build replayed pre-existing warnings from upstream modules; the new module
itself built successfully with no `sorry`, `axiom`, or `native_decide`.
