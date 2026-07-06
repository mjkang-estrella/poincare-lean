# M5-geo-31: blocked on the full anti-Lipschitz ball theorem

Task: prove the lower local distance half in a new
`Poincare.Global.GeodesicDistanceLower` module, including a compact chart-ball
metric lower bound, integrand lower comparison, exit estimate, and the
anti-Lipschitz ball statement needed by volume positivity.

## Status

I added the new Lean module:

```text
Poincare/Global/GeodesicDistanceLower.lean
```

No existing Lean file was edited, and `Poincare.lean` was not changed.  The
module contains a verified strict partial, not a vacuous wrapper.

## Verified Lean payload

The new file proves the pointwise integrand comparison hook:

```lean
theorem inverseChartCurve_enorm_mfderiv_ge_of_chartMetric_sqrt_lower
```

This theorem reuses
`inverseChartCurve_enorm_mfderiv_eq_chartMetric` from
`Poincare.Global.GeodesicLength` and turns a real lower estimate

```lean
lam * ‖u‖ ≤
  Real.sqrt (CovariantDerivative.chartMetric g.inner x₀ (z s) u u)
```

into the corresponding `ENNReal.ofReal` lower bound for the path-length
integrand of the inverse-chart curve.

The file also proves the unconditional chart-ball exit estimate:

```lean
theorem chart_ball_exit_pathELength_lower_bound
```

For every positive chart radius `r`, it produces `c : ℝ≥0` with `0 < c` such
that every `C¹` path beginning at `x₀` and ending outside

```lean
(extChartAt I x₀).symm ''
  Metric.ball ((extChartAt I x₀) x₀) r
```

has

```lean
(c : ℝ≥0∞) ≤ Manifold.pathELength I γ a b
```

The proof uses the neighborhood form of the inverse-chart ball and
`setOf_riemannianEDist_lt_subset_nhds I`, then composes the resulting local
Riemannian-distance lower bound with `Manifold.riemannianEDist_le_pathELength`.

Finally, the file packages the exit estimate in existential form:

```lean
theorem exists_chart_ball_exit_pathELength_lower_bound
```

## Remaining blocker

The full anti-Lipschitz ball statement is still not proved:

```lean
exists_extChartAt_symm_antilipschitz_ball
```

Equivalently, this does not yet discharge
`LocalChartAntilipschitzLowerBound` from
`Poincare/Global/NormalizedFlow.lean`.

The missing formal step is the finite pairwise lower comparison on a small
chart ball:

```lean
dist (symm x) (symm y) ≥ K⁻¹ * ‖x - y‖
```

for all chart points in the ball.  The verified integrand hook is ready for the
needed compact metric lower eigenvalue estimate, but I did not complete the
chain from a uniform pointwise chart-metric lower bound to Euclidean length of
arbitrary chart paths and then to a single `AntilipschitzWith K` constant.

The volume-positivity payoff remains parked.  The downstream theorem

```lean
volumeMeasure_univ_ne_zero_of_localChartAntilipschitzLowerBound
```

is already proved in `Poincare.Global.NormalizedFlow`, so once
`LocalChartAntilipschitzLowerBound` is supplied the unconditional
`volumeMeasure_univ_ne_zero` plumbing should be cheap.  I did not add that
wrapper here because the hypothesis has not been discharged.

## Verification

Required build command:

```text
lake build Poincare.Global.GeodesicDistanceLower
```

Actual result:

```text
Build completed successfully (2840 jobs).
```

The build replayed existing modules and emitted pre-existing warnings from
other files, then built `Poincare.Global.GeodesicDistanceLower` successfully.
