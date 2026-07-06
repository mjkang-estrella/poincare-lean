# M5-geo-24 blocked report

## Status

Strict partial progress in a new file only:
`Poincare/Global/GeodesicReanchorClose.lean`.

No existing Lean file was edited, and `Poincare.lean` was not changed.

The new module closes the first-order derivative mismatch from
`M5-geo-11_blocked.md`: on an honest chart overlap, the total Frechet
derivative used by `chartTransitionState`,

```lean
chartTransitionDeriv x₀ y₀ z = fderiv ℝ (chartTransition x₀ y₀) z
```

is now identified with the manifold differential expression
`chartTransitionMFDeriv` used by the chart-metric transport theorem in
`GeodesicReanchorLaw.lean`.

This lets the existing metric bridge be restated for the actual state
derivative and proves the position-component transition law.  The module also
packages the strongest remaining local reduction: the transported state solves
the target-anchor first-order chart ODE as soon as the velocity-component
Christoffel transition law is supplied.

## Added declarations

```lean
theorem Poincare.GeodesicTransport.chartTransition_hasFDerivAt_chartTransitionMFDeriv
    (x₀ y₀ : M) {z : ClosedSmoothModel n}
    (hz : z ∈ (extChartAt (closedSmoothModelWithCorners n) x₀).target)
    (hy :
      (extChartAt (closedSmoothModelWithCorners n) x₀).symm z ∈
        (extChartAt (closedSmoothModelWithCorners n) y₀).source) :
    HasFDerivAt (chartTransition (n := n) x₀ y₀)
      (chartTransitionMFDeriv (x₀ := x₀) (y₀ := y₀) z) z

theorem Poincare.GeodesicTransport.chartTransitionDeriv_eq_chartTransitionMFDeriv
    (x₀ y₀ : M) {z : ClosedSmoothModel n}
    (hz : z ∈ (extChartAt (closedSmoothModelWithCorners n) x₀).target)
    (hy :
      (extChartAt (closedSmoothModelWithCorners n) x₀).symm z ∈
        (extChartAt (closedSmoothModelWithCorners n) y₀).source) :
    chartTransitionDeriv (n := n) x₀ y₀ z =
      chartTransitionMFDeriv (x₀ := x₀) (y₀ := y₀) z

theorem Poincare.GeodesicTransport.chartMetric_chartTransitionDeriv
    (g : ClosedSmoothRiemannianMetric n M) (x₀ y₀ : M) {z : ClosedSmoothModel n}
    (hz : z ∈ (extChartAt (closedSmoothModelWithCorners n) x₀).target)
    (hy :
      (extChartAt (closedSmoothModelWithCorners n) x₀).symm z ∈
        (extChartAt (closedSmoothModelWithCorners n) y₀).source)
    (u v : ClosedSmoothModel n) :
    CovariantDerivative.chartMetric g.inner y₀ (chartTransition x₀ y₀ z)
        (chartTransitionDeriv x₀ y₀ z u)
        (chartTransitionDeriv x₀ y₀ z v) =
      CovariantDerivative.chartMetric g.inner x₀ z u v

theorem Poincare.GeodesicTransport.chartTransitionState_fst_hasDerivAt

theorem Poincare.GeodesicTransport.chartTransitionState_eventually_fst_hasDerivAt

theorem Poincare.GeodesicTransport.chartTransitionState_eventually_solves_of_velocity_component
```

The last theorem reduces the full `htransport_solves` input to the single
remaining velocity-component derivative:

```lean
∀ᶠ t in 𝓝 (0 : ℝ),
  HasDerivAt (fun s : ℝ => (chartTransitionState x₀ y₀ γ s).2)
    (-(chartChristoffelField g y₀
        (chartTransitionState x₀ y₀ γ t).1)
      (chartTransitionState x₀ y₀ γ t).2
      (chartTransitionState x₀ y₀ γ t).2) t
```

## What the new templates supplied

- `ChartCurvatureBridge3/4/5/6.lean` now supply strong fixed-anchor
  transported-section and transported-hom naturality, including
  `congr_of_eventuallyEq` and `_apply_chart` bridge lemmas.
- Those lemmas explain how to move closed Levi-Civita values through one
  anchor chart and were enough to reassess that the remaining obstruction is
  not a generic locality/congruence gap.
- `GeodesicReanchorLaw.lean` already supplied the chart-metric transport
  identity for `chartTransitionMFDeriv`; this task closes the exact derivative
  spelling mismatch so that identity applies to `chartTransitionDeriv`.

## What is still missing

The curvature-bridge templates do not yet expose the double-anchor
acceleration law needed for the second component of `chartTransitionState`.
Concretely, they do not prove that differentiating

```lean
fun s => chartTransitionDeriv x₀ y₀ (γ s).1 (γ s).2
```

along an `x₀` chart geodesic gives

```lean
-(chartChristoffelField g y₀ (chartTransitionState x₀ y₀ γ t).1)
  (chartTransitionState x₀ y₀ γ t).2
  (chartTransitionState x₀ y₀ γ t).2
```

in the `y₀` chart.  This is the double-good Christoffel/acceleration
transition law.  The new first-order lemmas remove the metric/position
component blockers, but the transported velocity derivative remains to be
proved, likely by specializing the fixed-anchor transported-hom naturality to
two overlapping anchor charts and then pairing with the Koszul characterizers.

`ExponentialMap.lean`'s interval uniqueness and endpoint-control assets also
do not remove this blocker: same-anchor uniqueness was already available in
`GeodesicReanchor.lean`; the missing input is still that the transitioned
shifted state solves the `y₀` chart ODE.

## Verification

Commands run:

```bash
placeholder/bypass grep on Poincare/Global/GeodesicReanchorClose.lean
lake build Poincare.Global.GeodesicReanchorClose
git diff --check -- Poincare/Global/GeodesicReanchorClose.lean
```

Actual result:

```text
lake build Poincare.Global.GeodesicReanchorClose
Build completed successfully (2829 jobs).
```

The build replayed pre-existing imported-module linter warnings.  The new
module built successfully, and the placeholder/bypass grep found no matches.
