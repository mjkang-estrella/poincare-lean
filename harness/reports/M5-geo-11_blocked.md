# M5-geo-11 blocked report

## Status

Partial progress in a new file only:
`Poincare/Global/GeodesicReanchorLaw.lean`.

The file proves the chart-metric transport identity in the form that matches
the existing `CovariantDerivative.chartMetric` API.  On a chart overlap, the
`y₀` chart metric at the transition point, evaluated on the model vectors
obtained by inverse-chart differential followed by `y₀` chart differential,
is equal to the `x₀` chart metric at the original chart point.  Both sides
reduce to `g.inner` at the same underlying manifold point.

The full transition law for `chartTransitionState` is still not discharged, so
the unconditional re-anchoring theorem from `GeodesicReanchor.lean` was not
instantiated.

## Added declarations

```lean
def Poincare.GeodesicTransport.chartTransitionMFDeriv
    (x₀ y₀ : M) (z : ClosedSmoothModel n) :
    ClosedSmoothModel n →L[ℝ] ClosedSmoothModel n

theorem Poincare.GeodesicTransport.chartMetric_chartTransitionMFDeriv
    (g : ClosedSmoothRiemannianMetric n M) (x₀ y₀ : M)
    {z : ClosedSmoothModel n}
    (hy :
      (extChartAt (closedSmoothModelWithCorners n) x₀).symm z ∈
        (extChartAt (closedSmoothModelWithCorners n) y₀).source)
    (u v : ClosedSmoothModel n) :
    CovariantDerivative.chartMetric g.inner y₀ (chartTransition x₀ y₀ z)
        (chartTransitionMFDeriv (x₀ := x₀) (y₀ := y₀) z u)
        (chartTransitionMFDeriv (x₀ := x₀) (y₀ := y₀) z v) =
      CovariantDerivative.chartMetric g.inner x₀ z u v
```

`chartTransitionMFDeriv` is independent of `g`; the theorem keeps `g` as its
metric parameter.

## Verification

Command run:

```bash
lake build Poincare.Global.GeodesicReanchorLaw
```

Actual result:

```text
Build completed successfully (2828 jobs).
```

The build replayed pre-existing imported-module warnings.  The new module uses
only completed Lean proofs and adds no proof-bypass declarations.

## Remaining blocker

The proved identity uses the manifold differential expression
`chartTransitionMFDeriv`.  The ODE state in `GeodesicOverlap.lean` uses the
total Frechet derivative

```lean
chartTransitionDeriv x₀ y₀ z =
  fderiv ℝ (chartTransition x₀ y₀) z
```

The next bridge should identify these derivatives on the honest overlap:

```lean
chartTransitionDeriv x₀ y₀ z =
  chartTransitionMFDeriv (x₀ := x₀) (y₀ := y₀) z
```

under `z ∈ (extChartAt I x₀).target` and
`(extChartAt I x₀).symm z ∈ (extChartAt I y₀).source`.  The direct proof gets
to the expected chain-rule statement, but needs careful normalization between
the lambda body of `chartTransition` and the composed function expected by
`mfderiv_comp`.

After that first-order bridge, the real transition-law obligation remains the
second component derivative:

```lean
HasDerivAt
  (fun s =>
    (chartTransitionState x₀ y₀
      (fun r => geodesicGermChartSolution g x₀ v₀ (t₀ + r)) s).2)
  (-(chartChristoffelField g y₀
      (chartTransitionState x₀ y₀
        (fun r => geodesicGermChartSolution g x₀ v₀ (t₀ + r)) t).1)
      (chartTransitionState x₀ y₀
        (fun r => geodesicGermChartSolution g x₀ v₀ (t₀ + r)) t).2
      (chartTransitionState x₀ y₀
        (fun r => geodesicGermChartSolution g x₀ v₀ (t₀ + r)) t).2)
  t
```

The intended Koszul route is now narrowed to:

1. Use `chartMetric_chartTransitionMFDeriv` to rewrite all metric pairings
   through the transition differential.
2. Differentiate those pairings along the shifted `x₀` geodesic.
3. Use the cutoff-`1` Koszul pairing characterization from
   `GeodesicReanchor.lean` on both chart germs.
4. Convert paired equality to vector equality with the existing
   chart-metric nondegeneracy lemma.
5. Feed the two component derivative facts into
   `chartTransitionState_eventually_solves_of_components`.

This would discharge the `htransport_solves` input of
`shifted_geodesicGermAt_eventuallyEq_geodesicGermAt_reanchored`; the remaining
unconditional re-anchor theorem is then the neighborhood/double-good glue.
