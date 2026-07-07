# M5-glob-17 done report

## Status

Strict partial progress in a new Lean file only:
`Poincare/Global/HdiffInstantiate.lean`.

No existing Lean file was edited, and `Poincare.lean` was not changed.

The new module adds one isolated theorem:

```lean
theorem Poincare.GeodesicTransport.chartGeodesicMetric_differentiated_pullback_hdiff_of_eventually_cutoff_eq_one
```

## Proved strict partial

The theorem instantiates the abstract differentiated-pullback lemma from
`PullbackDifferentiate.lean` with the concrete chart data:

```text
G0    = chartGeodesicMetric g x0
G1    = chartGeodesicMetric g y0
sigma = chartTransition x0 y0
D     = chartTransitionDeriv x0 y0
```

It assumes local/eventual membership in the overlap and local/eventual
cutoff-one facts, then derives internally:

- `ContDiffAt ℝ 2 (chartTransition x0 y0) z` from the `extChartAt` transition;
- `HasFDerivAt chartTransition (chartTransitionDeriv ... z) z`;
- `HasFDerivAt chartTransitionDeriv (fderiv ... z) z`;
- differentiability of both concrete `chartGeodesicMetric` families from
  `CovariantDerivative.contDiff_blendedChartMetric`;
- the pullback germ by filtering the pointwise theorem
  `chartGeodesicMetric_chartTransitionDeriv_of_cutoff_eq_one`.

The resulting conclusion is the concrete `hdiff` identity required by
`DifferentiatedCompat.lean`.

## Verification

Commands run:

```bash
placeholder scan on Poincare/Global/HdiffInstantiate.lean
git diff --cached --check -- Poincare/Global/HdiffInstantiate.lean harness/reports/M5-glob-17_done.md
lake build Poincare.Global.HdiffInstantiate
```

Actual result:

```text
rg: no matches
git diff --cached --check: no output
lake build Poincare.Global.HdiffInstantiate
✔ [2833/2833] Built Poincare.Global.HdiffInstantiate (4.7s)
Build completed successfully (2833 jobs).
```

The build replayed pre-existing imported-module warnings. The new module built
successfully and introduced no reported warning.
