# M5-glob-16 done report

## Status

Strict partial progress in a new Lean file only:
`Poincare/Global/PullbackDifferentiate.lean`.

No existing Lean file was edited, and `Poincare.lean` was not changed.

The new module adds one isolated theorem:

```lean
theorem Poincare.GeodesicTransport.differentiated_pullback_hdiff_of_eventuallyEq
```

## Proved strict partial

The theorem proves the calculus core of the `hdiff` producer.

Given:

- a source metric family `G0`;
- a target metric family `G1`;
- a base transition `sigma`;
- a first-derivative field `D`;
- local derivative data `HasFDerivAt sigma (D z) z`,
  `HasFDerivAt D (fderiv ℝ D z) z`, and the metric derivative data;
- the germ identity

```text
G1 (sigma q) (D q a) (D q b) = G0 q a b
```

eventually at `z`,

it differentiates the germ and proves exactly the three-term `hdiff` shape:

```text
dG1[D e](D a,D b)
  + G1((dD[e]) a,D b)
  + G1(D a,(dD[e]) b)
  =
dG0[e](a,b).
```

The proof uses `Filter.EventuallyEq.fderiv_eq` for the germ equality and
Mathlib's `HasFDerivAt.comp`/`HasFDerivAt.clm_apply` chain-rule API to expand
the base and two moving vector slots.

## Remaining integration boundary

This theorem is stated at the abstract calculus layer.  The chart-specialized
instantiation should set:

```text
G0    = chartGeodesicMetric g x0
G1    = chartGeodesicMetric g y0
sigma = chartTransition x0 y0
D     = chartTransitionDeriv x0 y0
```

and supply the cutoff-one pullback germ plus the local derivative hypotheses
from the open-zone/chart-transition regularity package.

## Verification

Commands run:

```bash
rg -n '\b(sorry|admit|axiom)\b|native_decide' Poincare/Global/PullbackDifferentiate.lean
git diff --check -- Poincare/Global/PullbackDifferentiate.lean
lake build Poincare.Global.PullbackDifferentiate
```

Actual result:

```text
rg: no matches
git diff --check: no output
lake build Poincare.Global.PullbackDifferentiate
✔ [1920/1920] Built Poincare.Global.PullbackDifferentiate (2.0s)
Build completed successfully (1920 jobs).
```
