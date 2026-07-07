# M5-rigid-4 report: anchor curvature instantiation strict partial

## Verification

- `lake build Poincare.Global.JacobiInstantiate`: **success**.
- The build completed with replayed upstream warnings only; the new module built.
- `Poincare/Global/JacobiInstantiate.lean` contains no forbidden proof
  placeholders or primitive trust extensions.

## Added files

- `Poincare/Global/JacobiInstantiate.lean`
- `harness/reports/M5-rigid-4_blocked.md`

No existing Lean file or import aggregator was edited.

## Verified statements

The main non-vacuous isolated statement is:

```lean
theorem Poincare.chartCurvatureOf_chartChristoffelField_constantCurvature_one_anchor
```

It proves the forward transported chart constant-curvature identity at the
anchor for any `g : ClosedSmoothRiemannianMetric 3 M` with
`HasConstantSectionalCurvature3 g 1`:

```lean
G0 (chartCurvatureOf (chartChristoffelField g x0) z0 u w a) b
  =
-(1 / 2) * chartTensorKulkarniNomizu G0 G0 u w a b
```

where `z0 = extChartAt I3 x0 x0` and
`G0 p q = CovariantDerivative.chartMetric g.inner x0 z0 p q`.

Supporting proved lemmas:

```lean
theorem Poincare.chartMetric_anchor_eq_inner
theorem Poincare.chartMetric_chartCurvatureOf_chartChristoffelField_eq_inner_curvature
theorem Poincare.tensorKulkarniNomizuAt_eq_chartMetric_anchor
theorem Poincare.chartCurvatureOf_chartChristoffelField_unit_orthogonal_lowered_anchor
```

The last theorem gives the unit/transverse contraction in lowered form:
`G0 (R(v,J)v) b = -G0 J b`.

## Remaining boundary

This is blocked before the requested interval oscillator theorem.  The anchor
curvature bridge is now instantiated, but the generic raised vector form
`chartCurvatureOf ... v J v = -J` and the interval equation `J'' = -J` still
need a theorem converting the lowered chart-metric identity back to the model
coordinate vector and transporting it away from the anchor point.

The exact bite is the generic tangent/model bookkeeping:

- `HasConstantSectionalCurvature3` and `ChartCurvatureBridge6` naturally use
  tangent vectors at a manifold point.
- `coordinateCovariantJacobiSecond_eq_chartCurvatureOf` is a model-coordinate
  theorem for an `E`-valued chart curve.
- At the anchor, lowering by `CovariantDerivative.chartMetric` is enough to
  prove the KN identity, but raising the lowered identity to a model vector and
  repeating it at each `gamma(t).1` along an honest interval requires an additional
  chart-coordinate/tangent transport lemma.

Consequently the Gauss orthogonality input can feed the lowered contraction at
the anchor, but the covariant-vs-coordinate second derivative bookkeeping away
from the anchor is not yet available in the repo API.
