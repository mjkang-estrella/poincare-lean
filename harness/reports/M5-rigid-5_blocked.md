# M5-rigid-5 report: zone curvature bridge partial

## Verification

- `lake build Poincare.Global.ChartCurvatureBridgeZone`: **success**.
- The build completed with replayed upstream warnings only.
- `Poincare/Global/ChartCurvatureBridgeZone.lean` contains no `sorry`, no new
  `axiom`, and no `native_decide`.

## Added files

- `Poincare/Global/ChartCurvatureBridgeZone.lean`
- `harness/reports/M5-rigid-5_blocked.md`

No existing Lean file or import aggregator was edited.

## Verified statements

The new module proves the arbitrary-point model-side bridge:

```lean
Poincare.ChartCurvatureBridgeZone
  .chartCurvatureOf_chartChristoffelField_eq_chartLeviCivita_curvature_at
```

This moves the `ChartCurvatureBridge2` packaging from the anchor image to any
model point `z`:

```lean
chartCurvatureOf (GeodesicTransport.chartChristoffelField g x₀) z u v w
  =
CovariantDerivative.curvatureOp (GeodesicTransport.chartLeviCivita g x₀)
  (FiberBundle.extend _ (x := z) u)
  (FiberBundle.extend _ (x := z) v)
  (FiberBundle.extend _ (x := z) w) z
```

The module also proves the lowered constant-curvature-one identity for the
transported manifold curvature at a chart-target point:

```lean
Poincare.ChartCurvatureBridgeZone
  .chartMetric_chartTransported_curvatureOp_constantCurvature_one_zone
```

Here the model vectors `u w a b : ClosedSmoothModel 3` are converted to tangent
vectors at `(extChartAt I3 x₀).symm z` by the inverse-chart derivative

```lean
chartInverseTangent x₀ z
```

and the result is:

```lean
chartMetric g.inner x₀ z
  (chartTransportedLeviCivitaSection x₀
    (curvatureOp g.leviCivita
      (extend _ (chartInverseTangent x₀ z u))
      (extend _ (chartInverseTangent x₀ z w))
      (extend _ (chartInverseTangent x₀ z a))) z) b
 =
-(1 / 2) * chartTensorKulkarniNomizu
  (fun p q => chartMetric g.inner x₀ z p q)
  (fun p q => chartMetric g.inner x₀ z p q)
  u w a b
```

Supporting verified statements:

```lean
Poincare.ChartCurvatureBridgeZone.chartInverseTangent
Poincare.ChartCurvatureBridgeZone.tensorKulkarniNomizuAt_eq_chartMetric_zone
Poincare.ChartCurvatureBridgeZone.chartMetric_chartTransported_curvatureOp_eq_inner_curvature_zone
```

The final composition theorem is also proved with an explicit bridge hypothesis:

```lean
Poincare.ChartCurvatureBridgeZone
  .chartCurvatureOf_chartChristoffelField_constantCurvature_one_zone_of_bridge
```

## Remaining boundary

The full requested zone bridge is not closed.  The missing non-vacuous glue is
the pointwise identification

```lean
chartCurvatureOf (GeodesicTransport.chartChristoffelField g x₀) z u w a
  =
CovariantDerivative.chartTransportedLeviCivitaSection x₀
  (CovariantDerivative.curvatureOp g.leviCivita
    (extend E3 (chartInverseTangent x₀ z u))
    (extend E3 (chartInverseTangent x₀ z w))
    (extend E3 (chartInverseTangent x₀ z a))) z
```

for `z` in a cutoff-one chart neighborhood.  The proved model-side bridge gives
the left side as `curvatureOp (chartLeviCivita g x₀)` on constant model fields
at `z`; what remains is the term-by-term source-point transport from those
constant model fields to the pushed-forward manifold fields determined by
`chartInverseTangent x₀ z`.

This is stronger/different bookkeeping than the anchor bridge: at the anchor,
canonical `extend` fields based at `x₀` have constant `x₀`-chart
representatives.  Away from the anchor, the correct fields for model-constant
vectors are inverse-chart-pushed fields, not the canonical `extend` fields
based at `(extChartAt I3 x₀).symm z`.  No existing source-point theorem in
`ChartCurvatureBridge3/4/5/6` currently packages that naturality.

Consequently the honest interval oscillator is still blocked on this final
chart-constant-field transport lemma.
