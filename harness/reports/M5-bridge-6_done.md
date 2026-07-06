# M5-bridge-6 done report

## Completed

- Added `Poincare/Global/ChartCurvatureBridge6.lean` without editing existing
  Lean files or `Poincare.lean`.
- Proved the anchor outer-transport helper:
  `ChartCurvatureBridge6.chartTransportedLeviCivitaSection_closed_hom_apply_anchor`.
- Proved the closed inner-field transport germ:
  `ChartCurvatureBridge6.chartTransportedLeviCivitaSection_inner_closed_extend_eventuallyEq`.
- Proved the requested theorem:
  `ChartCurvatureBridge6.chartLeviCivita_curvatureOp_extend_eq_chartTransported_curvatureOp`.
- Proved the full composed bridge:
  `ChartCurvatureBridge6.chartCurvatureOf_chartChristoffelField_eq_chartTransported_curvatureOp`.

The requested theorem statement is verbatim from
`harness/reports/M5-bridge-5_blocked.md`, with the only spelling adaptation
that it lives under namespace `Poincare.ChartCurvatureBridge6`.

## Verification

Command run:

```bash
lake build Poincare.Global.ChartCurvatureBridge6
```

Result: success. The build completed `3107` jobs. The output contains existing
dependency lint warnings; no new warning is emitted from
`Poincare/Global/ChartCurvatureBridge6.lean`.

## Sphere witness status

The witness

```lean
roundSphereMetric3_hasConstantSectionalCurvature_one :
  HasConstantSectionalCurvature3 roundSphereMetric3 1
```

was not added.  After the bridge theorem, the remaining glue is isolated to
chart-to-four-linear packaging, not to the manifold/model curvature transport:

1. A chart-curvature locality lemma for Christoffel fields:

```lean
chartCurvatureOf_congr_of_eventuallyEq
    {Γ Γ' : E → E →L[ℝ] E →L[ℝ] E} {z : E}
    (hΓ : Γ =ᶠ[𝓝 z] Γ') (u v w : E) :
    chartCurvatureOf Γ z u v w = chartCurvatureOf Γ' z u v w
```

This should be closed by `hΓ.fderiv_eq` and pointwise `hΓ.eq_of_nhds`.  It
would turn the existing germ from
`roundSphereMetric3_chartChristoffelField_eq_sphereChristoffel_of_eventuallyEq_one`
into
`chartCurvatureOf (GeodesicTransport.chartChristoffelField roundSphereMetric3 x₀) ... =
 chartCurvatureOf sphereChristoffel ...`.

2. A lowered chart/global algebra bridge at the anchor:

```lean
roundSphereMetric3_inner_chartTransported_curvature_eq_chartMetric
```

combining
`ChartCurvatureBridge6.chartCurvatureOf_chartChristoffelField_eq_chartTransported_curvatureOp`,
`CovariantDerivative.chartMetric_chartTransportedLeviCivitaSection`,
`chartTransportedLeviCivitaSection_extend_apply_chart`,
`roundSphereMetric3_chartMetric_eq`, and the definitional comparison between
`ClosedSmoothRiemannianMetric.tensorKulkarniNomizuAt` and
`chartTensorKulkarniNomizu` at `extChartAt (𝓡 3) x x`.

Those two pieces should compose with
`conformalChartMetric_chartCurvatureOf_sphereChristoffel` to produce the
round-sphere witness.
