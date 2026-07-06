# M5-bridge-5 blocked report

## Completed

- Added `Poincare/Global/ChartCurvatureBridge5.lean`.
- Proved generic inverse-chart transported-section germ locality:
  `ChartCurvatureBridge5.chartTransportedLeviCivitaSection_congr_of_eventuallyEq`.
- Proved the source-point version:
  `ChartCurvatureBridge5.chartTransportedLeviCivitaSection_congr_of_eventuallyEq_at`.
- Proved transported chart Levi-Civita hom germ locality in its field slot:
  `ChartCurvatureBridge5.chartTransportedLeviCivitaHom_congr_of_eventuallyEq`.
- Proved arbitrary-field pointwise and germ naturality for applying the
  transported hom and then reading through the anchor chart:
  `ChartCurvatureBridge5.chartTransportedLeviCivitaSection_hom_apply_chart` and
  `ChartCurvatureBridge5.chartTransportedLeviCivitaSection_hom_eventuallyEq`.

These are the generic outer transport/locality APIs that the M5-bridge-4 report
identified as missing.

## Verification

Command run:

```bash
lake build Poincare.Global.ChartCurvatureBridge5
```

Result: success.  The build completed all `3106` jobs and emitted only existing
dependency warnings.

## Remaining blocker

The remaining work is isolated to the single curvature assembly statement below.
It should now be a term-by-term proof using the new generic glue plus the
already-proven inner-field germs from `ChartCurvatureBridge4`, the closed-hom
germ from `ChartCurvatureBridge3`, and
`mlieBracket_extend_extend_eventually_eq_zero`.

```lean
theorem chartLeviCivita_curvatureOp_extend_eq_chartTransported_curvatureOp
    (g : ClosedSmoothRiemannianMetric n M) {x₀ : M} (u w a : TM x₀) :
    CovariantDerivative.curvatureOp (GeodesicTransport.chartLeviCivita g x₀)
        (FiberBundle.extend
          (E := fun z : F => TangentSpace (𝓘(ℝ, F)) z)
          F (x := extChartAt I x₀ x₀) u)
        (FiberBundle.extend
          (E := fun z : F => TangentSpace (𝓘(ℝ, F)) z)
          F (x := extChartAt I x₀ x₀) w)
        (FiberBundle.extend
          (E := fun z : F => TangentSpace (𝓘(ℝ, F)) z)
          F (x := extChartAt I x₀ x₀) a)
        (extChartAt I x₀ x₀)
      =
    CovariantDerivative.chartTransportedLeviCivitaSection x₀
      (CovariantDerivative.curvatureOp g.leviCivita
        (FiberBundle.extend F u)
        (FiberBundle.extend F w)
        (FiberBundle.extend F a))
      (extChartAt I x₀ x₀)
```

Once this statement closes, the full bridge is its composition with
`ChartCurvatureBridge2.chartCurvatureOf_chartChristoffelField_eq_chartLeviCivita_curvature`;
the round-sphere witness should then be the chart-curvature calculation plus the
round-sphere chart metric/Kulkarni-Nomizu identification.
