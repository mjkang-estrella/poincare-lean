# M5-bridge-3 blocked report

## Result

Created `Poincare/Global/ChartCurvatureBridge3.lean` without editing existing
Lean files or `Poincare.lean`.

The new module proves two non-vacuous transport germs:

- `Poincare.ChartCurvatureBridge3.chartTransportedLeviCivitaSection_extend_eventuallyEq_const`
  turns the pointwise chart statement for canonical `extend` fields into an
  eventual equality on model space near `extChartAt I x0 x0`.
- `Poincare.ChartCurvatureBridge3.chartTransportedLeviCivitaHom_extend_eventuallyEq_closed`
  specializes the lower-level
  `LeviCivitaTransport.chartTransportedLeviCivitaHom_eq_closed_of_eventually_eq_one`
  to canonical `extend` fields, using local differentiability of `extend`
  rather than the global smoothness hypothesis of
  `GeodesicTransport.chartLeviCivita_eventuallyEq_closed`.

## Verification

Final requested check:

```text
lake build Poincare.Global.ChartCurvatureBridge3
```

Result: success, `Build completed successfully (3102 jobs)`.

## Remaining blocker

The full curvature-level bridge is not completed.  The current API gives the
one-derivative chart transport:

```lean
chartTransportedLeviCivitaHom_inCoordinates_apply_chart
```

and the new file gives the two needed germs for canonical extensions.  However
`curvatureOp` contains outer derivatives of inner derivative fields:

```lean
fun y => cov Z y (W y)
```

For this cross-space bridge, the missing theorem is an eventual equality saying
that inverse-chart transport of the manifold-side inner derivative field is the
model-side inner derivative field.  In schematic form, with the usual cutoff
arguments suppressed:

```lean
CovariantDerivative.chartTransportedLeviCivitaSection x0
    (fun y =>
      CovariantDerivative.chartTransportedLeviCivitaHom ... x0 ...
        (FiberBundle.extend F a) y (FiberBundle.extend F w y))
  =ᶠ[nhds (extChartAt I x0 x0)]
    fun z =>
      (GeodesicTransport.chartLeviCivita g x0)
        (FiberBundle.extend (E := fun z : F => TangentSpace 𝓘(ℝ, F) z)
          F (x := extChartAt I x0 x0) a)
        z
        (FiberBundle.extend (E := fun z : F => TangentSpace 𝓘(ℝ, F) z)
          F (x := extChartAt I x0 x0) w z)
```

Once that equality exists for `w` and `u`, the term-by-term pattern from
`constSMul_curvatureOp_extend_apply` should apply: use connection
`congr_of_eventuallyEq` for the two outer terms, the new hom germ for the
bracket term, and `mlieBracket_extend_extend_eventually_eq_zero` for the
canonical first-slot fields.

Without that inner-field naturality theorem, the two outer terms of
`curvatureOp_apply` cannot be transported from `M` to the model chart space.
