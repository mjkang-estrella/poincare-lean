# M5-bridge-4 blocked report

## Completed

- Added `Poincare/Global/ChartCurvatureBridge4.lean`.
- Proved the pointwise chart-transport identity for the inner field:
  `ChartCurvatureBridge4.chartTransportedLeviCivitaSection_inner_apply_chart`.
- Proved the isolated missing germ from the M5-bridge-3 report:
  `ChartCurvatureBridge4.chartTransportedLeviCivitaSection_inner_extend_eventuallyEq`.

This is the eventual equality between the transported manifold-side inner
covariant-derivative field and the model-side chart Levi-Civita derivative of
the corresponding canonical model extensions.

## Verification

Command run:

```bash
lake build Poincare.Global.ChartCurvatureBridge4
```

Result: success. The build completed all `3105` jobs and emitted only existing
dependency warnings.

## Remaining blocker

The curvature-level assembly is not yet closed.  The new inner-field germ is
available for the two inner terms, but the term-by-term curvature proof still
needs a general outer transport/locality glue lemma, not just the canonical
`extend` specialization now proved.

The needed glue has this shape:

```lean
CovariantDerivative.chartTransportedLeviCivitaSection x₀
    (fun y =>
      CovariantDerivative.chartTransportedLeviCivitaHom ... σ y (X y))
    (extChartAt I x₀ y)
=
  (GeodesicTransport.chartLeviCivita g x₀)
    (CovariantDerivative.chartTransportedLeviCivitaSection x₀ σ)
    (extChartAt I x₀ y)
    (CovariantDerivative.chartTransportedLeviCivitaSection x₀ X
      (extChartAt I x₀ y))
```

for arbitrary local tangent fields `σ` and `X`, plus the induced germ-locality:

```lean
σ =ᶠ[𝓝 x₀] τ →
  CovariantDerivative.chartTransportedLeviCivitaSection x₀ σ
    =ᶠ[𝓝 (extChartAt I x₀ x₀)]
  CovariantDerivative.chartTransportedLeviCivitaSection x₀ τ
```

With those two generic transport lemmas, the remaining assembly should follow
the report plan:

- use `chartTransportedLeviCivitaSection_inner_extend_eventuallyEq` for the
  `w` and `u` inner fields;
- use `ChartCurvatureBridge3.chartTransportedLeviCivitaHom_extend_eventuallyEq_closed`
  applied to `extend` directions to replace transported hom fields with
  `g.leviCivita` hom fields;
- use `CovariantDerivative.congr_of_eventuallyEq` for the two outer connection
  terms;
- use `mlieBracket_extend_extend_eventually_eq_zero` for the canonical bracket
  term.

Consequently the assembled link, the full bridge through
`ChartCurvatureBridge2.chartCurvatureOf_chartChristoffelField_eq_chartLeviCivita_curvature`,
and the sphere witness `HasConstantSectionalCurvature3 roundSphereMetric3 1`
remain blocked on that generic outer transport/locality glue.
