# M3-predicates-5 blocked report

## Verified progress

Added the fixed-vector spatial regularity layer to
`Poincare/Global/ScalarVariation.lean`:

- `VariationSpatiallyDifferentiableAt h x`: for every fixed model vector pair
  `p q : E`, the scalar component `y ↦ h y p q` is manifold-differentiable at
  `x`.  This is not a trace or covariant-derivative predicate.
- `TimeVariationSpatiallyDifferentiableAt gt t₀ x`: the same honest
  fixed-vector condition specialized to `timeDerivAt gt t₀`.
- `variationSpatiallyDifferentiableAt_timeDeriv_of_regular`: adapter from the
  time-variation regularity class to the raw variation class.
- Satisfiability witnesses:
  `variationSpatiallyDifferentiableAt_static`,
  `variationSpatiallyDifferentiableAt_zero`,
  `timeVariationSpatiallyDifferentiableAt_const`, and
  `variationSpatiallyDifferentiableAt_const_timeDeriv`.

This discharges the hypothesis-shape piece requested by the task: the new class
speaks only about fixed-vector scalar components and is satisfiable by static
fields, including the zero/static time-derivative variation.

## Remaining blocker

I did not discharge the nonzero `TraceMetricVariationDerivAt` target, because
the missing step is still a real closed-to-model transport theorem, not merely a
missing hypothesis name.

The model theorem
`RicciFlow.RicciFlow.fderiv_tensorMetricTrace_eq` proves exactly the desired
calculation on a fixed normed vector space:

```lean
(fderiv ℝ (tensorMetricTrace G H) x) w
  = ∑ i, covTensor2Deriv G H x w eᵢ (G x).inverse eⁱ
```

It uses `hasFDerivAt_inverse_raise`,
`g_inverse_raise_metric_compat`, and `H_inverse_raise_trace` to cancel the
inverse-raise derivative against the Christoffel slot corrections.

In the closed layer, applying that theorem honestly still requires a transport
lemma identifying, in a chart at `x`,

1. `traceMetricVariationAt g h` with the model `tensorMetricTrace` of the
   chart metric and chart representation of `h`;
2. `covTensor2DerivAt g h x w p q` with the model `covTensor2Deriv` for the
   chart Levi-Civita connection, after pushing `w p q` through the chart
   derivative; and
3. the canonical Levi-Civita values in `covTensor2DerivAt` with the chart
   Levi-Civita values on a bump-supported chart neighborhood.

The repo has the ingredients for this route (`extDerivFun_apply_fixed_chart`,
`chartMetric`, `chartTransported_metricCompatibleAt`,
`chartTransportedLeviCivitaHom_eq_leviCivita_eventually`, and the model
`fderiv_tensorMetricTrace_eq` chain), but there is not yet a compact theorem
bridging the closed `covTensor2DerivAt` expression to the model
`covTensor2Deriv` expression.  Adding a hypothesis that directly states the
contracted equality would restate `TraceMetricVariationDerivAt`, so I stopped
under the worker contract.

## Verification

Verified the changed Lean file:

```text
lake env lean Poincare/Global/ScalarVariation.lean
```

Result: success, with only the pre-existing unused-section-variable linter
warnings after the new declarations were cleaned up.

Verified the requested modules:

```text
lake build Poincare.Global.ScalarVariation Poincare.Global.ScalarEvolution
```

Result: success (`Build completed successfully (2806 jobs).`), with only
pre-existing linter warnings in replayed dependencies and the existing
`ScalarVariation.lean` unused-section-variable warnings.
