# M3-predicates-2 blocked report

## Completed

- Added and verified the closed algebraic bridge
  `metricDualVectorAt_eq_metricRaiseContinuousAt`:
  the algebraic `metricDualVectorAt g x (phi : Module.Dual ...)` is the same
  vector as `g.metricRaiseContinuousAt x phi` for continuous covectors.
- This removes one coercion/conversion step needed by any future spatial
  raised-basis derivative proof: the closed raised dual basis can now be
  rewritten to the continuous raise map used by the existing time-derivative
  machinery.

Commit:

```text
3a479697 Add closed metric dual raise bridge
```

## Blocker

The requested nonzero discharge of `TraceMetricVariationDerivAt` is still
blocked in the closed layer.

The model theorem
`RicciFlow.RicciFlow.fderiv_tensorMetricTrace_eq` proves the right identity
for a fixed model vector space:

```lean
fderiv (tensorMetricTrace G H) x w =
  sum_i covTensor2Deriv G H x w b_i ((G x).inverse b^i)
```

It relies on:

1. differentiability of the model metric family `G`;
2. differentiability of the tensor family `H`;
3. the inverse-raise derivative lemma
   `hasFDerivAt_inverse_raise` / `g_inverse_raise_metric_compat`;
4. Christoffel cancellation in the fixed model frame.

The closed theorem cannot currently be obtained by a direct rewrite because
`traceMetricVariationAt g h y` is defined using

```lean
Module.finBasis R (TM y)
metricDualVectorAt g y ((Module.finBasis R (TM y)).coord i)
```

at each fiber, while the chart route used by `mdifferentiableAt_gradient`
works with a smooth chart/trivialization frame transported through
`extChartAt`.  The missing closed bridge is therefore not only the inverse
raise derivative; it is the local-frame replacement theorem:

```lean
traceMetricVariationAt g h y
  =
trace of h y in a smooth chart/trivialization frame near x
```

together with the corresponding identification of the closed
`covTensor2DerivAt g h x w p q` correction terms with the model
`covTensor2Deriv G H ...` correction terms.  Existing transport results such
as `chartTransportedLeviCivitaValueAt_eq_closed_of_eventually_eq_one` provide
the Levi-Civita side, but there is no packaged theorem that combines:

- basis-invariance of the metric trace for an arbitrary local basis;
- smoothness/differentiability of the chosen local frame and raised dual
  coframe;
- the closed-to-model `covTensor2DerivAt` transport for a raw symmetric
  tensor field `h`.

Adding a hypothesis that simply states this transported trace derivative
identity would restate `TraceMetricVariationDerivAt` rather than discharge it,
so I stopped here under the worker contract.

## Recommended next task

Add a local-frame metric trace bridge before retrying
`TraceMetricVariationDerivAt`:

1. Define a trace over an arbitrary finite basis of `TM y` and prove it equals
   `traceMetricVariationAt` for bilinear `h y`.
2. Specialize that theorem to the smooth frame produced by
   `trivializationAt E (TangentSpace I) x` or the fixed chart frame used by
   `mdifferentiableAt_gradient`.
3. Prove the raised dual coframe is differentiable by rewriting with
   `metricDualVectorAt_eq_metricRaiseContinuousAt` and the model inverse-raise
   lemma.
4. Transport the model `fderiv_tensorMetricTrace_eq` back to the closed
   `extDerivFun`/`covTensor2DerivAt` statement using the existing
   Levi-Civita transport theorem.

Only after this bridge exists should `deltaGamma_innerTrace_eq` be restated
without the `TraceMetricVariationDerivAt` input.

## Verification

```text
lake build Poincare.Global.ScalarVariation Poincare.Global.ScalarEvolution
```

Result: success.

No forbidden proof placeholder construct was added.
