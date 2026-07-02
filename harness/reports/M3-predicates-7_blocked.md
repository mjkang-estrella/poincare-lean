# M3-predicates-7 blocked report

## Verified native progress

Added a non-vacuous decomposition of the remaining trace-derivative frontier in
`Poincare/Global/ScalarVariation.lean`:

- `TraceMetricVariationProductRuleAt`: isolates the finite-sum product rule for
  differentiating `traceMetricVariationAt g h`, with one term for the fixed-slot
  derivative of `h` and one term for the raised dual basis derivative
  `spatialMetricDualVectorDerivAt`.
- `TraceMetricVariationRaiseCancellationAt`: isolates the contracted
  raised-index cancellation that turns the `spatialMetricDualVectorDerivAt`
  contribution into the two Levi-Civita correction terms in
  `covTensor2DerivAt`.
- `traceMetricVariationDerivAt_of_productRule_raiseCancellation`: proves the
  frozen `TraceMetricVariationDerivAt` predicate from those two obligations.
- `deltaGamma_innerTrace_eq_of_covTensor2Regular_traceProduct`: downstream
  adapter that consumes the two new trace obligations instead of requiring
  `TraceMetricVariationDerivAt` directly.

This keeps the target statement unchanged and avoids adding a hypothesis that
merely restates the contracted trace equality.

## Remaining blocker

I did not prove the two analytic obligations from
`VariationSpatiallyDifferentiableAt h x` and metric smoothness.

The remaining proof work is now split into two concrete non-vacuous lemmas:

1. Prove `TraceMetricVariationProductRuleAt` from the fixed-fiber product rule:
   differentiate the finite sum for `traceMetricVariationAt`, using the
   derivative of `y ↦ metricDualVectorAt g y φ` and fixed-vector
   differentiability of `h`.
2. Prove `TraceMetricVariationRaiseCancellationAt` by expanding
   `spatialMetricDualVectorDerivAt`, then proving the finite-dimensional
   adjoint trace identity that converts the raised-covector correction into the
   first-slot Levi-Civita correction.

Both are genuine calculus/algebra facts, not target restatements.  I stopped
there rather than hiding them inside a broad class or a direct trace equality.

## Verification

Narrow file check:

```text
lake env lean Poincare/Global/ScalarVariation.lean
```

Result: success, with the pre-existing unused-section-variable warnings in
`ScalarVariation.lean`.

Requested module build:

```text
lake build Poincare.Global.ScalarVariation Poincare.Global.ScalarEvolution
```

Result: success (`Build completed successfully (2806 jobs).`), with existing
warnings in replayed dependencies and the pre-existing
`ScalarVariation.lean` unused-section-variable warnings.
