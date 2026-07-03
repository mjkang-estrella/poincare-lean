# M4-prep-18 done report

## Pre-formal trace re-validation

The M4-prep-17 coefficient pinning changes the tensor RHS to

```text
roughTensorLaplacianAt Ric
  + 2 * lichnerowiczCurvatureAt Ric
  - ricciActionOnTensorAt Ric
```

Equivalently, using
`ricciQuadraticAt_eq_two_lichnerowiczCurvatureAt_ricciVariationField`, this is

```text
roughTensorLaplacianAt Ric - ricciActionOnTensorAt Ric + ricciQuadraticAt.
```

Its fixed-metric trace is not the Hamilton scalar RHS.  The existing trace
lemmas give:

* `roughTensorLaplacianRicciTraceAt_of_traceSecondRegularity`:
  `tr_g(roughTensorLaplacianAt Ric) = ΔR`.
* `ricciActionRicciTraceAt`: `tr_g(ricciActionOnTensorAt Ric) = 2 |Ric|²`.
* `lichnerowiczCurvatureAt_ricciQuadraticAt_trace_cancellation`:
  `tr_g(-2L + Q) = 0`, and since `Q = 2L`, the corrected tensor trace has
  `tr_g(2L - A) = 2 |Ric|² - 2 |Ric|² = 0`.

So the corrected tensor RHS traces to `ΔR`.

This reconciles with the proven scalar equation because `scalarAt` is the
moving-metric trace of the Ricci tensor.  The existing scalar-variation chain
does not identify `dR/dt` with only `tr_g(∂ₜ Ric)`: in
`hasDerivAt_scalarAt_lichnerowicz`, the derivative of the raised trace is

```text
tr_g(∂ₜ Ric) - metricVariationRicciPairingAt g (timeDerivAt gt t₀) x.
```

For Ricci flow, `timeDerivAt = -2 Ric`, and the merged bookkeeping lemma
`metricVariationRicciPairingAt_timeDeriv_eq_negTwoRicci` gives

```text
metricVariationRicciPairingAt g (timeDerivAt gt t₀) x = -2 |Ric|².
```

Therefore the moving-metric contribution is

```text
- metricVariationRicciPairingAt g (timeDerivAt gt t₀) x = +2 |Ric|².
```

The corrected tensor trace `ΔR` plus this moving-metric term is exactly the
proven Hamilton scalar RHS `ΔR + 2 |Ric|²`.  No residual coefficient error is
visible in the merged `timeDerivAt` / trace-variation bookkeeping.

