# M3-predicates-20 blocked report

## Verified progress

This worker produced three proof-bearing commits.

1. Commit `9b4dbba4` adds the requested neighborhood-form scalar-entry
   vocabulary:
   - `CovTensor2ExtContMDiffAt`
   - `MetricExtContMDiffAt`
   - `TimeVariationExtContMDiffAt`
   - `TraceMetricVariationEntriesExtContMDiffAt`
   - `TimeVariationTraceEntriesExtContMDiffAt`

   It also proves the mechanical adapters from `ContMDiffAt 2` entries to the
   older point-at-`x` predicates:
   `CovTensor2ExtDifferentiableAt`, `CovTensor2ExtSecondDifferentiableAt`,
   `TimeVariationExtSecondDifferentiableAt`, and
   `MetricExtSecondDifferentiableAt`.  Static/zero witnesses are verified,
   and smooth metric entries are supplied by
   `ClosedSmoothRiemannianMetric.metric_pairing_contMDiffAt_two`.

2. Commit `b656aa1c` discharges the trace-C² side from the new neighborhood
   vocabulary:
   - finite real `ContMDiffAt 2` sum/product helpers,
   - `contMDiffAt_two_matrix_det_of_entries`,
   - C² Gram determinant/adjugate/inverse entries,
   - `traceMetricVariationAt_contMDiffAt_two_of_entries`,
   - `traceMetricVariationExtSecondDifferentiableAt_of_entries_contMDiffAt`,
   - `traceMetricVariationExtSecondDifferentiableAt_timeDeriv_of_entries_contMDiffAt`.

   This uses the honest Gram route: products and determinant/adjugate
   polynomials of C² entries, inverse via determinant nonvanishing at the base
   point, then the existing
   `traceMetricVariationExtSecondDifferentiableAt_of_contMDiffAt` bridge.

3. Commit `082b3b5f` adds the verified static sanity witness
   `deltaGammaFirstSlotTraceFieldCovariantDerivativeAt_const`, and a contraction
   wrapper
   `deltaGammaContractionTraceHessianDerivativeAt_of_firstSlot_entries_contMDiffAt`.
   The wrapper removes the explicit trace-C² hypothesis from the existing
   contraction-side adapter whenever the new time-variation entry C² vocabulary
   is available.  It still requires the non-static moving-frame predicate
   `DeltaGammaFirstSlotTraceFieldCovariantDerivativeAt`.

## Remaining exact obligation

The non-static contraction-side assembly is still blocked by the same genuine
moving-frame identity isolated in the previous reports:

```lean
DeltaGammaFirstSlotTraceFieldCovariantDerivativeAt gt t₀ x
```

The obstruction is not the trace C² predicate anymore; that is now discharged
from `TimeVariationTraceEntriesExtContMDiffAt gt t₀ x 2`.

The remaining proof must identify the derivative of the moving fiberwise trace

```lean
fun y : M =>
  deltaGammaFirstSlotTraceFieldAt gt t₀ y (extend E w y)
```

with the fixed-base contraction `deltaGammaContractionDerivAt gt t₀ x u w`.
The model-space proof uses:

```lean
deltaGamma_trace_slot_cancel
deltaGammaContractionDeriv_slot_cancelled
deltaGammaContractionDeriv_eq_covTensor1Deriv
```

Those rely on a fixed global basis, trace cyclicity for the Christoffel action,
and an `fderiv`-of-bundled-trace lemma.  In the closed file, the target trace
field rebuilds `Module.finBasis ℝ (TM y)` in each fiber, while
`deltaGammaContractionDerivAt` traces `covDeltaGammaDerivAt` using the base
fiber `TM x` and canonical extensions.  The missing closed theorem is the
two-point moving-frame transport statement showing that these derivative
descriptions agree, with the Levi-Civita corrections cancelling by the closed
analogue of the model trace-cyclicity lemma.

## Verification

Checked forbidden placeholders:

```bash
rg -n "\b(sorry|admit|axiom|native_decide)\b" \
  Poincare/Global/ScalarVariation.lean Poincare/Global/ScalarEvolution.lean
```

Result: no matches.

Exact requested build:

```bash
lake build Poincare.Global.ScalarVariation Poincare.Global.ScalarEvolution
```

Result: success, with pre-existing linter warnings.
