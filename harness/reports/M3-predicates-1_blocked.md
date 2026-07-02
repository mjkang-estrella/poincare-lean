# M3-predicates-1 blocked report

## Completed

- Proved the closed `covTensor2DerivAt` slot-linearity layer under explicit,
  satisfiable hypotheses:
  - `Tensor2AddLeft`, `Tensor2SMulLeft`, `Tensor2AddRight`,
    `Tensor2SMulRight`
  - `CovTensor2ExtDifferentiableAt`
  - `covTensor2DerivAt_add_deriv`, `covTensor2DerivAt_smul_deriv`
  - `covTensor2DerivAt_add_left`, `covTensor2DerivAt_smul_left`
  - `covTensor2DerivAt_add_right`, `covTensor2DerivAt_smul_right`
- Discharged `CovTensor2DerivTraceSwapAt` from those hypotheses with
  `covTensor2DerivTraceSwapAt_of_regular`.
- Specialized the trace-swap discharge to metric variations:
  `timeDerivAt` is fiberwise bilinear from `TimeDifferentiableAt`, so
  `covTensor2DerivTraceSwapAt_timeDeriv_of_regular` only requires the honest
  scalar-field differentiability condition
  `CovTensor2ExtDifferentiableAt (timeDerivAt gt t0) x`.
- Propagated the result to the inner-trace wrapper via
  `deltaGamma_innerTrace_eq_of_covTensor2Regular`, which removes the
  `CovTensor2DerivTraceSwapAt` input and leaves `TraceMetricVariationDerivAt`
  as the remaining first-order metric-compatibility input.
- Added satisfiability witnesses:
  - zero bilinearity and differentiability witnesses for the new regularity
    predicates
  - `covTensor2DerivTraceSwapAt_zero`
  - `traceMetricVariationDerivAt_const_timeDeriv`

## Blocker

The full nonzero `TraceMetricVariationDerivAt` proof is not yet available in
the closed layer.

The model theorem `fderiv_tensorMetricTrace_eq` differentiates the metric trace
by handling the derivative of the raised index and canceling the resulting
Christoffel terms by metric compatibility.  In the closed file, the trace

```lean
traceMetricVariationAt g h y
```

uses the moving raised basis vector

```lean
metricDualVectorAt g y ((Module.finBasis ℝ (TM y)).coord i)
```

but there is not yet a closed spatial theorem identifying the derivative of
that moving raised-basis vector field with the Levi-Civita correction needed
for the cancellation.  The existing `metricRaiseDerivAt` machinery is a time
derivative for metric flows at a fixed tangent fiber; it does not supply the
spatial moving-frame derivative required here.

The next proof task should add a closed spatial raise-derivative/raised-basis
bridge, then use `leviCivita_metricCompatibleAt` to prove the cancellation and
discharge `TraceMetricVariationDerivAt` for nonzero variation fields.

## Verification

```text
lake build Poincare.Global.ScalarVariation Poincare.Global.ScalarEvolution
```

Result: success.

No forbidden proof placeholder construct was added.
