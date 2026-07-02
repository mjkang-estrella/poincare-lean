# M3-predicates-6 blocked report

## Verified native progress

Added closed-vocabulary spatial metric and inverse-raise cancellation lemmas to
`Poincare/Global/ScalarVariation.lean`, without using the closed-to-model
transport route:

- `spatialMetricDerivAt`: the spatial derivative of the metric pairing on
  canonical extensions of fixed tangent vectors.
- `spatialMetricDerivAt_eq_leviCivita`: the fixed-vector metric-compatibility
  identity
  `∂ᵥ g(p,q) = g(∇ᵥ p,q) + g(p,∇ᵥ q)` in the closed connection vocabulary.
- `leviCivitaRightCovectorLinearAt` and `leviCivitaRightCovectorAt`: linear and
  continuous-linear packaging of the covector `q ↦ g(p, ∇ᵥ q)`.
- `spatialMetricDualVectorDerivAt`: the closed algebraic candidate for the
  spatial derivative of a raised fixed covector.
- `spatialMetricDualVectorDerivAt_inner_apply`: pairing that candidate with the
  metric gives `-∂ᵥ g(♯φ, -)`, i.e. the native analogue of the metric-
  compatibility cancellation behind the model inverse-raise derivative.

These are the native step-1 and step-2 ingredients requested by the task.  The
work is committed in two verified units:

- `19b5648b Add closed spatial metric derivative compatibility`
- `7fd1a512 Add closed spatial raise cancellation algebra`

## Remaining blocker

I did not discharge the full nonzero `TraceMetricVariationDerivAt` predicate.

The remaining gap is now narrower than the prior chart/model transport blocker,
but it is still a real missing closed theorem:

1. A manifold derivative theorem for the raised dual vector path
   `y ↦ metricDualVectorAt g y φ`, with derivative identified as
   `spatialMetricDualVectorDerivAt g x v φ`.
2. A closed product-rule bridge from fixed-vector component differentiability
   `VariationSpatiallyDifferentiableAt h x` plus slot-linearity of `h` to the
   canonical-extension derivative in `covTensor2DerivAt`.
3. The final finite-sum trace algebra turning the adjoint connection covector
   term into the first-slot Christoffel correction.

Adding any hypothesis that directly equates the contracted `covTensor2DerivAt`
sum with `extDerivFun (traceMetricVariationAt ...)` would just restate
`TraceMetricVariationDerivAt`, so I stopped under the worker contract.

## Verification

Checked the changed Lean file:

```text
lake env lean Poincare/Global/ScalarVariation.lean
```

Result: success, with the pre-existing unused-section-variable warnings in
`ScalarVariation.lean`.

Checked the requested modules:

```text
lake build Poincare.Global.ScalarVariation Poincare.Global.ScalarEvolution
```

Result: success (`Build completed successfully (2806 jobs).`), with existing
warnings in replayed dependencies and the same pre-existing
`ScalarVariation.lean` unused-section-variable warnings.

Checked for forbidden placeholders in the target modules:

```text
rg -n "\b(sorry|admit|axiom)\b" \
  Poincare/Global/ScalarVariation.lean Poincare/Global/ScalarEvolution.lean
```

Result: no matches.
