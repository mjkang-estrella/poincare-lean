# M3-predicates-4 blocked report

## Fiber-identification check

Route A's first premise is true in the current closed encoding:

```lean
example (x : M) : TangentSpace I x = E := rfl
example (x : M) :
    (TangentSpace I x →L[ℝ] TangentSpace I x) = (E →L[ℝ] E) := rfl
```

The narrow probe was checked with:

```text
lake env lean harness/fiber_probe.lean
```

and succeeded.

However, the canonical extension layer does not collapse away:

```lean
example {x : M} (p : TM x) (y : M) : extend E p y = p := rfl
```

fails with a type mismatch.  Thus the closed fiber type is definitionally the
model space, but the fields used by `covTensor2DerivAt` are still genuine
canonical extensions, and the connection-correction terms cannot be erased by
definitional reduction.

Both probes were temporary and removed.

## Completed verified progress

Added the frame-free trace-linearity kernel to
`Poincare/Global/ScalarVariation.lean`:

- `traceMetricVariationAt_eq_linearMap_trace`: direct basis-free bridge from
  the raw metric trace to `LinearMap.trace` of the raised endomorphism once the
  fiber value is packaged as a bilinear form.
- `metricTraceEndomorphismContinuousAt` and
  `traceMetricVariationAt_eq_trace_metricTraceEndomorphismContinuousAt`:
  continuous-linear packaging of the raised endomorphism.
- `traceMetricVariationAt_timeDeriv_eq_linearMap_trace`: specialization of
  the bridge to the metric time-derivative bilinear form.
- `endomorphismTraceContinuousAt` and
  `hasDerivAt_trace_endomorphismContinuousAt`: the finite-dimensional trace as
  a continuous linear functional on the fixed tangent fiber endomorphism space,
  plus the derivative rule `d(tr A) = tr(dA)` for fixed-fiber time paths.

This is exactly the part of Route A made available by the definitional
identification `TM x = E`.

## Remaining blocker

`TraceMetricVariationDerivAt` still cannot be discharged honestly from the
current closed layer.

The target is spatial and covariant:

```lean
∀ w : TM x,
  ∑ i, covTensor2DerivAt g h x w eᵢ (♯eⁱ)
    = extDerivFun (fun y ↦ traceMetricVariationAt g h y) x w
```

Route A reduces the algebraic trace to a fixed-fiber trace, but the derivative
bridge still requires a non-vacuous theorem identifying:

1. the spatial derivative of the fixed-fiber endomorphism field
   `y ↦ ♯_g(y) ∘ h♭(y)`, and
2. the contracted covariant derivative
   `∑ᵢ (∇_w h)(eᵢ, ♯eⁱ)`.

The missing term is precisely the metric-compatibility cancellation: the
derivative of the raise map must cancel the Christoffel corrections introduced
by differentiating the tensor slots through `covTensor2DerivAt`.  The existing
closed hypotheses give differentiability of `h` only through canonical
extensions (`CovTensor2ExtDifferentiableAt`), not a fixed-vector
`HasFDerivAt` theorem for the endomorphism field, and there is not yet a
spatial closed analogue of the model inverse-raise derivative chain sufficient
to prove the cancellation.

Adding a hypothesis that directly states this equality would just rename
`TraceMetricVariationDerivAt`, so I stopped under the worker contract.

## Verification

Verified the changed Lean file:

```text
lake env lean Poincare/Global/ScalarVariation.lean
```

Result: success, with only pre-existing unused-section-variable linter
warnings.

Verified the requested modules:

```text
lake build Poincare.Global.ScalarVariation Poincare.Global.ScalarEvolution
```

Result: success (`Build completed successfully (2806 jobs).`), with
pre-existing linter warnings in replayed dependencies and the existing
`ScalarVariation.lean` unused-section-variable warnings.
