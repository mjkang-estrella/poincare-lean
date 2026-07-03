# M4-prep-4 done

## Trace obligations

`Poincare/Global/ScalarVariation.lean` now has a raw tensor version of the
second-order H-slot trace commute:

- `covTensor2SecondDerivAt_Hslot_trace_eq_hessianAt`

This is the non-time-variation analogue of
`covTensor2SecondDerivAt_timeDeriv_Hslot_trace_eq_hessianAt`; it keeps the
same Gram-route proof structure and exposes the honest inputs explicitly:
first-order trace differentiability for the tensor, differentiability of its
covariant derivative, bilinearity in both tensor slots, a bilinear-form wrapper,
and gradient differentiability for the scalar trace.

The two Ricci trace obligations are now discharged as theorem-producing
bridges:

- `ricciActionRicciTraceAt` proves `RicciActionRicciTraceAt g x`.
- `roughTensorLaplacianRicciTraceAt_of_traceSecondRegularity` proves
  `RoughTensorLaplacianRicciTraceAt g x` from the honest second-regularity
  package `RicciEvolutionTraceSecondRegularityAt g x`.

`RicciActionRicciTraceAt` is purely fiberwise linear algebra: each Ricci-action
slot is identified with the diagonal coordinate of `Ric♯ ∘ Ric♯`, then
`ricciNormSqAt_eq_trace` closes the trace as `2 * |Ric|²`.

`RoughTensorLaplacianRicciTraceAt` is the requested second-order trace commute
for the Ricci field: the raw H-slot theorem is specialized to
`ricciVariationField g`, the canonical first-order Ricci regularity supplies
`CovTensor2ExtDifferentiableAt`, and the new second-regularity package supplies
the Gram-route `C²` trace entries plus differentiability of `∇Ric`.

## Trace consistency chain

New chain theorems:

- `ricciEvolutionTraceIdentitiesAt_of_traceSecondRegularity`
- `ricciEvolution_rhs_trace_eq_hamilton_rhs_of_traceSecondRegularity`

Thus the wired trace-consistency lemma is unconditional modulo the honest
class `RicciEvolutionTraceSecondRegularityAt`: the traced Ricci-evolution RHS
matches the Hamilton scalar RHS

```lean
g.laplacianAt (fun y ↦ g.scalarAt y) x + 2 * g.ricciNormSqAt x
```

with no remaining packaged trace identities.

## Roadmap update

The trace-validation side of `SatisfiesRicciEvolutionAt` is closed modulo the
explicit second-regularity class above.  The sole remaining mathematical
content for deriving `SatisfiesRicciEvolutionAt` from Ricci flow is now subtask
1: the pointwise Ricci-identity commutation campaign proving the Ricci tensor
evolution equation itself.

## Verification

- `lake build Poincare.ChartIdentification` succeeded after refreshing the
  chart-identification artifact.
- `lake env lean Poincare/Global/ScalarVariation.lean` succeeded.
- `lake build Poincare.Global.ScalarVariation Poincare.Global.ScalarEvolution`
  succeeded: `Build completed successfully (2806 jobs).`
- `rg -n '\b(sorry|admit|axiom|native_decide)\b' Poincare/Global/ScalarVariation.lean Poincare/Global/ScalarEvolution.lean`
  returned no matches.
- `git diff --check` succeeded.
