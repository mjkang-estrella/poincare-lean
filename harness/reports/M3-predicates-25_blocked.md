# M3-predicates-25 blocked report

## Verified progress

This worker added two proof-bearing lemmas to
`Poincare/Global/ScalarVariation.lean`.

1. `deltaGammaDivergenceAt_eq_inner_sum`

   This rewrites the coordinate definition of
   `deltaGammaDivergenceAt gt t0 x u w`

   ```lean
   sum_i (finBasis.coord i)
     (covDeltaGammaDerivAt gt t0 x (b i) u w)
   ```

   into the metric-dual pairing form

   ```lean
   sum_i g.inner x
     (covDeltaGammaDerivAt gt t0 x (b i) u w) (sharp i)
   ```

   using the existing `coord_eq_inner_metricDualVectorAt` fiber identity.

2. `deltaGammaDivergenceAt_eq_innerTraceFieldDerivative_of_entryBridge`

   This records the exact remaining cyclic trace identity as an explicit
   hypothesis and proves that it is sufficient, together with the already
   verified scalar-entry bridge
   `deltaGammaInnerTraceFieldDerivativeTraceAt_of_entryBridge`, to identify
   the divergence contraction with the corrected derivative of the lower-slot
   inner trace field:

   ```lean
   deltaGammaDivergenceAt gt t0 x w u
     =
   extDerivFun
       (fun y => deltaGammaInnerTraceFieldAt g gt t0 y (extend E w y))
       x u
     - deltaGammaInnerTraceFieldAt g gt t0 x
       (g.leviCivita (extend E w) x u)
   ```

   No frozen target statement was changed.

## Remaining exact cyclic obligation

The explicit hypothesis of
`deltaGammaDivergenceAt_eq_innerTraceFieldDerivative_of_entryBridge` is the
remaining cyclic trace identity:

```lean
∀ u w : TM x,
  (letI : FiniteDimensional ℝ (TM x) :=
      inferInstanceAs (FiniteDimensional ℝ E)
   let g : ClosedSmoothRiemannianMetric n M := gt t₀
   let b := Module.finBasis ℝ (TM x)
   let sharp : Fin (Module.finrank ℝ (TM x)) → TM x :=
     fun i ↦ metricDualVectorAt g x (b.coord i)
   ∑ i, g.inner x (covDeltaGammaDerivAt gt t₀ x u (b i) (sharp i)) w)
  =
  (letI : FiniteDimensional ℝ (TM x) :=
      inferInstanceAs (FiniteDimensional ℝ E)
   let g : ClosedSmoothRiemannianMetric n M := gt t₀
   let b := Module.finBasis ℝ (TM x)
   let sharp : Fin (Module.finrank ℝ (TM x)) → TM x :=
     fun i ↦ metricDualVectorAt g x (b.coord i)
   ∑ i, g.inner x (covDeltaGammaDerivAt gt t₀ x (b i) w u) (sharp i))
```

This is exactly the direction/slot swap described by the task.

## Why the full identity is still blocked

The closed file currently has first-order Koszul and trace machinery, but it
does not yet expose the model route's second-covariant-derivative layer:

- a closed `covDeltaGamma_koszul` expansion of `g((nabla_v deltaGamma)(p,q),z)`
  into second derivatives of `timeDerivAt gt t0` plus first-order correction
  terms,
- closed analogues of the model `covTensor2SndDeriv` bilinearity and
  double-trace swap lemmas,
- the correction-cancellation lemmas needed to compare both contracted sides
  after expansion.

Because those ingredients are absent, I did not assert the cyclic trace
identity as a theorem.  The new bridge pins down the exact remaining statement
and verifies that this identity is precisely what converts the existing
inner-trace derivative reduction into the divergence contraction.

## Current remaining predicate frontier

No top-level Hamilton predicate was discharged in this slice.  The current
frontier remains:

- `DeltaGammaInnerTraceFieldCovariantDerivativeAt gt t0 x`
- `DeltaGammaDivergenceTraceInnerHessianDerivativeAt gt t0 x`
- `TensorDoubleDivergenceTimeDerivNegTwoRicciAt gt t0 x`
- `TraceMetricVariationLaplacianTimeDerivNegTwoRicciAt gt t0 x`
- `TensorDoubleDivergenceNegTwoRicciLinearityAt (gt t0) x`
- `ClosedContractedBianchiAt (gt t0) x`

The new code reduces the first item to the cyclic trace identity plus the
already verified inner-trace derivative bridge.

## Verification

Focused check:

```bash
lake env lean Poincare/Global/ScalarVariation.lean
```

Result: success, with existing linter warnings and `simp` suggestions only.

Requested build:

```bash
lake build Poincare.Global.ScalarVariation Poincare.Global.ScalarEvolution
```

Result: success (`Build completed successfully (2806 jobs).`), with existing
warnings from replayed dependencies and existing linter warnings in
`ScalarVariation.lean`.

No `sorry`, `admit`, `axiom`, or `native_decide` occurs in
`Poincare/Global/ScalarVariation.lean` or
`Poincare/Global/ScalarEvolution.lean`.
