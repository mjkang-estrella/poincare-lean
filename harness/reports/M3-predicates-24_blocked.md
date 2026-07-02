# M3-predicates-24 blocked report

## Verified progress

This worker produced three proof-bearing commits.

1. Commit `b0010ba7` adds the requested anchored Gram identity for the
   lower-slot inner trace field:
   - `deltaGammaInnerTraceFieldAt_eq_trace_in_basis`
   - `deltaGammaInnerTraceFieldAt_eq_sum_gram_inv`

   The anchored identity rewrites

   ```lean
   deltaGammaInnerTraceFieldAt g gt t₀ y w
   ```

   as

   ```lean
   ∑ i, ∑ j, (gramMatrix g x y)⁻¹ i j *
     g.inner y (deltaGammaAt gt t₀ y (gramFrame x y i)
       (gramFrame x y j)) w
   ```

   whenever `gramMatrix g x y` is invertible.

2. Commit `0c8a4548` records the entry-bridge reuse for the inner-trace
   slot order:
   - `deltaGammaInnerTraceEntry_mdiffAt_of_entryBridge`
   - `deltaGammaInnerTraceEntry_extDeriv_eq_of_entryBridge`

   These are direct re-slotting wrappers around the existing
   `DeltaGammaEntryDerivativeBridgeAt`; no new analytic assumption is added.

3. Commit `25c24c7a` proves the verified derivative reduction
   `deltaGammaInnerTraceFieldDerivativeTraceAt_of_entryBridge`.  For fixed
   `u w : TM x`, the scalar-entry bridge identifies the covariant derivative
   of the moving inner-trace field with

   ```lean
   let g : ClosedSmoothRiemannianMetric n M := gt t₀
   let b := Module.finBasis ℝ (TM x)
   let sharp i := metricDualVectorAt g x (b.coord i)
   ∑ i, g.inner x (covDeltaGammaDerivAt gt t₀ x u (b i) (sharp i)) w
   ```

   after the expected Levi-Civita correction on the test slot is subtracted.

## Remaining exact obligation

The target `DeltaGammaInnerTraceFieldCovariantDerivativeAt gt t₀ x` requires
the divergence contraction

```lean
deltaGammaDivergenceAt gt t₀ x w u
```

which unfolds to

```lean
let g : ClosedSmoothRiemannianMetric n M := gt t₀
let b := Module.finBasis ℝ (TM x)
let sharp i := metricDualVectorAt g x (b.coord i)
∑ i, g.inner x (covDeltaGammaDerivAt gt t₀ x (b i) w u) (sharp i)
```

The verified derivative reduction instead produces

```lean
let g : ClosedSmoothRiemannianMetric n M := gt t₀
let b := Module.finBasis ℝ (TM x)
let sharp i := metricDualVectorAt g x (b.coord i)
∑ i, g.inner x (covDeltaGammaDerivAt gt t₀ x u (b i) (sharp i)) w
```

Thus the remaining missing statement is the cyclic trace identity

```lean
let g : ClosedSmoothRiemannianMetric n M := gt t₀
let b := Module.finBasis ℝ (TM x)
let sharp i := metricDualVectorAt g x (b.coord i)
∑ i, g.inner x (covDeltaGammaDerivAt gt t₀ x u (b i) (sharp i)) w
  =
∑ i, g.inner x (covDeltaGammaDerivAt gt t₀ x (b i) w u) (sharp i)
```

or an equivalent honest theorem deriving it from the metric-variation
regularity already in scope.

## Why this is blocked

The contraction-side proof only needed trace cyclicity for the Levi-Civita
action on a single endomorphism trace; that is exactly what
`deltaGammaFirstSlotTrace_leviCivita_slot_cancel` proves.

The divergence side needs more than lower-slot symmetry of `deltaGammaAt`.
It must move the covariant-derivative direction from the external `u` slot
into the traced basis slot and simultaneously rotate the output pairing.  I
did not find an existing closed lemma that gives this cyclic trace identity
for `covDeltaGammaDerivAt`, and it does not follow from
`DeltaGammaEntryDerivativeBridgeAt` alone.

Because the frozen adapter

```lean
deltaGammaDivergenceTraceInnerHessianDerivativeAt_of_innerTraceField
```

waits on `DeltaGammaInnerTraceFieldCovariantDerivativeAt`, the final target

```lean
DeltaGammaDivergenceTraceInnerHessianDerivativeAt gt t₀ x
```

remains open.

## Current remaining predicate list

For the scalar-variation/Hamilton route in the current files, after the
already-closed contraction-side cascade, the exact remaining non-regularity
frontier is:

- `DeltaGammaInnerTraceFieldCovariantDerivativeAt gt t₀ x`
- consequently `DeltaGammaDivergenceTraceInnerHessianDerivativeAt gt t₀ x`
- `TensorDoubleDivergenceTimeDerivNegTwoRicciAt gt t₀ x`
- `TraceMetricVariationLaplacianTimeDerivNegTwoRicciAt gt t₀ x`
- `TensorDoubleDivergenceNegTwoRicciLinearityAt (gt t₀) x`
- `ClosedContractedBianchiAt (gt t₀) x`

The regularity/package hypotheses still present in the Hamilton wrappers are
`ClosedRicciFlowExtensionRegularAt`, `MetricFlowRegularAt`,
`TimeDifferentiableAt`, and the derivative of `metricRaiseContinuousAt`.

## Verification

Focused check after the proof-bearing commits:

```bash
lake env lean Poincare/Global/ScalarVariation.lean
```

Result: success, with existing linter warnings and `simp` suggestions only.

