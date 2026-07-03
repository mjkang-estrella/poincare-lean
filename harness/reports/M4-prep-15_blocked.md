# M4-prep-15 blocked report

## Status

The differentiated free-slot contracted Bianchi bridge is proved and compiled,
but the full `RicciSecondDerivCurvatureCommutationAt` target is still blocked
on the final curvature-action trace fold.

No frozen target statement was changed and no assumption hypothesis was added
to the Ricci evolution chain.

## Verified work landed

1. Added `eventually_closedContractedBianchiOneFormAt_canonical`.
   This exports the neighborhood one-form contracted Bianchi identity from the
   existing closed trace-contraction chain.

2. Added `ClosedContractedBianchiOneFormAt.differentiated_of_near` and
   `closedContractedBianchiOneFormAt_differentiated_canonical`.
   These differentiate the neighborhood one-form identity in a free slot and
   cancel the covariant one-form correction against the Hessian correction:

   ```lean
   extDerivFun
       (fun y =>
         tensorDivergenceOneFormAt g (ricciVariationField g) y
           (extend E w y)) x u
     - tensorDivergenceOneFormAt g (ricciVariationField g) x
         (g.leviCivita (extend E w) x u)
     =
       (1 / 2 : ℝ) * g.hessianAt (fun y => g.scalarAt y) x u w
   ```

3. Added
   `covTensor2SecondDerivAt_ricciVariationField_divergence_trace_eq` and
   `covTensor2SecondDerivAt_ricciVariationField_divergence_trace_eq_half_hessian`.
   These convert the differentiated one-form Bianchi bridge into the fixed
   raised-basis trace of the Ricci second covariant derivative:

   ```lean
   ∑ i, covTensor2SecondDerivAt g (ricciVariationField g) x
     u (b i) (sharp i) w
   =
     (1 / 2 : ℝ) * g.hessianAt (fun y => g.scalarAt y) x u w
   ```

4. Added
   `covTensor2SecondDerivAt_ricciVariationField_Hslot_trace_eq_hessianAt_scalar`.
   This identifies the H-slot trace with the scalar Hessian:

   ```lean
   ∑ j, covTensor2SecondDerivAt g (ricciVariationField g) x
     u w (b j) (sharp j)
   =
     g.hessianAt (fun y => g.scalarAt y) x u w
   ```

5. Added
   `deltaRicciSecondDerivContractionAt_negTwoRicci_eq_rough_sub_curvatureActions`.
   This is the assembled Hessian cancellation.  After substituting
   `h = -2 Ric`, the differentiated Bianchi bridge cancels the remaining
   scalar Hessian terms and reduces the contraction to:

   ```lean
   roughTensorLaplacianAt g (ricciVariationField g) x u w
     - CAu - CAw
   ```

   where

   ```lean
   CAu =
     ∑ i, covTensor2SecondDerivCurvatureActionAt
       g (ricciVariationField g) x (b i) u w (sharp i)

   CAw =
     ∑ i, covTensor2SecondDerivCurvatureActionAt
       g (ricciVariationField g) x (b i) w u (sharp i)
   ```

## Blocking point

The remaining atom is now purely algebraic in the curvature-action trace.  To
finish the frozen target as stated, the following fold is needed:

```lean
∀ u w : TM x,
  letI : FiniteDimensional ℝ (TM x) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  let b := Module.finBasis ℝ (TM x)
  let sharp : Fin (Module.finrank ℝ (TM x)) → TM x :=
    fun i => metricDualVectorAt g x (b.coord i)
  (∑ i, covTensor2SecondDerivCurvatureActionAt
      g (ricciVariationField g) x (b i) u w (sharp i))
    +
  (∑ i, covTensor2SecondDerivCurvatureActionAt
      g (ricciVariationField g) x (b i) w u (sharp i))
  =
    2 * lichnerowiczCurvatureAt g (ricciVariationField g) x u w
      - ricciActionOnTensorAt g (ricciVariationField g) x u w
      - ricciQuadraticAt g x u w
```

Equivalently, this is the exact residual needed to rewrite
`rough - CAu - CAw` into the frozen RHS of
`RicciSecondDerivCurvatureCommutationAt`:

```lean
roughTensorLaplacianAt g (ricciVariationField g) x u w
  - 2 * lichnerowiczCurvatureAt g (ricciVariationField g) x u w
  + ricciActionOnTensorAt g (ricciVariationField g) x u w
  + ricciQuadraticAt g x u w
```

I did not introduce this fold as an assumption or alter the frozen
`RicciSecondDerivCurvatureCommutationAt` statement.

## Verification

Commands run:

```bash
lake build Poincare.Global.ScalarVariation
lake build Poincare.Global.ScalarVariation Poincare.Global.ScalarEvolution
```

Results:

- `lake build Poincare.Global.ScalarVariation` succeeded.
- `lake build Poincare.Global.ScalarVariation Poincare.Global.ScalarEvolution`
  succeeded with existing warnings only.
