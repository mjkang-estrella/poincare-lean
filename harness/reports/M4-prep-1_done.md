# M4-prep-1 done

## Landed commits

1. `26ea5f6b` — specialized Ricci variation to the Ricci-flow velocity.
2. `d43b9d15` — added closed Ricci-evolution operator vocabulary.
3. `b659fada` — stated the closed Ricci tensor evolution target.

## New declaration surface

In `Poincare/Global/ScalarVariation.lean`:

- `deltaGamma_koszul_negTwoRicci_of_isClosedRicciFlowSolutionAt_near`
- `deltaRicciSecondDerivContractionAt`
- `deltaRicciAt_eq_secondDerivContractionAt`
- `deltaRicciAt_eq_negTwoRicci_secondDerivContractionAt_of_isClosedRicciFlowSolutionAt_near`
- `roughTensorLaplacianAt`
- `lichnerowiczCurvatureAt`
- `ricciActionOnTensorAt`
- `lichnerowiczLaplacianAt`
- `ricciQuadraticAt`
- `SatisfiesRicciEvolutionAt`
- `satisfiesRicciEvolutionAt_iff`

## Trace-consistency sanity check

The formal trace lemma was not landed in this prep slice. Informally, tracing
`SatisfiesRicciEvolutionAt` over a metric-dual basis should recover the proved
Hamilton scalar evolution shape
`d/dt scalarAt = laplacianAt scalarAt + 2 * ricciNormSqAt`.

The missing formal bridge is exactly the trace algebra for the new vocabulary:
the trace of `roughTensorLaplacianAt` on the Ricci field should give the scalar
Laplacian, while the traced curvature/Ricci-action terms together with
`ricciQuadraticAt` should reduce to `2 * ricciNormSqAt`.

## Remaining proof subtasks

1. Prove the closed Ricci-identity commutation that converts
   `deltaRicciSecondDerivContractionAt (negTwoRicciVariationField g)` into the
   Lichnerowicz-plus-quadratic vocabulary.
2. Prove metric-trace identities for `roughTensorLaplacianAt`,
   `lichnerowiczCurvatureAt`, `ricciActionOnTensorAt`, and `ricciQuadraticAt`.
3. Package canonical Ricci-field first and second spatial regularity so future
   consumers do not need to carry raw `CovTensor2*` hypotheses by hand.
4. Check the sign and slot convention of `ricciQuadraticAt` against the model
   `lichnerowiczLaplacian`/curvature-action formulas by chart reduction.
5. Assemble `SatisfiesRicciEvolutionAt` from
   `ricciVariation_eq_deltaGamma_contractions'`, the flow substitution lemmas,
   and the commutation result.
6. Add the formal trace corollary from `SatisfiesRicciEvolutionAt` to the
   already-proved `SatisfiesHamiltonScalarEvolutionAt` shape.

## Verification

- `lake env lean Poincare/Global/ScalarVariation.lean` succeeded, with only
  existing linter warnings.
- `lake build Poincare.Global.ScalarVariation Poincare.Global.ScalarEvolution`
  succeeded.
