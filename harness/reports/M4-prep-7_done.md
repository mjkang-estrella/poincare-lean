# M4-prep-7 done

## Slice 4

`Poincare/Global/ScalarVariation.lean` now has the planned pointwise
commutation target:

- `RicciSecondDerivCommutationAt`

The statement is the report-authored predicate:

```lean
∀ u w : TM x,
  deltaRicciSecondDerivContractionAt g (negTwoRicciVariationField g) x u w =
    lichnerowiczLaplacianAt g (ricciVariationField g) x u w
      + ricciQuadraticAt g x u w
```

Committed as:

- `11a43ca1 Add Ricci second derivative commutation predicate`

## Slice 5

The expanded curvature-commutation predecessor and bridge are now landed:

- `RicciSecondDerivCurvatureCommutationAt`
- `RicciSecondDerivCommutationAt.of_closed_bianchi`

`RicciSecondDerivCurvatureCommutationAt` exposes the full
`rough - 2 * Rm + Ric-action + quadratic` RHS.  The bridge folds the first
three terms back through `lichnerowiczLaplacianAt`, while preserving the exact
planned hypotheses:

- `ClosedRicciDerivativeExpansionAt g x`
- pointwise cyclic second Bianchi in `closedCurvatureCovDerivAt`
- `RicciSecondDerivCurvatureCommutationAt g x`

Committed as:

- `411fae36 Add Ricci curvature commutation bridge`

## Verification

- `lake build Poincare.Global.ScalarVariation` succeeded after slice 4.
- `lake build Poincare.Global.ScalarVariation` succeeded after slice 5.
- `rg -n '\b(sorry|admit|axiom|native_decide)\b' Poincare/Global/ScalarVariation.lean`
  returned no matches.
- `git diff --check` succeeded.
