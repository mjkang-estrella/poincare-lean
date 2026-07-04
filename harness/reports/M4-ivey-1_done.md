# M4-ivey-1 done: Goal 6 improved traceless pinching statement layer

## Implemented surface

- `ClosedSmoothRiemannianMetric.tracelessRicciNormSqAt_eq`
- `ClosedSmoothRiemannianMetric.tracelessRicciNormSqAt_eq_zero_iff_ricciEndoAt_eq_smul_id`
- `ClosedSmoothRiemannianMetric.tracelessPinchingAt`
- `ClosedSmoothRiemannianMetric.tracelessPinchingAt_eq`
- `ClosedSmoothRiemannianMetric.tracelessPinchingAt_nonneg_of_scalarAt_pos`
- `PinchingAlgebra.diagonalTracelessPinching3`
- `PinchingAlgebra.diagonalTracelessRicciReactionTrace3`
- `PinchingAlgebra.diagonalTracelessPinchingReactionNumerator3`
- `PinchingAlgebra.pinchedTracelessAdmissibleDelta3`
- `PinchingAlgebra.TracelessPinchingEigenvalueImprovementLemma3`
- `ClosedSmoothRiemannianMetric.tracelessPinchingGradientDrift3At`
- `ClosedSmoothRiemannianMetric.tracelessPinchingGradientDampingAt`
- `ClosedSmoothRiemannianMetric.pinchingTracelessRicciReactionTrace3At`
- `ClosedSmoothRiemannianMetric.tracelessPinchingReactionTermAt`
- `ClosedSmoothRiemannianMetric.SatisfiesTracelessPinchingImprovementEvolutionAt`

## Coefficient pins

The improved reaction numerator is pinned as

```text
old Hamilton-Schur numerator + 2 delta |Ric|^2 |Ric°|^2.
```

Formal pins:

- `(1,1,1)`: `diagonalTracelessPinchingReactionNumerator3 ... = 0`.
- `(1,1,2)`: `-16 + 8 * delta`.
- `(1,2,3)`: `-64 + 56 * delta`.
- near-degenerate `epsilon = 1/10`, eigenvalues `(1, 9/2, 9/2)`: `-49 + (4067 / 6) * delta`, saturated at `delta = 6 / 83`.

The admissible range recorded for the eigenvalue statement is

```text
0 <= delta <= 6 epsilon^2 / (1 - 2 epsilon + 3 epsilon^2).
```

## Roadmap

1. Prove the general-exponent quotient calculus for `R^(2 - delta)`.
2. Prove `TracelessPinchingEigenvalueImprovementLemma3`.
3. Assemble the improved evolution target from Ricci-norm and scalar evolution.
4. Reuse the completed-gradient square nonnegativity and prove its exponent coefficient.
5. Combine the evolution inequality with the scalar-minimum blow-up from Goal 3.
6. State and prove the closed-flow pinching-improvement theorem.

## Verification

- `lake env lean Poincare/Global/RicciNorm.lean` succeeded.
- `lake build Poincare.Global.RicciNorm Poincare.Global.ScalarVariation` succeeded.
- `rg -n "\b(sorry|admit|axiom|native_decide)\b" Poincare/Global/RicciNorm.lean Poincare/Global/ScalarVariation.lean` returned no matches.
- `git diff --check` succeeded.
