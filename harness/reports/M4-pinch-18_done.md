# M4-pinch-18 done: honest quotient evolution with explicit reaction remainder

## Pre-proof coefficient pins

The corrected quotient target keeps the reaction contribution explicit.  Write

```text
R = scalar, N = |Ric|^2, Q = N / R^2,
N_react = |Ric|^2 reaction trace + Ricci-flow metric-motion trace,
R_react = 2N,
(R^2)_react = 2R R_react = 4RN.
```

The named reaction remainder is normalized by

```text
(2 / R^4) P_reaction
  = N_react / R^2 - N (R^2)_react / R^4
  = N_react / R^2 - 2N R_react / R^3,
P_reaction = (R^2 N_react - N (R^2)_react) / 2.
```

Space form `(lambda, lambda, lambda)`:

```text
R = 3 lambda, N = 3 lambda^2,
N_react = 12 lambda^3, (R^2)_react = 36 lambda^3,
P_reaction = 0,
quotient reaction = 0.
```

Non-Einstein `(1,1,2)`:

```text
R = 4, N = 6,
N_react = -8 + 40 = 32, (R^2)_react = 96,
P_reaction = (16 * 32 - 6 * 96) / 2 = -32,
quotient reaction = 2 * (-32) / 4^4 = -1/4.
```

Non-Einstein `(1,2,3)`:

```text
R = 6, N = 14,
N_react = -24 + 144 = 120, (R^2)_react = 336,
P_reaction = (36 * 120 - 14 * 336) / 2 = -192,
quotient reaction = 2 * (-192) / 6^4 = -8/27.
```

These pins are formalized in `Poincare.Global.RicciNorm` as
`diagonalPinchingReactionRemainder3_spaceForm`,
`diagonalPinchingReactionQuotient3_one_one_two`, and
`diagonalPinchingReactionQuotient3_one_two_three`.

## Correction

The old `SatisfiesHamiltonPinchingEvolutionInequality3At` target is retained
only as correction history.  Its traceless-Ricci damping term is stronger than
the reaction supplied by the proven parabolic forms on `(1,1,2)`.

The corrected target is `SatisfiesPinchingQuotientEvolutionAt`: it separates
the completed gradient square from the reaction remainder.  The sign of the
reaction remainder under 3D Ricci nonnegativity is deliberately left for step 5.

## Implemented commits

- `b864dfae` Correct pinching quotient target.
- `e6fc2761` Add quotient product-rule lemmas.
- `e8602ec7` Assemble pinching quotient evolution.

## Formalized surface

- `pinchingGradientSquareAt`: honest metric-orthogonal sum of squares for
  `R * nabla Ric - nabla R tensor Ric`.
- `pinchingGradientSquareAt_nonneg` and `pinchingGradientDampingAt_nonpos`.
- `pinchingReactionRemainderAt`: explicit normalized reaction remainder
  `(1/2) * R^2 * N_react - R * N * R_react`.
- `gradientAt_quotient_eq_of_product_rule`,
  `laplacianAt_quotient_eq_of_product_rule`, and
  `quotient_derivative_eq_of_product_rule`.
- `hasDerivAt_ricciNormSqAt_eq_laplacianAt_sub_two_covNormSq_add_reactionMotionTrace3`:
  exact Ricci-norm parabolic form before dropping `|nabla Ric|^2`.
- `satisfiesPinchingQuotientEvolutionAt_of_ricciFlow`: quotient assembly from
  the scalar and Ricci-norm parabolic forms, with the spatial
  completed-square algebra exposed as the named hypothesis
  `PinchingQuotientCompletedSquareIdentityAt`.

## Completed-square status

The assembled theorem does not assume or prove any reaction sign.  It also does
not hide the gradient algebra in the target: the remaining spatial identity is
named explicitly as

```text
Delta N / R^2 - 2 N Delta R / R^3 - 2 |nabla Ric|^2 / R^2
  =
Delta Q + (2/R)<nabla R, nabla Q>
  - (2/R^4)|R nabla Ric - nabla R tensor Ric|^2.
```

This is the next local algebra target before the step-5 reaction-sign lemma can
be used to turn the corrected quotient evolution into a pinching estimate.

## Verification

- `lake env lean Poincare/Global/RicciNorm.lean`
- `lake build Poincare.Global.RicciNorm`
- `lake env lean Poincare/Global/ScalarVariation.lean`
- `lake build Poincare.Global.ScalarVariation`
- `lake env lean Poincare/Global/ScalarEvolution.lean`

## Step-5 outlook

The next proof obligation is the 3D reaction-sign lemma:

```text
Ric >= 0  ==>  pinchingReactionRemainderAt <= 0
```

with the corrected normalization above.  That should be proved as a separate
algebraic lemma, not bundled into the quotient-calculus assembly.
