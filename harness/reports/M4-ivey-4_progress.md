# M4-ivey-4 progress: traceless numerator bridges through vocabulary conversion

## Completed commits

1. `eadfcd75` - `Add traceless Ricci numerator bridges`
   - `ClosedSmoothRiemannianMetric.hasDerivAt_tracelessRicciNormSqAt_of_ricciNormSq_and_scalar_sq`
   - `ClosedSmoothRiemannianMetric.inner_gradientAt_tracelessRicciNormSqAt_scalarAt`
   - `ClosedSmoothRiemannianMetric.laplacianAt_tracelessRicciNormSqAt_eq`

2. `cbd0d005` - `Assemble traceless Ricci numerator parabolic form`
   - `hasDerivAt_tracelessRicciNormSqAt_eq_laplacianAt_sub_two_covNormSq_add_scalarGrad_add_tracelessReactionTrace3`

3. `3df043fe` - `Instantiate traceless rpow spatial expansion`
   - `ClosedSmoothRiemannianMetric.tracelessPinching_spatial_expansion`

4. `b2568c68` - `Add traceless pinching vocabulary conversions`
   - `ClosedSmoothRiemannianMetric.tracelessPinching_spatial_expansion_with_numerator_bridge`
   - `ClosedSmoothRiemannianMetric.tracelessPinchingReactionTermAt_eq_rpow_reaction_expansion`

## Remaining item 5 obstruction

Combining the exact numerator parabolic formula with the generic quotient
expansion gives the expected zeroth-order reaction term and the named drift.
The gradient part is not exactly the current
`tracelessPinchingGradientDampingAt` when `p = 2 - δ`.

With

- `R = g.scalarAt x`
- `N = g.ricciNormSqAt x`
- `A = covRicciNormSqAt g x`
- `B = g.pinchingMixedGradientPairingAt x`
- `S = g.scalarGradNormSqAt x`
- `p = 2 - δ`

the assembled gradient numerator is

```text
-2 * R^2 * A + 2 * p * R * B + (δ / 3) * R^2 * S - p * N * S
```

while the existing damping vocabulary is

```text
-2 * (R^2 * A - 2 * R * B + N * S)
```

Their difference is the gradient-defect term

```text
δ * ((N + R^2 / 3) * S - 2 * R * B)
```

Thus the final improved evolution inequality still needs a proven sign/control
lemma for the literal goal

```lean
δ * ((g.ricciNormSqAt x + (g.scalarAt x) ^ 2 / 3) *
      g.scalarGradNormSqAt x
    - 2 * g.scalarAt x * g.pinchingMixedGradientPairingAt x) ≤ 0
```

or the final target must carry this gradient-defect term explicitly.  The
available eigenvalue lemma
`PinchingAlgebra.TracelessPinchingEigenvalueImprovementLemma3_holds` controls
the zeroth-order diagonal reaction numerator; it does not by itself control
this spatial gradient defect.

## Verification so far

- `lake env lean Poincare/Global/ScalarEvolution.lean` succeeded after each
  committed proof unit, with existing linter warnings.
- The placeholder-token scan over `Poincare/Global/ScalarEvolution.lean`
  returned no matches after each proof unit.
