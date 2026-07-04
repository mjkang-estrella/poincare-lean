# M4-pinch-21 done: spatial expansion fires quotient evolution

## Formalized

- Proved the two Gram bridges:
  - `ClosedSmoothRiemannianMetric.pinchingMixedGradientPairingAt_eq_covRicciRicciPairingAt_gradientAt_scalarAt`
  - `ClosedSmoothRiemannianMetric.pinchingScalarRicciGradientProductAt_eq_scalarGradNormSqAt_mul_ricciNormSqAt`
- Added local eventual-product quotient rules:
  - `ClosedSmoothRiemannianMetric.gradientAt_quotient_eq_of_eventually_product_rule`
  - `ClosedSmoothRiemannianMetric.laplacianAt_quotient_eq_of_eventually_product_rule`
- Proved `ClosedSmoothRiemannianMetric.pinchingQuotient_spatial_expansion`, deriving

```text
ΔQ + (2/R)<∇R,∇Q>
  = ΔN/R² - 2 N ΔR/R³ - 4 cross/R³ + 2 rawProduct/R⁴
```

  on the positive-scalar domain, from quotient product rules, the Ricci-norm
  first-derivative pairing theorem, and the two Gram bridges.
- Renamed the previous completed-square assembler to
  `satisfiesPinchingQuotientEvolutionAt_of_ricciFlow_of_completed_square`.
- Kept
  `satisfiesPinchingQuotientEvolutionAt_of_ricciFlow_of_spatial_expansion`
  as the wrapper from explicit spatial expansion to the completed-square
  obligation.
- Restored `satisfiesPinchingQuotientEvolutionAt_of_ricciFlow` as the
  unconditional quotient evolution theorem: no completed-square or spatial
  expansion hypothesis remains, only the regularity classes consumed by the
  scalar, Ricci-norm, and quotient product-rule APIs.

## Verification

- `lake env lean Poincare/Global/ScalarEvolution.lean`
- `lake build Poincare.Global.ScalarVariation Poincare.Global.ScalarEvolution Poincare.Global.RicciNorm`

## Step-6 outlook

The next boundary is manifold-level reaction sign:

1. Use the merged RicciNorm eigenvalue reaction-sign lemmas.
2. Connect the pointwise Ricci endomorphism to a spectral decomposition under
   the required 3D/nonnegative-Ricci hypotheses.
3. Rewrite the quotient reaction remainder through the eigenvalue expression.
4. Feed the nonpositive reaction term into the maximum-principle layer.
