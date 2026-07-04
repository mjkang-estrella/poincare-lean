# M4-ivey-3 done: general-exponent quotient calculus

## Implemented surface

- `quotientRpowDerivativeAt`
- `hasDerivAt_quotient_rpow_of_derivatives`
- `ClosedSmoothRiemannianMetric.hasDerivAt_tracelessPinchingAt_of_scalar_and_tracelessNorm`
- `ClosedSmoothRiemannianMetric.gradientAt_rpow_const_of_ne`
- `ClosedSmoothRiemannianMetric.gradientAt_scalar_rpow`
- `ClosedSmoothRiemannianMetric.laplacianAt_rpow_const_of_ne`
- `ClosedSmoothRiemannianMetric.laplacianAt_scalar_rpow`
- `ClosedSmoothRiemannianMetric.quotient_rpow_spatial_expansion_of_eventually_product_rule`
- `ClosedSmoothRiemannianMetric.pinchingGradientSquareAt_rpowCoefficientExpansion`
- `ClosedSmoothRiemannianMetric.tracelessPinchingGradientDampingAt_eq_rpowCoefficientExpansion`

## Commit units

- `ba65c254` - real-power composition lemmas.
- `55cb025b` - general `u / R^p` quotient derivative and spatial quotient expansion.
- `3facf6af` - real-power completed-square coefficient bridge.

## Scope notes

- `Poincare/Global/RicciNorm.lean` was not modified.
- `Poincare/Global/ScalarVariation.lean` was not modified.
- The real-power Laplacian and spatial quotient lemmas follow the current
  project Laplacian APIs, so they carry all-point denominator nonzero and
  differentiability hypotheses for the denominator function. The theorem-facing
  quotient domain is still positive scalar curvature at the point; the evolution
  assembly can either discharge the all-point hypotheses on its positive-scalar
  region or add a local-congruence weakening layer.

## What roadmap item 3 still needs

The improved evolution assembly is not complete yet. It still needs:

1. A parabolic formula for
   `tracelessRicciNormSqAt = ricciNormSqAt - scalarAt^2 / n`, combining the
   existing Ricci-norm evolution with Hamilton scalar evolution and the
   scalar-square derivative.
2. Gradient and Laplacian bridge lemmas for `tracelessRicciNormSqAt`, especially
   the numerator-gradient pairing
   `inner (gradient tracelessRicciNormSqAt) (gradient scalarAt)` in terms of the
   existing `pinchingMixedGradientPairingAt` and `scalarGradNormSqAt`.
3. Instantiation of
   `quotient_rpow_spatial_expansion_of_eventually_product_rule` with
   `u = tracelessRicciNormSqAt`, `q = tracelessPinchingAt . delta`, and
   `p = 2 - delta`, including the local product equality on the positive-scalar
   domain and the gradient-field regularity hypotheses for `q`, `R^p`, and the
   product.
4. Algebra converting the generic quotient expansion into the statement-layer
   vocabulary:
   `tracelessPinchingGradientDrift3At`,
   `tracelessPinchingGradientDampingAt`, and
   `tracelessPinchingReactionTermAt`.
5. Final assembly with the 3D Ricci-norm parabolic estimate, scalar evolution,
   and the `TracelessPinchingEigenvalueImprovementLemma3` reaction sign lemma.

## Verification

- `lake env lean Poincare/Global/ScalarEvolution.lean` succeeded.
- `lake build Poincare.Global.ScalarEvolution Poincare.Global.ScalarVariation`
  succeeded.
- `rg -n "\b(sorry|admit|axiom|native_decide)\b" Poincare/Global/ScalarEvolution.lean Poincare/Global/ScalarVariation.lean`
  returned no matches.
- `git diff --check` succeeded.
