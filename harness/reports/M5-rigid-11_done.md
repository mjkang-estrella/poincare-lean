# M5-rigid-11 done: Cartan local-isometry pullback assembly

## Artifact

- Added `Poincare/Global/CartanLocalIsometry.lean`.
- Did not edit `Poincare.lean` or any existing proof module.

## Verified theorem surfaces

The new module packages the shared-factor normal-coordinate vectors:

```lean
Poincare.CartanLocalIsometry.sourceScaledNormalVector
Poincare.CartanLocalIsometry.targetScaledNormalVector
Poincare.CartanLocalIsometry.transverseScale
Poincare.CartanLocalIsometry.cartanChartDifferential
```

The isolated algebra step is:

```lean
Poincare.CartanLocalIsometry.sameFactors_anchor_pair
```

It applies the rigid-10 boundary
`CartanDifferential.tangentAlignment_scaled_radial_transverse_pair`: if source
and target endpoint differentials use the same radial factor `ρ` and
transverse factor `σ`, the tangent alignment preserves the anchor pairings.

The pointwise chart-metric pullback identity is:

```lean
Poincare.CartanLocalIsometry.chartMetric_pullback_identity_of_sameFactors
Poincare.CartanLocalIsometry.cartanMap_chart_pullback_identity
```

The second theorem specializes the factors to radial factor `1` and transverse
factor `sin ‖v‖ / ‖v‖`.

The packaged chart-local-isometry statement is:

```lean
Poincare.CartanLocalIsometry.cartanMap_isLocalIsometry_on_normalBall
```

It retains the strict chain-rule derivative from
`CartanDifferential.cartanChartMap_hasStrictFDerivAt_of_expAtChart` and proves
the pointwise chart-metric pullback equality for the resulting Cartan chart
differential, assuming the source and target endpoint metric expansions have
the shared Cartan radial/transverse factors.

## Verification

- `lake build Poincare.Global.CartanLocalIsometry`
- Result: build completed successfully (`Build completed successfully (3145 jobs)`).
- Forbidden-placeholder grep on `Poincare/Global/CartanLocalIsometry.lean`: no
  matches for `sorry`, `axiom`, or `native_decide`.
- `git diff --check -- Poincare/Global/CartanLocalIsometry.lean`: clean.
