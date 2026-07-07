# M5-rigid-10 done: endpoint differential surface packaged

## Artifact

- Added `Poincare/Global/CartanDifferential.lean`.
- Did not edit `Poincare.lean` or any existing proof module.

## Verified theorem surfaces

The new module packages the endpoint differential surface as composable
chart-level statements:

```lean
Poincare.CartanDifferential.endpoint_decomposition_homogeneity
Poincare.CartanDifferential.expAt_chart_radial_hasDerivAt_of_uniform_geodesicFlow
Poincare.CartanDifferential.expAt_chart_transverse_endpoint_hasDerivAt_eq_sin_div_smul
Poincare.CartanDifferential.expAt_chart_transverse_hasDerivAt_and_radial_pair_eq_zero
```

The transverse endpoint theorem performs the homogeneity bookkeeping from
`t • (v + s • (t⁻¹ • η))` to the actual endpoint perturbation
`t • v + s • η`, exposing the `(sin t) / t` factor.  The combined transverse
surface also ties the same derivative vector to the endpoint Gauss
cross-pairing.

## Cartan chain rule

The chart-coordinate Cartan composition is isolated as:

```lean
Poincare.CartanDifferential.cartanChartMap
```

with strict derivative chain-rule statements:

```lean
Poincare.CartanDifferential.cartanChartMap_hasStrictFDerivAt_of_expAtChart
Poincare.CartanDifferential.cartanChartMap_hasStrictFDerivAt_anchor
```

The general theorem composes the inverse derivative of the source
`OpenPartialHomeomorph`, the tangent alignment, and the target exponential
strict derivative.  The anchor theorem specializes the chain to derivative
`L`.

## Pullback/local-isometry boundary

The full pullback identity was not asserted as a theorem in this task.  The
remaining algebra after the endpoint differential facts is isolated as:

```lean
Poincare.CartanDifferential.tangentAlignment_scaled_radial_transverse_pair
```

This records that matching radial and transverse scale factors are preserved
by the rigid-9 tangent alignment/Gram-decomposition algebra.

## Verification

- `lake build Poincare.Global.CartanDifferential`
- Result: build completed successfully (`Build completed successfully (3144 jobs)`).
- Forbidden-placeholder grep on `Poincare/Global/CartanDifferential.lean`: no
  matches.
- `git diff --check -- Poincare/Global/CartanDifferential.lean`: clean.
