# M5-rigid-9 blocked: Cartan pullback strict partial

## Artifact

- Added `Poincare/Global/CartanPullback.lean`.

## Verified progress

The new module proves the requested radial/transverse Gram-algebra slice at
the anchor chart metric.  The core definitions are:

```lean
Poincare.CartanPullback.radialCoeff
Poincare.CartanPullback.radialPart
Poincare.CartanPullback.transversePart
```

The main proved decomposition theorem is:

```lean
Poincare.CartanPullback.pair_eq_radial_add_transverse
```

It states that, for a symmetric bilinear chart metric `B` and a radial vector
`v` with `B v v ≠ 0`, every pair of chart vectors decomposes into the sum of
the radial-radial block and transverse-transverse block, with the mixed terms
zero by orthogonality.

The source and target anchor chart metric specializations are:

```lean
Poincare.CartanPullback.sourceAnchorChartMetric_pair_eq_radial_add_transverse
Poincare.CartanPullback.targetAnchorChartMetric_pair_eq_radial_add_transverse
```

The file also proves that a Cartan tangent alignment carries the same
radial/transverse factors across the anchors:

```lean
Poincare.CartanPullback.tangentAlignment_radialCoeff_map
Poincare.CartanPullback.tangentAlignment_radialPart_map
Poincare.CartanPullback.tangentAlignment_transversePart_map
```

These use the existing `CartanMap.TangentAlignment.map_app` metric-preservation
law and do not add assumptions.

## Verification

- `lake build Poincare.Global.CartanPullback`
- Result: build completed successfully (`Build completed successfully (3143 jobs)`).
- Forbidden-placeholder grep on `Poincare/Global/CartanPullback.lean`: no
  matches for `sorry`, `axiom`, or `native_decide`.

## Remaining boundary

The full Cartan pullback/local-isometry statement remains blocked.  The repo
now has the anchor Gram decomposition and the M5-rigid-8 transverse Jacobi
bridge, but I still did not find a proved nonzero-point differential theorem
for the fixed-time exponential that packages:

1. radial factor `1` away from the anchor,
2. transverse factor `sin ‖v‖ / ‖v‖` after homogeneity rescaling,
3. zero radial/transverse cross terms at the endpoint,
4. a PartialHomeomorph chain-rule theorem for the composed `cartanMap`.

Without those theorem surfaces, the requested pullback identity on the normal
ball would require either new hypotheses that already contain the missing
differential action or a vacuous wrapper, both disallowed by the worker
contract.
