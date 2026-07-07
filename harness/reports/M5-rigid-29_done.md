# M5-rigid-29 done: coefficient bridge strict partial

## Files

- Added `Poincare/Global/CartanCoefficientBridge.lean`.
- Added this report.
- Did not edit existing Lean modules, including `Poincare.lean`.

## Chosen route

I used option (a): the existing punctured/source-owned consumer shape.

The downstream weight-canceling consumer in `CartanWeightInvariant.lean` needs:

- a source-owned `CartanLocalIsometry.PuncturedWeightedSourceEndpointExpansion g x₀ κsource`;
- the unconditional round-sphere punctured target expansion already supplied by
  `CartanExpansionBridge`;
- a `CartanWeightInvariant.PuncturedWeightedAnchorPairing` comparing the
  source-owned weight with the target chart weight.

The new theorem constructs the punctured source expansion internally from the
three source endpoint coefficient blocks:

- radial-radial;
- radial-transverse;
- transverse-transverse, with the source transverse factor
  `CartanLocalIsometry.transverseScale v = sin ‖v‖ / ‖v‖` built into the
  transverse block.

It then invokes the existing source-owned weight-invariant Cartan local-isometry
consumer to produce the exp-chart pullback equality for `cartanChartMap`.

## Verified strict partial

The new module contains one isolated non-vacuous statement:

```lean
theorem Poincare.CartanCoefficientBridge.cartanMap_isLocalIsometry_on_punctured_normalBall_of_source_endpoint_pairings
```

The proof expands arbitrary endpoint chart vectors as

```lean
u = radialPart S v u + transversePart S v u
```

and similarly for `u'`.  Bilinearity plus endpoint chart-metric symmetry turns
the three coefficient blocks into the weighted source endpoint expansion.  The
anchor mixed terms are killed with the existing `CartanPullback` Gram
orthogonality lemmas.

The theorem deliberately does not claim to derive the geometric endpoint block
facts themselves; those remain the inputs supplied by the Jacobi/Gauss layer.
The anchor weight comparison remains the explicit
`PuncturedWeightedAnchorPairing` input required by the existing invariant
consumer.

## Verification

Forbidden-placeholder scan on `Poincare/Global/CartanCoefficientBridge.lean`
found no matches.

Top-level declaration scan found exactly one declaration:

```text
37:theorem cartanMap_isLocalIsometry_on_punctured_normalBall_of_source_endpoint_pairings
```

Diff whitespace check:

```bash
git diff --check
```

Actual result: success.

Required build:

```bash
lake build Poincare.Global.CartanCoefficientBridge
```

Actual result: success. Final output ended with:

```text
✔ [3151/3151] Built Poincare.Global.CartanCoefficientBridge (3.5s)
Build completed successfully (3151 jobs).
```

The build replayed existing upstream warnings.  The final verified build emitted
no warning from `Poincare/Global/CartanCoefficientBridge.lean`.
