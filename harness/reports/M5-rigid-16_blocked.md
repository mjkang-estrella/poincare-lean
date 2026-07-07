# M5-rigid-16 blocked: punctured consumer landed, source expansion still missing

## Landed strict partial

The zero-vector obstruction from `CartanSourceExpansion.not_weightedSourceEndpointExpansion_zero`
is avoided by adding a genuine punctured expansion surface, not by weakening the
metric identity.

New additive surfaces in `Poincare/Global/CartanLocalIsometry.lean`:

```lean
Poincare.CartanLocalIsometry.PuncturedWeightedSourceEndpointExpansion
Poincare.CartanLocalIsometry.PuncturedWeightedTargetEndpointExpansion
Poincare.CartanLocalIsometry.PuncturedWeightedEndpointExpansionBundle
Poincare.CartanLocalIsometry.weightedEndpointExpansionBundle_of_punctured
Poincare.CartanLocalIsometry.cartanMap_isLocalIsometry_on_punctured_normalBall_of_puncturedEndpointExpansionBundle
```

The punctured source predicate quantifies only over
`v ∈ (expAtChartOpenPartialHomeomorph (g := g) x₀).source` with `v ≠ 0`, and
keeps the original weighted full bilinear metric identity as its field.

New additive surfaces in `Poincare/Global/CartanExpansionBridge.lean`:

```lean
Poincare.CartanExpansionBridge.roundSphere_targetPuncturedWeightedEndpointExpansion
Poincare.CartanExpansionBridge.puncturedWeightedEndpointExpansionBundle_of_sourceExpansion_and_roundSphere
Poincare.CartanExpansionBridge.cartanMap_isLocalIsometry_on_punctured_normalBall_of_sourceExpansion_and_roundSphere
```

The target-side proof factors through the punctured shape immediately from the
existing unconditional round-sphere conformal-weight computation.

New file:

```lean
Poincare/Global/CartanPunctured.lean
```

Main theorem:

```lean
Poincare.CartanPunctured.cartanMap_anchor_or_punctured_localIsometry_of_sourceExpansion_and_roundSphere
```

This theorem performs the requested case split: `v = 0` uses
`CartanIsometryFinal.cartanChartMap_anchor_isLocalIsometry`, and `v ≠ 0` uses
the punctured source expansion plus the round-sphere target expansion.

## Remaining blocked statement

The missing source-side theorem is now consistently shaped as the single
punctured predicate:

```lean
CartanLocalIsometry.PuncturedWeightedSourceEndpointExpansion g x₀
  (fun v : E =>
    CartanExpansionBridge.roundSphereEndpointChartWeight p₀
      ((GeodesicTransport.expAtChartOpenPartialHomeomorph
        (g := roundSphereMetric3) p₀) (L v)))
```

I did not find an existing theorem that assembles the interval/Jacobi facts
into this full bilinear endpoint chart-metric identity.  The available
ingredients still expose conditional radial/transverse derivative and Gauss
pairing surfaces, but not the endpoint weighted bilinear source expansion
itself.  Therefore the final constant-curvature-1 source expansion and the
fully unconditional corrected local-isometry theorem are not honestly proved in
this task.

## Verification

Requested verification command:

```text
lake build Poincare.Global.CartanLocalIsometry Poincare.Global.CartanExpansionBridge Poincare.Global.CartanPunctured
```

Actual result: build completed successfully (`Build completed successfully
(3148 jobs)`).  The build emitted existing upstream warnings.

Forbidden placeholder scan:

```text
rg -n "\bsorry\b|\baxiom\b|native_decide" \
  Poincare/Global/CartanLocalIsometry.lean \
  Poincare/Global/CartanExpansionBridge.lean \
  Poincare/Global/CartanPunctured.lean
```

Actual result: no matches.

Diff whitespace check:

```text
git diff --check -- \
  Poincare/Global/CartanLocalIsometry.lean \
  Poincare/Global/CartanExpansionBridge.lean \
  Poincare/Global/CartanPunctured.lean
```

Actual result: clean.
