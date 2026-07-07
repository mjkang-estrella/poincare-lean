# M5-rigid-14 blocked: endpoint expansion corrected, source bridge still missing

## Pinning outcome

The unweighted target endpoint expansion is false in the round-sphere chart.

The existing round-sphere chart computation gives

```lean
Poincare.roundSphereMetric3_chartMetric_eq
```

namely, in stereographic coordinates,

```text
G_z(u,w) = (16 / (||z||^2 + 4)^2) * <u,w>.
```

At the anchor, the chart coordinate is the stereographic origin and the factor
is `1`.  Along a great circle through the anchor, the stereographic coordinate
has radial form `z(t) = 2 * tan(t / 2) * e`; at the nonzero endpoint with
`||z|| = 2` (for example `t = pi / 2`), the factor is

```text
16 / (2^2 + 4)^2 = 1 / 4.
```

So pairing the endpoint chart metric against the same sin-Jacobi chart vectors
cannot equal the anchor pairing unless the endpoint is the anchor.  This is
formalized in the new file as:

```lean
Poincare.CartanExpansionBridge.stereographicScalarConformalFactor_two
Poincare.CartanExpansionBridge.stereographicScalarConformalFactor_two_ne_one
```

## Corrected form landed

The corrected endpoint expansion carries a shared scalar chart-weight `κ` on
both sides:

```text
source endpoint metric = κ * source anchor scaled pairing
target endpoint metric = κ * target anchor scaled pairing
```

Then the same Cartan tangent-alignment algebra cancels the common weight.

Additive surfaces added to `Poincare/Global/CartanLocalIsometry.lean`:

```lean
Poincare.CartanLocalIsometry.WeightedSourceEndpointExpansion
Poincare.CartanLocalIsometry.WeightedTargetEndpointExpansion
Poincare.CartanLocalIsometry.WeightedEndpointExpansionBundle
Poincare.CartanLocalIsometry.weightedEndpointExpansionBundle_of_metric_expansions
Poincare.CartanLocalIsometry.chartMetric_pullback_identity_of_sameWeightedFactors
Poincare.CartanLocalIsometry.cartanMap_chart_pullback_identity_of_weightedEndpointExpansionBundle
Poincare.CartanLocalIsometry.cartanMap_isLocalIsometry_on_normalBall_of_weightedEndpointExpansionBundle
```

New bridge file:

```lean
Poincare/Global/CartanExpansionBridge.lean
```

Main new theorem surfaces:

```lean
Poincare.CartanExpansionBridge.bilinear_eq_of_forall_self_eq
Poincare.CartanExpansionBridge.roundSphereEndpointChartWeight
Poincare.CartanExpansionBridge.roundSphere_chartMetric_eq_endpointWeight_mul_targetAnchor
Poincare.CartanExpansionBridge.roundSphere_targetWeightedEndpointExpansion
Poincare.CartanExpansionBridge.weightedEndpointExpansionBundle_of_sourceExpansion_and_roundSphere
Poincare.CartanExpansionBridge.cartanMap_isLocalIsometry_on_normalBall_of_sourceExpansion_and_roundSphere
```

The target side is now instantiated unconditionally from the round-sphere
conformal metric computation.  The bridge consumes a source expansion with the
same pinned target endpoint weight and then gives the corrected local-isometry
pullback identity.

## Remaining obstruction

The repo still does not expose a theorem deriving the source-side weighted full
bilinear endpoint expansion from the lower-level interval facts.  The new
polarization helper proves the bilinear promotion once a symmetric quadratic
endpoint identity is available, but the existing interval lemmas in
`CartanDifferential.lean`, `JacobiOscillator.lean`, `GaussLemmaIntegrated.lean`,
and `GeodesicSpeed.lean` still stop at conditional directional/interval
surfaces.  In particular, I did not find or prove the missing theorem that
turns those facts into

```lean
Poincare.CartanLocalIsometry.WeightedSourceEndpointExpansion
```

with the same `roundSphereEndpointChartWeight` consumed by the target side.
Therefore the unconditional normal-ball local isometry is not honestly proved
in this task.

## Verification

Requested verification command:

```text
lake build Poincare.Global.CartanLocalIsometry Poincare.Global.CartanExpansionBridge
```

Actual result: build completed successfully (`Build completed successfully
(3146 jobs)`).  The build emitted existing upstream warnings, but both target
modules built.

Forbidden placeholder scan:

```text
rg -n "\bsorry\b|\baxiom\b|native_decide" \
  Poincare/Global/CartanLocalIsometry.lean \
  Poincare/Global/CartanExpansionBridge.lean
```

Actual result: no matches.

Diff whitespace check:

```text
git diff --check -- Poincare/Global/CartanLocalIsometry.lean Poincare/Global/CartanExpansionBridge.lean
```

Actual result: clean.
