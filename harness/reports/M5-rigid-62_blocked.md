# M5-rigid-62 blocked: bilinear unscale bridge built, scalar normalization still explicit

## Status

Added `Poincare/Global/UnscaledFeed.lean` and did not edit existing Lean
modules, including `Poincare.lean`.

The new module proves the bilinear rescale bridge for chart-metric pairings and
feeds the resulting unscaled source/target formulas into the existing
`EqualityChain` and `PairingFeed` consumer.

## Verified payload

The new module exports:

```lean
Poincare.UnscaledFeed.continuousLinearPairing_smul_smul
Poincare.UnscaledFeed.sourceAnchorChartMetric_inv_smul_inv_smul
Poincare.UnscaledFeed.targetAnchorChartMetric_inv_smul_inv_smul
Poincare.UnscaledFeed.source_unscaled_endpoint_pairing_of_rescaled_anchor_pairing
Poincare.UnscaledFeed.target_unscaled_endpoint_pairing_of_rescaled_anchor_pairing
Poincare.UnscaledFeed.hosted_endpoint_pairing_feed_of_rescaled_sin_sq_anchor_pairings
Poincare.UnscaledFeed.cartanMap_isLocalIsometry_on_normalBall_of_rescaled_sin_sq_hosted_anchor_pairings
```

The source and target conversion lemmas prove the non-vacuous bilinear step:

```lean
Real.sin T ^ 2 *
  CartanMap.{source,target}AnchorChartMetric ... (T⁻¹ • w) (T⁻¹ • w')
=
Real.sin θ ^ 2 *
  CartanMap.{source,target}AnchorChartMetric ... w w'
```

provided the scalar normalization is supplied as:

```lean
Real.sin T ^ 2 * (T⁻¹ * T⁻¹) = Real.sin θ ^ 2
```

The final theorem then consumes rescaled source and target feeds, derives the
unscaled feeds, invokes
`EqualityChain.cartanMap_isLocalIsometry_on_normalBall_of_sin_sq_hosted_anchor_pairings`,
and reaches the `cartanMap_isLocalIsometry`-shaped conclusion.

## Remaining blocker

The scalar normalization is still not discharged by an exported theorem.  The
exact identities needed to make the new bridge fire without extra assumptions
are:

```lean
hSourceScale :
  Real.sin Ts ^ 2 * (Ts⁻¹ * Ts⁻¹) = Real.sin θs ^ 2

hTargetScale :
  Real.sin Tt ^ 2 * (Tt⁻¹ * Tt⁻¹) = Real.sin θt ^ 2

hSin :
  Real.sin θt ^ 2 = Real.sin θs ^ 2
```

Equivalently, a common-factor version would need the exported chain's `θs` and
`θt` bookkeeping to identify both normalized factors:

```lean
Real.sin Tt ^ 2 * (Tt⁻¹ * Tt⁻¹) =
  Real.sin Ts ^ 2 * (Ts⁻¹ * Ts⁻¹)
```

I did not find an existing exported rigid-47-style theorem in the inspected
scale modules that supplies these identities in the exact `EqualityChain`
shape.  The target rescaled feed from `TargetPackage` can supply the target
`hTargetRescaled` hypothesis; the source side still requires the analogous
rescaled feed plus the same scalar normalization.

## Verification

Forbidden-token scan:

```bash
rg -n "\b(sorry|admit|axiom|native_decide)\b" Poincare/Global/UnscaledFeed.lean
```

Actual result: no matches.

Whitespace check:

```bash
git diff --check -- Poincare/Global/UnscaledFeed.lean
```

Actual result: success.

Required build:

```bash
lake build Poincare.Global.UnscaledFeed
```

Actual result: succeeded.  The build replayed pre-existing upstream warnings;
the new module built successfully.

Final build lines:

```text
✔ [3176/3176] Built Poincare.Global.UnscaledFeed (3.5s)
Build completed successfully (3176 jobs).
```
