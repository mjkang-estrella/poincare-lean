# M5-rigid-76 blocked report

## Status

Added the speed-square reconciliation layer and verified it builds, but the
curvature-only `cartanMap_isLocalIsometry` theorem is still blocked upstream of
the scalar algebra.

The radial mismatch is resolved algebraically: the consumer scalar for the
rescaled-anchor radial block is the speed-free `T ^ 2`, not
`T ^ 2 * speed ^ 2`.

## Files changed

- `Poincare/Global/CorrectedRadial.lean`
  - Added `CorrectedRadial.timeRadialScale T := T ^ 2`.
  - Added additive source/target endpoint assembly variants using the
    speed-free radial consumer scalar.
  - Added additive common-speed final consumer variants using
    `timeRadialScale` for radial blocks and
    `JacobiNormSystem.speedPinnedScale speed T` for transverse blocks.
- `Poincare/Global/SpeedReconcile.lean`
  - New file.
  - Proves the bookkeeping identity
    `ρρ' * (T ^ 2 * speed ^ 2) =
      T ^ 2 * (ρρ' * speed ^ 2)`.
  - Rewrites `RayIdentification` radial endpoint pairings into the
    `CorrectedRadial.timeRadialScale` rescaled-anchor form.
  - Provides source and target radial-block adapters.
  - Provides a final local-isometry consumer whose radial blocks are discharged
    from ray-identification plus speed-package-shaped equalities.

## Exact remaining blocker

The new scalar-correct final consumer still needs the following non-radial and
speed/ray package facts. These are not currently exported as a combined
curvature-only package in the imported modules:

```lean
hSourceRay : (PsiS v T).1 = T • Vs
hTargetRay : (PsiT (L v) T).1 = T • Vt

hSourceEndpointSpeed :
  CovariantDerivative.chartMetric g.inner x0
      ((GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x0) v)
      Vs Vs = speed ^ 2
hTargetEndpointSpeed :
  CovariantDerivative.chartMetric roundSphereMetric3.inner p0
      ((GeodesicTransport.expAtChartOpenPartialHomeomorph
        (g := roundSphereMetric3) p0) (L v))
      Vt Vt = speed ^ 2

hSourceAnchorSpeed :
  CartanMap.sourceAnchorChartMetric g x0 (T⁻¹ • v) (T⁻¹ • v) = speed ^ 2
hTargetAnchorSpeed :
  CartanMap.targetAnchorChartMetric p0 (T⁻¹ • L v) (T⁻¹ • L v) = speed ^ 2

hSourceRadialTransverse
hSourceTransverseTransverse
hTargetRadialTransverse
hTargetTransverseTransverse
```

The radial/radial blocks are no longer assumed in the new final theorem; they
are supplied by `SpeedReconcile.source_radialPart_endpoint_pairing_eq_timeRadialScale`
and `SpeedReconcile.target_radialPart_endpoint_pairing_eq_timeRadialScale`.

## Verification

Forbidden-token scan on the touched Lean files:

```bash
rg -n "\b(sorry|admit|axiom|native_decide)\b" \
  Poincare/Global/SpeedReconcile.lean \
  Poincare/Global/CorrectedRadial.lean
```

Result: no matches.

Required build:

```bash
lake build Poincare.Global.SpeedReconcile Poincare.Global.CorrectedRadial
```

Result: passed. The build completed successfully with pre-existing imported
module warnings.
