# M5-rigid-77 blocked report

## Status

Added `Poincare/Global/CombinedFeed.lean` and verified it builds.

The new file proves the non-vacuous common-feed step that is available now:
under one common `(v, T, PsiS, PsiT, speed)` it derives the source and target
mixed radial/transverse endpoint blocks from the ray law plus endpoint
orthogonality, then feeds
`SpeedReconcile.cartanMap_isLocalIsometry_on_normalBall_of_ray_reconciled_decomposed_blocks`.

The requested curvature-only `cartanMap_isLocalIsometry` remains blocked:
current exports still do not provide one common-time hosted package producing
all ray, speed, orthogonality, and transverse-pairing facts simultaneously.

## File added

- `Poincare/Global/CombinedFeed.lean`
  - `radialPart_endpoint_pairing_eq_zero_of_ray_and_transverse_orthogonal`
  - `source_radial_transverse_block_eq_zero_of_ray_and_transverse_orthogonal`
  - `target_radial_transverse_block_eq_zero_of_ray_and_transverse_orthogonal`
  - `cartanMap_isLocalIsometry_of_common_ray_speed_orthogonal_transverse_feed`

## Exact remaining unco-quantified facts

The new common-feed theorem still needs these common-time facts. These are the
facts that must be produced from the hosted datum before the theorem can become
curvature-only:

```lean
hSourceTransverseOrthogonal :
  ∀ a : E3,
    CovariantDerivative.chartMetric g.inner x0
        ((GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x0) v)
        ((PsiS (CartanPullback.transversePart
          (CartanMap.sourceAnchorChartMetric g x0) v a) T).1) Vs = 0

hTargetTransverseOrthogonal :
  ∀ a : E3,
    CovariantDerivative.chartMetric roundSphereMetric3.inner p0
        ((GeodesicTransport.expAtChartOpenPartialHomeomorph
          (g := roundSphereMetric3) p0) (L v))
        ((PsiT (CartanPullback.transversePart
          (CartanMap.targetAnchorChartMetric p0) (L v) a) T).1) Vt = 0

hSourceTransverseTransverse :
  ∀ a a' : E3,
    CovariantDerivative.chartMetric g.inner x0
        ((GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x0) v)
        ((PsiS (CartanPullback.transversePart
          (CartanMap.sourceAnchorChartMetric g x0) v a) T).1)
        ((PsiS (CartanPullback.transversePart
          (CartanMap.sourceAnchorChartMetric g x0) v a') T).1) =
      JacobiNormSystem.speedPinnedScale speed T *
        CartanMap.sourceAnchorChartMetric g x0
          (T⁻¹ • CartanPullback.transversePart
            (CartanMap.sourceAnchorChartMetric g x0) v a)
          (T⁻¹ • CartanPullback.transversePart
            (CartanMap.sourceAnchorChartMetric g x0) v a')

hTargetTransverseTransverse :
  ∀ a a' : E3,
    CovariantDerivative.chartMetric roundSphereMetric3.inner p0
        ((GeodesicTransport.expAtChartOpenPartialHomeomorph
          (g := roundSphereMetric3) p0) (L v))
        ((PsiT (CartanPullback.transversePart
          (CartanMap.targetAnchorChartMetric p0) (L v) a) T).1)
        ((PsiT (CartanPullback.transversePart
          (CartanMap.targetAnchorChartMetric p0) (L v) a') T).1) =
      JacobiNormSystem.speedPinnedScale speed T *
        CartanMap.targetAnchorChartMetric p0
          (T⁻¹ • CartanPullback.transversePart
            (CartanMap.targetAnchorChartMetric p0) (L v) a)
          (T⁻¹ • CartanPullback.transversePart
            (CartanMap.targetAnchorChartMetric p0) (L v) a')
```

## Why this is blocked

- `CartanCascade.exists_common_shrunk_source_target_strictDeriv_of_hosted_linearized_pl`
  exports a common source/target radius, but the source and target times are
  separate (`Ts`, `Tt`) and each linearized family is conditional on supplied
  Picard-Lindelöf data.
- `SpeedGeneric.source_hosted_transverse_rescaled_endpoint_pairing_eq_speed_pinned_of_interval_norm_package`
  and the target analogue can prove the transverse/transverse facts, but they
  require the full interval package (`hplLinear`, `hPsiDerWithin`, membership,
  scalar norm PL, initial scalar values, endpoint identification, speed, and
  orthogonality) as inputs. I found no exported theorem that returns that whole
  package at the same `(T, PsiS, PsiT)` used by the final consumer.
- `OrthogonalityFeed.source_transverse_horth_on_Icc_of_payload` and the target
  analogue produce endpoint orthogonality only from a payload interval with
  base flow, variation flow, speed-constancy, differentiability, and cutoff
  assumptions. Those assumptions are not exported as one common hosted package
  aligned with the transverse-pairing theorem.

Adding a curvature-only theorem here would therefore require either inventing
the missing package as assumptions in different notation or hiding it inside a
vacuous wrapper. I did neither.

## Verification

Required build:

```bash
lake build Poincare.Global.CombinedFeed
```

Result: passed. The build completed successfully with pre-existing imported
module warnings.

Forbidden-token scan on the new Lean file:

```bash
rg -n "\b(sorry|admit|axiom|native_decide)\b" Poincare/Global/CombinedFeed.lean
```

Result: no matches.
