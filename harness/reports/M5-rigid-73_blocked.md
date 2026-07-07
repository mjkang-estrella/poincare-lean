# M5-rigid-73 blocked

## Status

Added `Poincare/Global/CorrectedRadial.lean` as a new additive module.

The file proves the corrected-radial consumer layer:

- `CorrectedRadial.plainRadialScale`
- `CorrectedRadial.plainRadialScale_unfold`
- `CorrectedRadial.plainRadialScale_rescaled_pairing`
- `CorrectedRadial.hosted_rescaled_endpoint_pairing_eq_of_corrected_radial_transverse_blocks`
- `CorrectedRadial.source_hosted_rescaled_endpoint_pairing_eq_of_corrected_radial_transverse_blocks`
- `CorrectedRadial.target_hosted_rescaled_endpoint_pairing_eq_of_corrected_radial_transverse_blocks`
- `CorrectedRadial.hosted_endpoint_pairing_feed_of_common_speed_corrected_radial_decomposed_blocks`
- `CorrectedRadial.cartanMap_isLocalIsometry_on_normalBall_of_common_speed_corrected_radial_decomposed_blocks`

No existing Lean files were edited, including `Poincare.lean`.

## Verification

Command:

```bash
lake build Poincare.Global.CorrectedRadial
```

Result:

```text
Build completed successfully (3182 jobs).
```

The build emitted pre-existing warnings in imported modules. The final
`Poincare.Global.CorrectedRadial` target built successfully.

## What was fixed

The new consumer separates the radial and transverse scalars instead of
forcing both through `JacobiNormSystem.speedPinnedScale`.

The corrected radial scalar is:

```lean
def plainRadialScale (speed T : ℝ) : ℝ :=
  T ^ 2 * speed ^ 2
```

The endpoint feed compares the source and target decomposed sums term-by-term.
The radial summands match through
`CartanPullback.tangentAlignment_radialPart_map` and
`CartanMap.TangentAlignment.map_app`; the transverse summands match through
`CartanPullback.tangentAlignment_transversePart_map` and the same alignment
pairing identity.

The final local-isometry consumer then feeds this corrected endpoint pairing
equality into `PairingFeed.cartanMap_isLocalIsometry_on_normalBall_of_hosted_endpoint_pairing_feed`.

## Remaining block

The corrected consumer is proved, but the task is not fully discharged from
the currently exported geometric facts. The remaining obstacle is the actual
radial/radial endpoint block for the hosted linearized family. The new
consumer deliberately asks for the corrected plain radial scale:

```lean
(hSourceRadialRadial :
  ∀ a a' : E3,
    CovariantDerivative.chartMetric g.inner x0
        ((GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x0) v)
        ((PsiS (CartanPullback.radialPart
          (CartanMap.sourceAnchorChartMetric g x0) v a) T).1)
        ((PsiS (CartanPullback.radialPart
          (CartanMap.sourceAnchorChartMetric g x0) v a') T).1) =
      plainRadialScale speed T *
        CartanMap.sourceAnchorChartMetric g x0
          (T⁻¹ • CartanPullback.radialPart
            (CartanMap.sourceAnchorChartMetric g x0) v a)
          (T⁻¹ • CartanPullback.radialPart
            (CartanMap.sourceAnchorChartMetric g x0) v a'))
```

and the target analogue:

```lean
(hTargetRadialRadial :
  ∀ a a' : E3,
    CovariantDerivative.chartMetric roundSphereMetric3.inner p0
        ((GeodesicTransport.expAtChartOpenPartialHomeomorph
          (g := roundSphereMetric3) p0) (L v))
        ((PsiT (CartanPullback.radialPart
          (CartanMap.targetAnchorChartMetric p0) (L v) a) T).1)
        ((PsiT (CartanPullback.radialPart
          (CartanMap.targetAnchorChartMetric p0) (L v) a') T).1) =
      plainRadialScale speed T *
        CartanMap.targetAnchorChartMetric p0
          (T⁻¹ • CartanPullback.radialPart
            (CartanMap.targetAnchorChartMetric p0) (L v) a)
          (T⁻¹ • CartanPullback.radialPart
            (CartanMap.targetAnchorChartMetric p0) (L v) a'))
```

`ExponentialRayLawFull.lean` exports the closed-interval base ray law for
`expAt`, but it does not currently export the needed differentiated
homogeneity / linearized uniqueness theorem identifying the radial `Psi`
endpoint with the ray derivative. Without that theorem, instantiating the two
radial hypotheses above would restate the missing geometric block.

`BlocksDischarge.lean` also only exports anchor Gram facts for mixed
radial/transverse pairings; it does not by itself prove the endpoint mixed
block hypotheses for arbitrary hosted `Psi`.

Under the worker contract, stopping here is preferable to adding a wrapper
that assumes the geometric radial block has already been discharged.
