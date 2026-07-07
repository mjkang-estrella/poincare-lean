# M5-rigid-75 blocked

## Status

Added `Poincare/Global/IsometryFinal.lean` as the required new module.

No existing Lean files were edited, including `Poincare.lean`.

The final theorem `cartanMap_isLocalIsometry` was not stated, because one
required radial hypothesis of
`CorrectedRadial.cartanMap_isLocalIsometry_on_normalBall_of_common_speed_corrected_radial_decomposed_blocks`
cannot be instantiated from the exported facts without an additional bridge.

## Isolated unfed hypothesis

Source radial/radial block required by the final consumer:

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

Target radial/radial block is the analogous unfed hypothesis.

## Why the exported radial theorem does not feed it

`RayIdentification.radialPart_endpoint_pairing_eq_radialCoeff_mul_plainRadialScale`
exports:

```lean
G ((Ψ (CartanPullback.radialPart B v u) T).1)
  ((Ψ (CartanPullback.radialPart B v u') T).1) =
    (CartanPullback.radialCoeff B v u *
        CartanPullback.radialCoeff B v u') *
      CorrectedRadial.plainRadialScale speed T
```

The consumer requires the right-hand side to be:

```lean
CorrectedRadial.plainRadialScale speed T *
  B (T⁻¹ • CartanPullback.radialPart B v u)
    (T⁻¹ • CartanPullback.radialPart B v u')
```

For hosted data, `SpeedPackage` identifies:

```lean
CartanMap.sourceAnchorChartMetric g x0 (T⁻¹ • v) (T⁻¹ • v) = speed ^ 2
```

and similarly on the target side after alignment. Thus the rescaled-anchor
pairing of radial parts expands to the coefficient product times `speed ^ 2`.
The consumer right-hand side therefore has an extra factor of `speed ^ 2`
relative to the theorem exported by `RayIdentification`, unless a unit-speed
normalization or a corrected radial scalar is supplied.

Under the worker contract, adding a wrapper that assumes this bridge would be
a vacuous restatement of the missing radial block rather than a discharge.

## Verification

Command:

```bash
lake build Poincare.Global.IsometryFinal
```

Result:

```text
Build completed successfully (3187 jobs).
```

The build emitted pre-existing warnings in imported modules. The final
`Poincare.Global.IsometryFinal` target built successfully.
