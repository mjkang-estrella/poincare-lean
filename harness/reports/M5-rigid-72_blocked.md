# M5-rigid-72 blocked

## Status

Blocked on the radial/radial scalar required by the decomposed consumer.

Added `Poincare/Global/RadialBlock.lean` with non-vacuous algebraic facts:

- `RadialBlock.speedPinnedScale_unfold`
- `RadialBlock.speedPinnedScale_one_pi`
- `RadialBlock.ray_pairing_time_smul`
- `RadialBlock.ray_pairing_rescaled_initial`
- `RadialBlock.consumer_speedPinned_rescaled_pairing`

No existing Lean files were edited, including `Poincare.lean`.

## Verification

Command:

```bash
lake build Poincare.Global.RadialBlock
```

Result:

```text
Build completed successfully (3181 jobs).
```

The build emitted pre-existing warnings in imported modules.  The final
`Poincare.Global.RadialBlock` target built successfully.

## Blocking scalar

The requested decomposed radial/radial field uses:

```lean
JacobiNormSystem.speedPinnedScale speed T
```

but the definition unfolds to the transverse sine scale:

```lean
theorem speedPinnedScale_unfold (speed T : ℝ) :
    JacobiNormSystem.speedPinnedScale speed T =
      Real.sin (speed * T) ^ 2 * (speed ^ 2)⁻¹ := by
  rfl
```

The new file also proves the half-period pin:

```lean
@[simp]
theorem speedPinnedScale_one_pi :
    JacobiNormSystem.speedPinnedScale 1 Real.pi = 0 := by
  simp [JacobiNormSystem.speedPinnedScale]
```

For a ray-shaped radial variation, the endpoint algebra is ordinary time
scaling:

```lean
theorem ray_pairing_time_smul
    (B : E →L[ℝ] E →L[ℝ] ℝ) (T : ℝ) (w w' : E) :
    B (T • w) (T • w') = T ^ 2 * B w w' := by
  simp [pow_two, mul_assoc]
```

and with the rescaled initial data used by the decomposed consumer:

```lean
theorem ray_pairing_rescaled_initial
    (B : E →L[ℝ] E →L[ℝ] ℝ) {T : ℝ} (hT : T ≠ 0) (w w' : E) :
    B (T • (T⁻¹ • w)) (T • (T⁻¹ • w')) = B w w' := by
  simp [hT]
```

So the ray variation does not supply the consumer's
`speedPinnedScale speed T` sine factor on the radial/radial block.

## Verbatim hypotheses still not instantiable

Source:

```lean
(hSourceRadialRadial :
  ∀ a a' : E3,
    CovariantDerivative.chartMetric g.inner x₀
        ((GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀) v)
        ((Ψs (CartanPullback.radialPart
          (CartanMap.sourceAnchorChartMetric g x₀) v a) T).1)
        ((Ψs (CartanPullback.radialPart
          (CartanMap.sourceAnchorChartMetric g x₀) v a') T).1) =
      JacobiNormSystem.speedPinnedScale speed T *
        CartanMap.sourceAnchorChartMetric g x₀
          (T⁻¹ • CartanPullback.radialPart
            (CartanMap.sourceAnchorChartMetric g x₀) v a)
          (T⁻¹ • CartanPullback.radialPart
            (CartanMap.sourceAnchorChartMetric g x₀) v a'))
```

Target:

```lean
(hTargetRadialRadial :
  ∀ a a' : E3,
    CovariantDerivative.chartMetric roundSphereMetric3.inner p₀
        ((GeodesicTransport.expAtChartOpenPartialHomeomorph
          (g := roundSphereMetric3) p₀) (L v))
        ((Ψt (CartanPullback.radialPart
          (CartanMap.targetAnchorChartMetric p₀) (L v) a) T).1)
        ((Ψt (CartanPullback.radialPart
          (CartanMap.targetAnchorChartMetric p₀) (L v) a') T).1) =
      JacobiNormSystem.speedPinnedScale speed T *
        CartanMap.targetAnchorChartMetric p₀
          (T⁻¹ • CartanPullback.radialPart
            (CartanMap.targetAnchorChartMetric p₀) (L v) a)
          (T⁻¹ • CartanPullback.radialPart
            (CartanMap.targetAnchorChartMetric p₀) (L v) a'))
```

## Why the wrapper was not added

`BlocksDischarge.lean` supplies the mixed blocks, and `SpeedGeneric.lean`
supplies the sine-scaled endpoint package under the transverse orthogonality
hypotheses.  `OrthogonalityFeed.lean` already records the radial pin as
`t * speed²`, not zero, so that transverse route does not apply to the radial
input.

Instantiating the two radial/radial hypotheses above with the current
`speedPinnedScale` scalar would therefore restate the missing block or force a
transverse sine scale onto the ray variation.  Under the worker contract, that
would be a vacuous wrapper rather than proof progress.
