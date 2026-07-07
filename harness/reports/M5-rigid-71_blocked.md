# M5-rigid-71 blocked

## Status

Blocked before the final wrapper.

Added `Poincare/Global/BlocksDischarge.lean` with the block-side facts that do
discharge from the current exported inventory:

- `BlocksDischarge.tangentAlignment_apply_ne_zero`
- `BlocksDischarge.source_radialPart_transversePart_pair`
- `BlocksDischarge.source_transversePart_radialPart_pair`
- `BlocksDischarge.target_radialPart_transversePart_pair`
- `BlocksDischarge.target_transversePart_radialPart_pair`

No existing Lean files were edited, including `Poincare.lean`.

## Verification

Command:

```bash
lake build Poincare.Global.BlocksDischarge
```

Result:

```text
Build completed successfully (3181 jobs).
```

The build emitted pre-existing warnings in imported modules; the new target
built successfully.

## Blocking field

The first decomposed consumer field that I could not instantiate from exported
hosted data is exactly this hypothesis from
`Poincare/Global/DecomposedAssembly.lean`:

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

The target-side radial/radial field has the same shape with
`roundSphereMetric3`, `p₀`, `L v`, and `Ψt`.

## Why this blocks the wrapper

`cartanMap_isLocalIsometry_on_normalBall_of_common_speed_decomposed_blocks`
needs all six endpoint block fields at the actual hosted source and target
data.  The current exports cover:

- the decomposed consumer itself in `DecomposedAssembly.lean`;
- speed nonzero/value facts in `TheLocalIsometry.lean` and
  `SpeedPackage.lean`;
- transverse orthogonality feeds in `OrthogonalityFeed.lean`;
- speed-generic endpoint formulas in `SpeedGeneric.lean`, conditional on the
  interval/norm package fields;
- Gram decomposition and mixed anchor orthogonality in `CartanPullback.lean`.

I did not find an exported theorem proving the radial/radial endpoint pairing
above for `Ψs` with the `speedPinnedScale speed T` scalar.  The older
scale-generic route in `CartanScaleGeneric.lean` keeps
`hostedRadialScale` equal to `1`, which does not directly supply the
`speedPinnedScale speed T` radial block required by the M5-rigid-70 decomposed
consumer.

Therefore adding a theorem named `cartanMap_isLocalIsometry` here would either
leave the radial block as an assumption or restate the consumer, which would be
a vacuous wrapper under the worker contract.
