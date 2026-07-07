# M5-rigid-101 blocked: block adapter proved, exact pullback needs a unit transverse scalar

## Status

Added `Poincare/Global/PullbackFeed.lean`.  No existing Lean files were edited,
including `Poincare.lean`.

The new module proves the non-vacuous feed from the verified decomposed block
shape to `PairingUpgrade`, but only after isolating the remaining scalar needed
to turn the block expansion into the stronger exact anchor pullback:

```lean
JacobiNormSystem.speedPinnedScale speed T * (T⁻¹ * T⁻¹) = 1
```

## Verified payload

The new module exports:

```lean
Poincare.PullbackFeed.source_anchor_pullback_of_time_radial_blocks_and_unit_transverse
Poincare.PullbackFeed.target_anchor_pullback_of_time_radial_blocks_and_unit_transverse
Poincare.PullbackFeed.exists_equiv_and_cartanMap_isLocalIsometry_on_normalBall_of_time_radial_blocks
```

These theorems use the current campaign block formulas:

- radial/radial with `CorrectedRadial.timeRadialScale T`;
- radial/transverse equal to `0`;
- transverse/transverse with `JacobiNormSystem.speedPinnedScale speed T`;
- endpoint additivity;
- Gram radial/transverse recomposition.

They then build the exact source and target pullbacks required by
`PairingUpgrade.exists_equiv_and_cartanMap_isLocalIsometry_on_normalBall_of_hosted_anchor_pullbacks`
and feed that theorem, preserving the `A/B` coercion equalities to the selected
`linearizedEndpointCLM`s.

## Remaining blocker

The exact `hSourcePullback` / `hTargetPullback` shape from M5-rigid-100 is:

```lean
∀ a a' : E3,
  Gs (Ψs a T).1 (Ψs a' T).1 =
    CartanMap.sourceAnchorChartMetric g x₀ a a'

∀ b b' : E3,
  Gt (Ψt b T).1 (Ψt b' T).1 =
    CartanMap.targetAnchorChartMetric p₀ b b'
```

After the verified decomposed block assembly, the radial term unscales to the
anchor radial block from `T ≠ 0`, but the transverse term unscales only if:

```lean
JacobiNormSystem.speedPinnedScale speed T * (T⁻¹ * T⁻¹) = 1
```

That scalar is not exported by
`UniformFlowExport.exists_common_time_with_uniform_flow_exports_and_enriched_selectors`.
The selector exports `Ψs/Ψt`, endpoint additivity and homogeneity, strict
derivatives, linearized packages, and ray identities; it does not export this
unit transverse normalization.  Assuming the whole exact pullback would rename
the missing feed.  Assuming only the scalar above is the narrow isolated
blocker proved by `PullbackFeed`.

There is a second upstream packaging gap if trying to instantiate the transverse
blocks directly from the selector: `AssemblyDone.source_transverseTransverse_of_enriched_gronwall_feed`
and its target analogue still need the bounded norm-system PL/radius side
conditions (`hplNorm`, `hqBound`, `hgronwallRadius`, `hpinnedRadius`, and the
initial norm-state identities).  Those are not part of the `UniformFlowExport`
selector output either.

## Verification

- Forbidden-token scan on `Poincare/Global/PullbackFeed.lean`
  - Result: no matches.
- `lake build Poincare.Global.PullbackFeed`
  - Result: success.  The build replayed pre-existing upstream warnings; no
    warning was emitted from `Poincare/Global/PullbackFeed.lean` on the final
    run.
  - Final lines:

```text
✔ [3184/3184] Built Poincare.Global.PullbackFeed (3.4s)
Build completed successfully (3184 jobs).
```
