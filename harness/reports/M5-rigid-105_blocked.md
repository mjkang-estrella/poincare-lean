# M5-rigid-105 blocked: block-diagonal upgrade verified, curvature-only wrapper still lacks exported transverse package

## Outcome

Added `Poincare/Global/BlockDiagonal.lean`.  No existing Lean files were
edited, including `Poincare.lean`.

The block-diagonal endpoint-equivalence upgrade requested by M5-rigid-105 is
proved and verified.  The new module does not try to force a uniform sine-square
pullback.  Instead it proves injectivity from two positive block scales on the
radial/transverse decomposition and then constructs the endpoint CLEs needed by
the corrected pairing consumer.

## Verified payload

The generic linear-algebra upgrade is:

```lean
Poincare.BlockDiagonal.injective_of_rescaled_blockDiagonal_pullback_posDef
Poincare.BlockDiagonal.exists_continuousLinearEquiv_of_rescaled_blockDiagonal_pullback_posDef
```

These use the direct decomposition from `CartanPullback`:

```lean
radialPart S v u + transversePart S v u = u
```

If `D u = 0`, the block-diagonal pullback gives

```lean
cr * S (T⁻¹ • radialPart S v u) (T⁻¹ • radialPart S v u) +
ct * S (T⁻¹ • transversePart S v u) (T⁻¹ • transversePart S v u) = 0
```

with `0 < cr`, `0 < ct`, and `T ≠ 0`.  At least one block is nonzero when
`u ≠ 0`, so positive-definiteness makes the sum strictly positive, a
contradiction.

The hosted source/target constructors are:

```lean
Poincare.BlockDiagonal.exists_continuousLinearEquiv_of_sourceAnchor_rescaled_blockDiagonal_pullback
Poincare.BlockDiagonal.exists_continuousLinearEquiv_of_targetAnchor_rescaled_blockDiagonal_pullback
Poincare.BlockDiagonal.exists_continuousLinearEquiv_of_source_linearizedEndpointCLM_rescaled_blockDiagonal_pullback
Poincare.BlockDiagonal.exists_continuousLinearEquiv_of_target_linearizedEndpointCLM_rescaled_blockDiagonal_pullback
```

The direct consumer adapter is:

```lean
Poincare.BlockDiagonal.exists_equiv_and_cartanMap_isLocalIsometry_on_normalBall_of_time_radial_block_diagonal_blocks
Poincare.BlockDiagonal.exists_equiv_and_cartanMap_isLocalIsometry_on_normalBall_of_angle_time_radial_block_diagonal_blocks
```

It constructs `A` and `B` from the two-scale source/target block identities,
then feeds:

```lean
CorrectedRadial.cartanMap_isLocalIsometry_on_normalBall_of_common_speed_time_radial_decomposed_blocks
```

The angle specialization supplies positivity from:

```lean
Poincare.BlockDiagonal.timeRadialScale_pos_of_ne_zero
Poincare.BlockDiagonal.speedPinnedScale_pos_of_mul_mem_Ioo
```

## Remaining blocker for curvature-only target

The new block-diagonal upgrade removes the single-scale obstruction from
M5-rigid-104, but it does not close the broader curvature-only
`cartanMap_isLocalIsometry` wrapper.  The remaining blocker is upstream of this
file: the public hosted selector still does not export the all-direction
transverse package needed to instantiate the block identities without assuming
them.

The existing boundary in `Poincare/Global/TheIsometry.lean` is still the
resisting interface, verbatim:

```lean
(hplLinear : forall w w' : E3,
  IsPicardLindelof ... ((0 : E3), T^-1 • (w + w')) aLin rLin LipLin KLin)
```

and its recorded explanation is:

```text
The currently exported hosted linearized-family API consumes a single
zero-centered package and exports the rescaled family, endpoint additivity, and
endpoint homogeneity. It does not export this all-direction centered package,
nor the accompanying centered closed-ball membership hypotheses required by
`BoundedPackage.source_hosted_transverse_rescaled_endpoint_pairing_eq_speed_pinned_of_plNorm_on_closedBall`
and its target analogue.
```

So the block-diagonal CLE/pairing path is now verified, but the curvature-only
wrapper would still have to assume the unfed transverse package export.

## Verification

- `rg -n '\b(sorry|admit|axiom|native_decide)\b' Poincare/Global/BlockDiagonal.lean`
  - Result: no matches.
- `git diff --check -- Poincare/Global/BlockDiagonal.lean`
  - Result: success.
- `lake build Poincare.Global.BlockDiagonal`
  - Result: success.  The build replayed pre-existing imported-module
    warnings; no failure was emitted from `Poincare/Global/BlockDiagonal.lean`.
  - Final lines:

```text
✔ [3183/3183] Built Poincare.Global.BlockDiagonal (3.9s)
Build completed successfully (3183 jobs).
```
