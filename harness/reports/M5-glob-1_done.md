# M5-glob-1 done report

## Delivered files

- `harness/reports/M5-glob-1_assets.md`
- `Poincare/Global/CoveringSkeleton.lean`

No existing Lean files or `Poincare.lean` were edited.

## Proven Lean payload

`Poincare/Global/CoveringSkeleton.lean` proves:

- `surjective_of_isOpen_isClosed_range`: elementary clopen-image surjectivity.
- `IsLocalHomeomorph.surjective_of_isClosed_range`: local homeomorphism plus closed image into a
  preconnected target is surjective.
- `isCoveringMap_of_compact_isLocalHomeomorph`: compact Hausdorff source plus local homeomorphism
  gives `IsCoveringMap`.
- `bijective_of_isCoveringMap_simplyConnected`: a covering map with connected total space over a
  simply connected locally path connected base is bijective.
- `isHomeomorph_of_isCoveringMap_simplyConnected`: the corresponding `IsHomeomorph` statement.
- `homeomorphOfIsCoveringMapSimplyConnected`: bundled `E ≃ₜ X` version.

## Verification

Command run:

```bash
lake build Poincare.Global.CoveringSkeleton
```

Actual result:

```text
✔ [1666/1666] Built Poincare.Global.CoveringSkeleton (1.4s)
Build completed successfully (1666 jobs).
```

## Remaining glue for the rigidity endgame

The future local-isometry statement should provide `IsLocalHomeomorph Phi` for
`Phi : M -> RoundSphere3`, or equivalent `OpenPartialHomeomorph` witnesses. Then the remaining
inputs are the standard topological instances: compact Hausdorff total space, Hausdorff target,
connected total space, and `SimplyConnectedSpace` plus `LocPathConnectedSpace` for the round sphere.
