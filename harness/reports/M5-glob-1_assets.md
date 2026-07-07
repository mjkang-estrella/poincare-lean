# M5-glob-1 assets report

## Mathlib covering-space inventory

Pinned Mathlib has `Mathlib/Topology/Covering.lean` as a deprecated shim importing
`Mathlib.Topology.Covering.Basic`. The real covering files present in this worktree are:

- `Mathlib/Topology/Covering/Basic.lean`
- `Mathlib/Topology/Covering/Quotient.lean`
- `Mathlib/Topology/Covering/AddCircle.lean`
- `Mathlib/Topology/Homotopy/Lifting.lean` for path, homotopy, monodromy, and lifting criteria.
- `Mathlib/AlgebraicTopology/FundamentalGroupoid/SimplyConnected.lean` for `SimplyConnectedSpace`.

### (a) Local homeomorphism plus compactness/uniformity implies covering

What exists:

- `IsCoveringMap` and `IsCoveringMapOn` are defined in `Topology/Covering/Basic.lean`.
  A covering map is not required to be surjective; fibers may be empty.
- `IsCoveringMap.isLocalHomeomorph`, `IsCoveringMap.continuous`, `IsCoveringMap.isOpenMap`,
  and `IsCoveringMap.isSeparatedMap` are available.
- `IsCoveringMapOn.of_openPartialHomeomorph` proves that if `E` and `X` are Hausdorff,
  `E` is compact, `f` is continuous, and every point over a chosen subset has an
  `OpenPartialHomeomorph` witness agreeing with `f`, then `f` is a covering map on that subset.
- The pointwise version `IsEvenlyCovered.of_openPartialHomeomorph` is also available.
- `IsClosedMap.isCoveringMapOn_of_openPartialHomeomorph` is the noncompact closed-map + finite-fiber
  version.
- `IsLocalHomeomorph` already provides global `OpenPartialHomeomorph` witnesses for each point, so
  the compact Hausdorff API can be wrapped into a clean theorem:
  compact Hausdorff source + Hausdorff target + `IsLocalHomeomorph f` implies `IsCoveringMap f`.

What does not appear to exist:

- I found no direct theorem named like "uniform local homeomorphism implies covering".
- I found no direct theorem that consumes a positive Lebesgue/uniform normal radius condition.
- The future local-isometry statement should therefore feed either `IsLocalHomeomorph f` plus compactness,
  or the stronger per-point `OpenPartialHomeomorph` witnesses expected by Mathlib.

Verdict: compact + local homeomorphism closes now through `IsCoveringMapOn.of_openPartialHomeomorph`.
The "uniform radius" route is not a named Mathlib theorem in the pinned API; it should be treated as
project glue unless the future rigidity statement already gives `IsLocalHomeomorph`.

### (b) Covering of simply connected base by connected total space is a homeomorphism

What exists:

- `SimplyConnectedSpace` is defined via the fundamental groupoid, and provides
  `PathConnectedSpace` plus `SimplyConnectedSpace.paths_homotopic`.
- `IsCoveringMap.exists_path_lifts`, `liftPath`, `liftHomotopy`, monodromy, and
  `IsCoveringMap.existsUnique_continuousMap_lifts` exist in `Topology/Homotopy/Lifting.lean`.
- The lifting theorem says a map from a simply connected, locally path connected space lifts
  uniquely through a covering map after specifying one lifted basepoint.
- `IsCoveringMap.eq_of_comp_eq` gives uniqueness of two lifts from a preconnected space when they
  agree at one point.
- `IsLocalHomeomorph.toHomeomorphOfBijective` converts a bijective local homeomorphism into a
  bundled homeomorphism.

What does not appear to exist:

- I found no prepackaged theorem with the exact classical statement
  "covering over simply connected, locally path connected base with connected total space is a
  homeomorphism".

Verdict: the classical statement closes now as a short proof: lift `id : X -> X` to a section
`F : X -> E`, use connectedness of `E` and covering-map uniqueness to prove `F (p e) = e`, then
turn the resulting bijective local homeomorphism into a homeomorphism.

## Remaining project glue

To consume the future rigidity output for `Phi : M -> RoundSphere3`, the endgame needs:

1. A theorem or construction exporting the local isometry as `IsLocalHomeomorph Phi` (or per-point
   `OpenPartialHomeomorph` witnesses).
2. Topological instances for the total and base spaces:
   `T2Space`, `CompactSpace` for the total space, and `T2Space` for the target.
3. `ConnectedSpace M`.
4. `SimplyConnectedSpace RoundSphere3` and `LocPathConnectedSpace RoundSphere3`.
5. A small bridge from the resulting `M ≃ₜ RoundSphere3` to the specific recognition statement
   expected by `SphereTheorem.lean`.
