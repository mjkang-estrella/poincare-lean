Read harness/worker_contract.md first and obey it strictly.

# Task M5-rigid-109: the three bounds — coefficient, center, shrink at the selector

Context: `harness/reports/M5-rigid-108_blocked.md` (READ FIRST — the VERBATIM three hypotheses: ball-uniform coefficient bound `‖Aop‖ ≤ C`, uniform center bound `Q`, shrink `C·T ≤ 1/2`). PROVEN: the tuple constructor from exactly these (`CoefficientShrink.lean`, with source/target specializations + continuation lemmas). THE EXPORTS: (1) `C` — the coefficient operator norm along the selector's base curve, bounded ball-uniformly: `UniformShrink.lean`'s ball-uniform machinery PROVED this shape for the εlin bound (its proof extracts a coefficient bound — RE-EXPORT the bound itself); (2) `Q` — the uniform center bound over the bounded `w`-ball: `BoundedPackage/GronwallMembership.lean`'s bounded-`q` handoff (the anchor-metric sup on the compact ball); (3) the shrink `C·T ≤ 1/2` — one more term in the ball-radius min (the rigid-97/108 arithmetic: `T(v) ∝ ‖v‖`; shrink the `v`-ball radius below `(δ/2)/(2C)`). EXPORT the three at the selector's datum (source + target), feed the constructor → the tuple → `TransverseExport`'s composite → `BlockDiagonal` → `A/B` → 🎯 `cartanMap_isLocalIsometry` (curvature-only). If ONE resists, isolate verbatim.

Deliverables in a NEW file `Poincare/Global/ThreeBounds.lean` (do NOT edit existing files, incl. `Poincare.lean`). Report `harness/reports/M5-rigid-109_{done|blocked}.md`.

No vacuous wrappers. Verify: `lake build Poincare.Global.ThreeBounds` and report the actual result. Commit your work.
