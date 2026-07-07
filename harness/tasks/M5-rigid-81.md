Read harness/worker_contract.md first and obey it strictly.

# Task M5-rigid-81: hplNorm — the PL norm package at the hosted datum

Context: `harness/reports/M5-rigid-80_blocked.md` (READ FIRST — the VERBATIM `hplNorm` field). PROVEN: the one-sided orthogonality feed routed through `CombinedFeed` → `SpeedReconcile` → the T² consumer (`BundleDischarge.lean`, 585 lines). THE ONE FIELD: the source (and target) `SpeedGeneric` Picard–Lindelöf norm package for the transverse-transverse blocks — the PL constants `(radius, rNorm, LNorm, KNorm)` at the hosted anchor data. WHERE PL DATA LIVES: the hosted flow construction carries its PL package (`GeodesicLengthFinal.lean`'s shrunk cutoff-one flow — its existence statement HAS the PL bounds; `CartanHomogeneity.lean` hosts inside it; the `ChartChristoffelPicardLindelof`-shaped structures in `GeodesicChart/GeodesicTransport.lean`) — and `TargetPackage/CartanIsometryTheorem.lean`'s interval discharges consumed the SAME kind of package: FIND how they obtained theirs and replay at the common hosted datum (likely: the existence theorem yields the package; thread it through the bundle instead of re-deriving). Feed `hplNorm` (+ its target analogue) → the transverse blocks land → the bundle completes → 🎯 `cartanMap_isLocalIsometry` (curvature-only). If ONE resists, isolate verbatim.

Deliverables in a NEW file `Poincare/Global/PLNormFeed.lean` (do NOT edit existing files, incl. `Poincare.lean`). Report `harness/reports/M5-rigid-81_{done|blocked}.md`.

No vacuous wrappers. Verify: `lake build Poincare.Global.PLNormFeed` and report the actual result. Commit your work.
