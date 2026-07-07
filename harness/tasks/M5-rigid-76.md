Read harness/worker_contract.md first and obey it strictly.

# Task M5-rigid-76: the speed² reconciliation — scalar bookkeeping, then the isometry

Context: `harness/reports/M5-rigid-75_blocked.md` (READ FIRST — the exact factor accounting). THE MISMATCH: `RayIdentification` gives the radial pairing in coefficient-product form (`ρ·ρ'·T²·speed²`-shaped); `CorrectedRadial`'s consumer wants the rescaled-anchor form whose anchor factor `G(anchor)(T⁻¹v, T⁻¹v) = speed²` (`SpeedPackage` identification) — so the two sides differ by which power of `speed` sits in the scalar. THE RECONCILIATION IS ALGEBRA: compute BOTH sides completely — LHS (ray): `ρρ'·T²·speed²`; RHS (consumer): `scalar · (ρρ'·speed²)` — so the CORRECT scalar is `T²` (plain time-square, speed-FREE). CHECK `CorrectedRadial.lean`'s `plainRadialScale` definition: if it is `T²·speed²`, the consumer double-counts — ADD (additive, NEW file + allowed additive edits to `CorrectedRadial.lean` ONLY as new variants) the `T²`-scalar consumer variant (replay the rigid-73 proof pattern with the corrected scalar — the pullback matching still works: `T²` is side-independent and the `speed²`s match through the alignment); if it is already `T²`, the mismatch is on the anchor side — reconcile by the `SpeedPackage` identification lemma. ⚠️ PIN the final scalar identity numerically on the sphere if ANY doubt. Then feed EVERYTHING → 🎯 `cartanMap_isLocalIsometry` (curvature-only). If ONE resists, isolate verbatim.

Deliverables in a NEW file `Poincare/Global/SpeedReconcile.lean`. Report `harness/reports/M5-rigid-76_{done|blocked}.md`.

No vacuous wrappers. Verify: `lake build Poincare.Global.SpeedReconcile Poincare.Global.CorrectedRadial` (BOTH must pass) and report the actual result. Commit your work.
