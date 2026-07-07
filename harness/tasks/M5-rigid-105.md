Read harness/worker_contract.md first and obey it strictly.

# Task M5-rigid-105: the block-diagonal upgrade — per-block positive scales

Context: `harness/reports/M5-rigid-104_blocked.md` (READ FIRST — refutation #9: one uniform sin² scalar forces sin²=1; the radial block carries the PLAIN scale, transverse carries sin²). THE CORRECT STRUCTURE: the pullback is BLOCK-DIAGONAL in the radial/transverse decomposition — `G_target(Φu, Φu') = c_r·(radial part pairing) + c_t·(transverse part pairing)` with TWO positive scales (`c_r = plain time-radial`, `c_t = sin²` — both positive on the shrunk ball). THE UPGRADE VARIANT (additive): injectivity from block-diagonal positive scales — `Φu = 0 ⟹ c_r·|radial(u)|² + c_t·|transverse(u)|² = 0 ⟹ both parts 0 ⟹ u = 0` (the Gram decomposition is direct — `CartanPullback.lean`); replay `ScaledUpgrade.lean`'s CLE construction with the two-scale hypothesis. THE CONSUMER SIDE: check what the final pairing consumer actually needs — the PULLBACK IDENTITY it concludes is itself the block formula (both sides share BOTH scales through the alignment — the sT-invariance) — the consumer chain (`CorrectedRadial/PairingFeed`) was built for exactly the two-scale form (T² radial + sin² transverse): FEED IT DIRECTLY with the block identities (the corrected adapters + blocks, per rigid-104's inventory). 🎯 `cartanMap_isLocalIsometry` (curvature-only). If ONE resists, isolate verbatim.

Deliverables in a NEW file `Poincare/Global/BlockDiagonal.lean` (do NOT edit existing files, incl. `Poincare.lean`). Report `harness/reports/M5-rigid-105_{done|blocked}.md`.

No vacuous wrappers. Verify: `lake build Poincare.Global.BlockDiagonal` and report the actual result. Commit your work.
