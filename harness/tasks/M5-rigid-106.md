Read harness/worker_contract.md first and obey it strictly.

# Task M5-rigid-106: the transverse package at the selector — the last export

Context: `harness/reports/M5-rigid-105_blocked.md` (READ FIRST — the VERBATIM missing transverse export). PROVEN: the block-diagonal upgrade + `A/B` adapter feeding `CorrectedRadial` (`BlockDiagonal.lean`). THE LAST EXPORT: the transverse block identities AT THE SELECTOR'S DATUM — the pieces: `AssemblyDone.lean`'s enriched transverse blocks (their hypotheses: the bounded norm-system data), `ScalarPin.lean`'s `hplNorm` constructors, `GronwallMembership/UniformShrink.lean`'s side conditions (`hqBound/hgronwallRadius/hpinnedRadius`, initial identities), all AT the `UniformFlowExport` selector's families (their exported ODE/initial/membership facts match — ALIGN shapes; the uniform-shrink data supplies the radii). THREAD them (the rigid-98 adapter pattern — the fields exist; export the composite). Then `BlockDiagonal`'s adapter fires → `A/B` → the consumer → 🎯 `cartanMap_isLocalIsometry` (curvature-only). If ONE resists, isolate verbatim.

Deliverables in a NEW file `Poincare/Global/TransverseExport.lean` (do NOT edit existing files, incl. `Poincare.lean`). Report `harness/reports/M5-rigid-106_{done|blocked}.md`.

No vacuous wrappers. Verify: `lake build Poincare.Global.TransverseExport` and report the actual result. Commit your work.
