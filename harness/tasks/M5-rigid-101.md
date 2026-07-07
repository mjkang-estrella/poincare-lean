Read harness/worker_contract.md first and obey it strictly.

# Task M5-rigid-101: the pullback feed at the selector — the blocks meet the families

Context: `harness/reports/M5-rigid-100_blocked.md` (READ FIRST — the VERBATIM `hSourcePullback/hTargetPullback` shapes: `G(endpoint)(Ψ_b(T).1, Ψ_{b'}(T).1) = anchorMetric(b, b')`-shaped). PROVEN: the pairing-based upgrade + hosted adapters (`PairingUpgrade.lean`). THE IDENTITIES ARE THE CAMPAIGN'S BLOCK FORMULAS: the decomposed bilinear expansion — radial (`RayIdentification/SpeedReconcile.lean`: fed by the SELECTOR'S RAY IDENTITIES, exported!), mixed (zero — `OneSidedPayload/BundleDischarge.lean`), transverse (`AssemblyDone.lean`'s enriched blocks with membership `GronwallMembership.lean`), combined by the Gram decomposition + family additivity (`CartanPullback/LinearizedAdditivity.lean` — the `CombinedFeed/DecomposedAssembly.lean` assembly theorems). THE TASK: instantiate the block theorems AT THE SELECTOR'S FAMILIES (`UniformFlowExport.lean`'s selected `Ψs/Ψt` — their exported properties ARE the blocks' hypotheses: ray identities, ODE facts, membership; MATCH shapes), assemble the full pullback identities via the decomposition, feed `PairingUpgrade`'s theorem → `A/B` + coercions → the consumer → 🎯 `cartanMap_isLocalIsometry` (curvature-only). If ONE resists, isolate verbatim.

Deliverables in a NEW file `Poincare/Global/PullbackFeed.lean` (do NOT edit existing files, incl. `Poincare.lean`). Report `harness/reports/M5-rigid-101_{done|blocked}.md`.

No vacuous wrappers. Verify: `lake build Poincare.Global.PullbackFeed` and report the actual result. Commit your work.
