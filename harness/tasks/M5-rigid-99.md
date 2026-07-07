Read harness/worker_contract.md first and obey it strictly.

# Task M5-rigid-99: THE FINAL ASSEMBLY — all witnesses public

Context: `harness/reports/M5-rigid-98_done.md` (READ FIRST) + `M5-rigid-91_blocked.md` + `M5-rigid-88_blocked.md`. EVERY WITNESS IS NOW PUBLIC: the selector outputs with strict derivatives + RAY IDENTITIES both sides at the common `T < εlin` (`UniformFlowExport.lean`); the transverse blocks with membership (`AssemblyDone.lean` + `GronwallMembership/SolutionsFeed.lean`); the orthogonality (`OneSidedPayload/BundleDischarge.lean`); the radial pairing consequences (`RayIdentification/SpeedReconcile.lean` — fed by the ray identities); speeds (`SpeedPackage.lean`); the consumer chain (`BundleDischarge → CombinedFeed → CorrectedRadial T² → PairingFeed/EqualityChain`). ASSEMBLE at the selector's datum. 🎯 `cartanMap_isLocalIsometry` — for every closed simply-connected `g` with `HasConstantSectionalCurvature3 g 1`, anchors `x₀ p₀`, some alignment `L`: the chart-metric pullback equality on a punctured shrunk normal ball — CURVATURE-ONLY hypotheses. If ONE hypothesis genuinely cannot be fed, isolate verbatim.

Deliverables in a NEW file `Poincare/Global/LocalIsometryTheorem.lean` (do NOT edit existing files, incl. `Poincare.lean`). Report `harness/reports/M5-rigid-99_{done|blocked}.md`.

No vacuous wrappers. Verify: `lake build Poincare.Global.LocalIsometryTheorem` and report the actual result. Commit your work.
