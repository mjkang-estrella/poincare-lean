Read harness/worker_contract.md first and obey it strictly.

# Task M5-rigid-86: the assembly, retried — the feeds are complete

Context: `harness/reports/M5-rigid-85_done.md` + `M5-rigid-84_blocked.md` (READ BOTH). rigid-84 isolated `hplLinear`; rigid-85 REMOVED it (`SolutionsFeed.source/target_transverseTransverse_of_solutions_feed` — the exact block shape `BundleDischarge` consumes, both sides, from solution additivity). THE FEED INVENTORY IS COMPLETE — rigid-84's task file lists it; substitute `SolutionsFeed` for the old bounded feed. THE ASSEMBLY: at the hosted datum, instantiate: the solutions feeds' hypotheses (the hosted zero-centered package + additivity exports — `LinearizedFamilyExport/LinearizedAdditivity/CartanCascade.lean`), the one-sided orthogonality (`OneSidedPayload/BundleDischarge.lean`), the radial facts (`RayIdentification/SpeedReconcile.lean`), speeds (`SpeedPackage/TheLocalIsometry.lean`) — and apply the consumer chain (`BundleDischarge` → `CombinedFeed` → `CorrectedRadial` T²). 🎯 `cartanMap_isLocalIsometry` — curvature-only. If ONE hypothesis genuinely cannot be fed, isolate verbatim with the exact mismatch.

Deliverables in a NEW file `Poincare/Global/IsometryAssembly.lean` (do NOT edit existing files, incl. `Poincare.lean`). Report `harness/reports/M5-rigid-86_{done|blocked}.md`.

No vacuous wrappers. Verify: `lake build Poincare.Global.IsometryAssembly` and report the actual result. Commit your work.
