Read harness/worker_contract.md first and obey it strictly.

# Task M5-rigid-71: discharge the decomposed blocks — the wrapper falls

Context: `harness/reports/M5-rigid-70_done.md` (READ FIRST). PROVEN: `cartanMap_isLocalIsometry_on_normalBall_of_common_speed_decomposed_blocks` (`DecomposedAssembly.lean` — READ its full hypothesis list: the decomposed block hypotheses, source and target). EVERY BLOCK'S CONTENT IS PROVEN — the campaign's whole inventory: radial (speed instantiations, `TheLocalIsometry.lean`/`SpeedPackage.lean`), cross (the transverse orthogonality feed, `OrthogonalityFeed.lean`), transverse (the restricted variants + speed-generic pinned formulas, `SpeedGeneric.lean` + interval discharges `CartanIsometryTheorem/TargetPackage.lean`), the Gram decomposition (`CartanPullback.lean`), family additivity (`LinearizedAdditivity.lean`), hosting (`CartanHomogeneity.lean`), alignment preservation (`CartanPullback/CartanMap.lean`). THE TASK: instantiate each block hypothesis at the actual hosted data and apply the consumer. 🎯 `cartanMap_isLocalIsometry` — hypotheses ONLY: curvature + instances + anchors + alignment. If ONE block field resists, isolate verbatim.

Deliverables in a NEW file `Poincare/Global/BlocksDischarge.lean` (do NOT edit existing files, incl. `Poincare.lean`). Report `harness/reports/M5-rigid-71_{done|blocked}.md`.

No vacuous wrappers. Verify: `lake build Poincare.Global.BlocksDischarge` and report the actual result. Commit your work.
