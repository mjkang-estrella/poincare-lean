Read harness/worker_contract.md first and obey it strictly.

# Task M5-rigid-78: the hosted payload package — bundle the interval assumptions

Context: `harness/reports/M5-rigid-77_blocked.md` (READ FIRST — the exact payload fields). PROVEN: mixed blocks from ray + orthogonality, fed into the T² consumer (`CombinedFeed.lean`). REMAINING: ONE COMMON-TIME HOSTED PACKAGE exporting the payload interval assumptions — base flow, variation flow, speed constancy, differentiability, cutoff — aligned with BOTH the transverse orthogonality theorem (`OrthogonalityFeed/SmoothDependenceDischarge.lean` payload forms) and the transverse-transverse endpoint facts (`SpeedGeneric.lean`'s interval hypotheses). EACH FIELD IS DISCHARGED SOMEWHERE: the hosted flow + cutoff facts (`CartanHomogeneity.lean`, `GeodesicLengthFinal.lean`'s shrunk package), speed constancy (`SpeedPackage.lean`), variation flow + differentiability (`GeodesicFlowDerivative/LinearizedFamilyExport/CartanCascade.lean`), the interval discharges (`CartanIsometryTheorem.lean` source / `TargetPackage.lean` sphere). THE TASK: define/prove the BUNDLE — one structure or one existence theorem quantifying a hosted datum satisfying every field simultaneously (radius intersection), source AND target; then INSTANTIATE the transverse facts from it and complete the combined feed → 🎯 `cartanMap_isLocalIsometry` (curvature-only). If ONE field cannot be co-discharged, isolate verbatim.

Deliverables in a NEW file `Poincare/Global/HostedPayload.lean` (do NOT edit existing files, incl. `Poincare.lean`). Report `harness/reports/M5-rigid-78_{done|blocked}.md`.

No vacuous wrappers. Verify: `lake build Poincare.Global.HostedPayload` and report the actual result. Commit your work.
