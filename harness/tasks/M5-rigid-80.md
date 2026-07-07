Read harness/worker_contract.md first and obey it strictly.

# Task M5-rigid-80: the bundle discharge — one-sided exports feed everything

Context: `harness/reports/M5-rigid-79_done.md` + `M5-rigid-78_blocked.md` + `M5-rigid-77_blocked.md` (READ ALL). NOW AVAILABLE: the one-sided `Icc 0 T` transverse Gauss payload + source/target orthogonality feeds (`OneSidedPayload.lean`, 571 lines) — the `hflow` interval mismatch is RESOLVED (the `Icc 0 ε` exports feed directly). THE TASK: complete rigid-78's bundle — one common hosted datum (radius intersection) satisfying: the one-sided payload fields (base/variation flows, speed constancy, differentiability, cutoff — from `CartanHomogeneity/GeodesicLengthFinal/SpeedPackage/GeodesicFlowDerivative/CartanCascade.lean`), the transverse-transverse interval facts (`SpeedGeneric.lean` + `CartanIsometryTheorem/TargetPackage.lean` discharges), the radial facts (`RayIdentification/SpeedReconcile.lean`), the mixed derivation (`CombinedFeed.lean`) — and FEED the T² consumer (`CorrectedRadial.lean`). 🎯 `cartanMap_isLocalIsometry` — curvature-only. If ONE field cannot be co-quantified, isolate verbatim.

Deliverables in a NEW file `Poincare/Global/BundleDischarge.lean` (do NOT edit existing files, incl. `Poincare.lean`). Report `harness/reports/M5-rigid-80_{done|blocked}.md`.

No vacuous wrappers. Verify: `lake build Poincare.Global.BundleDischarge` and report the actual result. Commit your work.
