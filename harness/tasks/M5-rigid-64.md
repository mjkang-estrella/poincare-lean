Read harness/worker_contract.md first and obey it strictly.

# Task M5-rigid-64: instantiate the two feeds — the isometry without pairing hypotheses

Context: `harness/reports/M5-rigid-63_done.md` (READ FIRST). THE CONSUMER IS ONE STEP AWAY: `cartanMap_isLocalIsometry_on_normalBall_of_common_rescaled_anchor_pairings` (`SourcePackage.lean`) needs exactly TWO hypotheses — `hSourceRescaled` and `hTargetRescaled` (the sin²-pinned pairing formulas at common time `T`). THE SUPPLIERS EXIST: `target_hosted_rescaled_endpoint_pairing_eq_pinned_of_interval_norm_package` (`TargetPackage.lean`) and its source mirror (`SourcePackage.lean`) — each conditional on interval/norm packages. THE TASK: DISCHARGE those packages at the actual hosted data — the cutoff-one flow facts (`CartanHomogeneity.lean` hosting, `CartanIsometryTheorem.lean`'s source interval discharge, the sphere-side instances from `TargetPackage/CartanCascade.lean`'s feeds), the actual cascade families (`CartanCascade.lean`) — producing the two feeds for concrete `(v, Ψs, Ψt, T)` on a shrunk ball, then apply the consumer. 🎯 `cartanMap_isLocalIsometry`-shaped with hypotheses ONLY: `HasConstantSectionalCurvature3 g 1` (+ closed/simply-connected instances), anchors, the alignment — NO pairing/interval hypotheses. If ONE package field resists, isolate verbatim.

Deliverables in a NEW file `Poincare/Global/IsometryInstantiate.lean` (do NOT edit existing files, incl. `Poincare.lean`). Report `harness/reports/M5-rigid-64_{done|blocked}.md`.

No vacuous wrappers. Verify: `lake build Poincare.Global.IsometryInstantiate` and report the actual result. Commit your work.
