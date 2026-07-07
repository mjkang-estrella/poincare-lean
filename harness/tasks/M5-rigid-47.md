Read harness/worker_contract.md first and obey it strictly.

# Task M5-rigid-47: THE FINAL COMPOSITION — every piece exists; compose them

Context: `harness/reports/M5-rigid-46_done.md` + `M5-rigid-45_blocked.md` (READ BOTH). THE COMPLETE INVENTORY (all proven, all gated):
- strict derivatives both sides, common radius: `exists_common_shrunk_source_target_strictDeriv_of_hosted_linearized_pl` (`CartanCascade.lean`)
- the action equation: `linearizedEndpointCLM_apply_sourceScaledNormalVector_of_radial_and_rescaled_harmonic` (`CartanActionEquations.lean`) — its radial hypothesis from the hosted endpoint derivative (`CartanHomogeneity.lean`), its rescaled-harmonic hypothesis from the oscillator interval discharge (REUSE the discharge inside `CartanIsometryTheorem.lean`'s proof of `actual_jacobi_norms_eq_pinned_on_cutoff_one_Icc`)
- the equivalence upgrade: `exists_continuousLinearEquiv_of_sourceScaledNormalVector_action` (`CartanEquivUpgrade.lean`)
- the source pairing blocks: `actual_jacobi_pairing_eq_pinned_of_quadratic_and_linearized_unique` (`CartanIsometryPackage.lean`) + constant speed + integrated Gauss (+ the rigid-30/31/32 endpoint conversions in `CartanDomainShrink/CartanHomogeneity.lean`)
- the target side: SAME generic theorems at `roundSphereMetric3` (the witness `roundSphereMetric3_hasConstantSectionalCurvature_one`)
- the consumer: `cartanMap_isLocalIsometry_on_punctured_normalBall_of_hosted_scale_endpoint_pairings` (`CartanScaleGeneric.lean`)
THE TASK: COMPOSE. Choose ONE `v` quantification (the common shrunk ball intersected with whatever each piece needs — one final radius intersection), instantiate each piece, feed the consumer. 🎯 DELIVERABLE: `cartanMap_isLocalIsometry`-shaped — for every closed simply-connected constant-curvature-1 `g`, anchors, some alignment `L`: the pullback equality on the punctured shrunk ball. If ONE piece's hypothesis genuinely cannot be fed, isolate THAT hypothesis verbatim.

Deliverables in a NEW file `Poincare/Global/CartanFinalComposition.lean` (do NOT edit existing files, incl. `Poincare.lean`). Report `harness/reports/M5-rigid-47_{done|blocked}.md`.

No vacuous wrappers. Verify: `lake build Poincare.Global.CartanFinalComposition` and report the actual result. Commit your work.
