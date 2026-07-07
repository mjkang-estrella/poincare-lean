Read harness/worker_contract.md first and obey it strictly.

# Task M5-rigid-94: the PL packages — construct, select, feed the rays

Context: `harness/reports/M5-rigid-93_blocked.md` (READ FIRST — the VERBATIM zero-centered PL package shapes + the downstream ray fields `hSourceRay/hTargetRay`). THE WITNESSES EXIST IN PIECES: (1) rigid-42's `exists_hosted_linearized_solution_family_on_pl_closedBall` (`LinearizedFamilyExport.lean`) CONSTRUCTED the zero-centered family from a PL fixed point — READ its proof: the `IsPicardLindelof` instance it built is the package the master bundle wants — RE-EXPORT it (replay the construction exporting the package itself, not just the family); the coefficient bounds come from the enriched base curve (`EnrichedCascade.lean`'s `BaseCurvePackage` — continuity of Γ along the exported curve, sup on the compact interval — the rigid-82 `UniformPL.lean` bounded-center machinery); (2) the common-time selection: `CommonTime.lean`'s shared `T` + the packages select `PsiS/PsiT`; (3) the ray fields: `RayIdentification.radial_linearized_endpoint_eq_time_smul_velocity_of_uniform_geodesicFlow` at the selected families (hypothesis alignment — the selected families satisfy the uniform-flow hypotheses by construction). Then the master bundle closes → the assembly → 🎯 `cartanMap_isLocalIsometry` (curvature-only). If ONE resists, isolate verbatim.

Deliverables in a NEW file `Poincare/Global/PLPackages.lean` (do NOT edit existing files, incl. `Poincare.lean`). Report `harness/reports/M5-rigid-94_{done|blocked}.md`.

No vacuous wrappers. Verify: `lake build Poincare.Global.PLPackages` and report the actual result. Commit your work.
