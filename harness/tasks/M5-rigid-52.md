Read harness/worker_contract.md first and obey it strictly.

# Task M5-rigid-52: hΦderHosted assembled — run the composition

Context: `harness/reports/M5-rigid-51_done.md` + `M5-rigid-50_blocked.md` + `M5-rigid-49_blocked.md` (READ ALL THREE — the chain of one-hypothesis rounds). NOW PROVEN: the acceleration identity (`coordinateJacobiAcceleration_chartChristoffelField_eq_neg_sub_corrections_at_state`, `AccelerationIdentity.lean`) — the exact input of `hosted_rescaled_harmonic_hasDerivWithinAt_of_acceleration_eq` (`HarmonicHosted.lean`). ASSEMBLE: (1) feed the identity → `hΦderHosted`; (2) feed that + `hosted_linearized_endpoint_eq_rescaled_harmonic_of_uniqueOn_Icc` (`CartanEndpointUnique.lean`) into `linearizedEndpointCLM_apply_sourceScaledNormalVector_of_hosted_endpoint_unique` (`CartanIsometryDone.lean`) → the ACTION EQUATIONS with everything discharged; (3) the equivalence upgrade (`CartanEquivUpgrade.lean`) on the resulting diagonal action; (4) the cascade strict derivatives (`CartanCascade.lean`) + scale normalization (`CartanFinalComposition.lean`); (5) the pairing blocks (`CartanIsometryPackage/Theorem.lean` + speed + Gauss at the hosted conversions); (6) 🎯 feed `cartanMap_isLocalIsometry_on_punctured_normalBall_of_hosted_scale_endpoint_pairings` (`CartanScaleGeneric.lean`): THE LOCAL ISOMETRY. If ONE hypothesis emerges, isolate verbatim (the established pattern).

Deliverables in a NEW file `Poincare/Global/CartanTheIsometry.lean` (do NOT edit existing files, incl. `Poincare.lean`). Report `harness/reports/M5-rigid-52_{done|blocked}.md`.

No vacuous wrappers. Verify: `lake build Poincare.Global.CartanTheIsometry` and report the actual result. Commit your work.
