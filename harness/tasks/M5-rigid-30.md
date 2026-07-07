Read harness/worker_contract.md first and obey it strictly.

# Task M5-rigid-30: instantiate the three blocks — THE UNCONDITIONAL LOCAL ISOMETRY

Context: `harness/reports/M5-rigid-29_done.md` (READ FIRST). The bridge is PROVEN: `cartanMap_isLocalIsometry_on_punctured_normalBall_of_source_endpoint_pairings` (`CartanCoefficientBridge.lean`) — three endpoint-pairing block hypotheses (radial-radial, radial-transverse, transverse-transverse) ⟹ the local isometry. THE BLOCKS' CONTENT IS PROVEN: transverse-transverse = `actual_jacobi_pairing_eq_pinned_of_quadratic_and_linearized_unique` (`CartanIsometryPackage.lean`) fed by `actual_jacobi_norms_eq_pinned_on_cutoff_one_Icc` (`CartanIsometryTheorem.lean`); radial-radial = constant speed (`chart_geodesic_speed_constantOn`/`GeodesicLengthFinal.lean` forms); radial-transverse = the integrated Gauss orthogonal law (`GaussLemmaIntegrated.lean`, discharged payload versions in `SmoothDependenceDischarge.lean`). THE TASK: align hypothesis shapes — instantiate each block from its proven theorem (the endpoint evaluation `t = ‖v‖`, the interval/zone side conditions from the cutoff-one flow, the flow-derivative identification of `D(expAt)` with `J` values) — for BOTH the source (`HasConstantSectionalCurvature3 g 1`) and the target (`roundSphereMetric3` via the witness).

Deliverables in a NEW file `Poincare/Global/CartanBlocksInstantiate.lean` (do NOT edit existing files, incl. `Poincare.lean`):
1-3. The three blocks instantiated (source and target).
4. 🎯 `cartanMap_isLocalIsometry_unconditional`-shaped: THE LOCAL ISOMETRY for every closed simply-connected constant-curvature-1 `g`, every anchor pair, some alignment.
5. Report `harness/reports/M5-rigid-30_{done|blocked}.md`; if blocked, ONE shape-mismatch isolated.

No vacuous wrappers. Verify: `lake build Poincare.Global.CartanBlocksInstantiate` and report the actual result. Commit your work.
