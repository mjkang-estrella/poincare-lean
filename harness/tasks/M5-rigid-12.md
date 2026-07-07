Read harness/worker_contract.md first and obey it strictly.

# Task M5-rigid-12: discharge the shared-factor expansions — the local isometry unconditional

Context: `harness/reports/M5-rigid-11_done.md` (READ FIRST). `CartanLocalIsometry.lean` proves the pullback identity + `cartanMap_isLocalIsometry_on_normalBall` ASSUMING the source and target endpoint metric expansions have the shared Cartan radial/transverse factors (read the exact hypothesis structure). THE DISCHARGE: both sides satisfy it because both metrics have constant sectional curvature 1 — SOURCE `g` by task hypothesis, TARGET `roundSphereMetric3` by the witness (`roundSphereMetric3_hasConstantSectionalCurvature_one`, `RoundSphereWitness.lean`) — and the endpoint metric expansion (radial 1 / transverse sin/t / zero cross) follows from the metric-generic machinery: the differential surface (`CartanDifferential.lean` — proven for ANY closed metric), the Jacobi sin formula (`JacobiOscillator.lean` — for ANY constant-curvature-1 metric), Gauss pairing (`GaussLemmaIntegrated.lean`), constant speed (`GeodesicSpeed.lean`). Instantiate the expansion hypothesis on each side.

Deliverables, in a NEW file `Poincare/Global/CartanIsometryFinal.lean` (do NOT edit any existing file, incl. `Poincare.lean`):
1. THE SOURCE EXPANSION for any `g` with `HasConstantSectionalCurvature3 g 1` (assemble the metric-generic lemmas into rigid-11's exact hypothesis shape).
2. THE TARGET EXPANSION for `roundSphereMetric3` (same assembly + the witness).
3. 🎯 THE UNCONDITIONAL LOCAL ISOMETRY: `cartanMap` (with any alignment from `tangentAlignment_nonempty`) is a chart-local isometry on the normal ball, for every closed simply-connected `g` with constant curvature 1 — instantiating rigid-11.
4. Report `harness/reports/M5-rigid-12_{done|blocked}.md`; if blocked, ONE statement.

No vacuous wrappers. Verify: `lake build Poincare.Global.CartanIsometryFinal` and report the actual result. Commit your work.
