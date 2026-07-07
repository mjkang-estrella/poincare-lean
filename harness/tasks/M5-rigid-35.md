Read harness/worker_contract.md first and obey it strictly.

# Task M5-rigid-35: discharge the hosted surface — strict derivatives and differential actions

Context: `harness/reports/M5-rigid-34_done.md` + the theorem `cartanMap_isLocalIsometry_on_punctured_normalBall_of_hosted_scale_endpoint_pairings` (`CartanScaleGeneric.lean`, READ ITS FULL HYPOTHESIS LIST). Two hypothesis families remain:
(1) STRICT DERIVATIVES AT GENERAL `v`: `HasStrictFDerivAt (expAtChartOpenPartialHomeomorph …) A v` for `v ≠ 0` in the (shrunk) source — proven AT 0 (`expAt_chart_hasStrictFDerivAt_zero`, `ExponentialLocalHomeo.lean` via the two-variable uniform remainder); the SAME argument at shifted base points (the uniform remainders in `GeodesicDerivative/ExponentialFrechet.lean` are ball-uniform — check whether the two-variable estimate already covers moving base points; if the exported form is anchored at 0, replay the proof pattern at `v`); the derivative CANDIDATE `A` at `v` is the endpoint differential (the flow derivative at `(u,T)` — `CartanHomogeneity.lean` hosting).
(2) THE DIFFERENTIAL ACTIONS (`hDu`-family): the Cartan chart differential acts by the hosted scales on the decomposed vectors — assemble from the endpoint differential surface (`CartanDifferential.lean`), the hosted conversion (`CartanHomogeneity.lean`), the pinned pairing/scalars (`CartanIsometryTheorem/Package.lean`), and the alignment intertwining — at the `(u,T)` parameterization with the honest hosted scales (`hostedSourceTransverseScale` etc.).

Deliverables, in a NEW file `Poincare/Global/CartanHostedDischarge.lean` (do NOT edit any existing file, incl. `Poincare.lean`): the two families discharged on a (re)shrunk ball + 🎯 THE LOCAL ISOMETRY instantiated. Strict-partial per family; ONE isolated statement max. Report `harness/reports/M5-rigid-35_{done|blocked}.md`.

No vacuous wrappers. Verify: `lake build Poincare.Global.CartanHostedDischarge` and report the actual result. Commit your work.
