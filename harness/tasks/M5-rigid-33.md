Read harness/worker_contract.md first and obey it strictly.

# Task M5-rigid-33: the (u,T) assembly — the hosted data becomes the blocks

Context: `harness/reports/M5-rigid-32_blocked.md` (READ FIRST). HOSTED (`CartanHomogeneity.lean`): for small `v`, the working pair `u = (δ/2)·v̂`, `T = ‖v‖/(δ/2)` with `T • u = v`, `‖u‖ < δ`, all cutoff-one PL hypotheses at `(u,T)`, the `expAt v` endpoint formula, the radial endpoint derivative. THE REMAINING CONVERSION: the source endpoint pairing BLOCKS (the bridge's hypotheses, `CartanCoefficientBridge.lean`) and the strict differential identifications, at the `(u,T)` parameterization: transverse-transverse from `actual_jacobi_pairing_eq_pinned_of_quadratic_and_linearized_unique` (`CartanIsometryPackage.lean`) + `actual_jacobi_norms_eq_pinned_on_cutoff_one_Icc` (`CartanIsometryTheorem.lean`) evaluated at `t = T` along the `(u)`-geodesic (their hypotheses ARE the hosted cutoff-one data — check shapes and feed); radial from the hosted endpoint derivative + constant speed; cross from integrated Gauss (`GaussLemmaIntegrated/SmoothDependenceDischarge.lean`); the `D(expAt)(v)`-image identification via `T • u = v` + the flow-derivative/homogeneity laws (`GeodesicFlowDerivative.lean`, `ExponentialRayLawFull.lean`). Reconcile the sin normalization: the pinned scalars at `(u,T)` give `sin(sT)`-shaped values with `s` the `u`-speed — express the block's expected function in those terms (the bridge's blocks are parameterized by functions — supply the correct ones; do NOT force `sin‖v‖` if the honest value differs — the two sides share whatever the honest function is).

Deliverables in a NEW file `Poincare/Global/CartanBlocksFinal.lean` (do NOT edit existing files, incl. `Poincare.lean`):
1. THE BLOCKS at `(u,T)` (source; the target by the same generic route + the witness).
2. 🎯 THE LOCAL ISOMETRY via the bridge on the hosted ball.
3. Report `harness/reports/M5-rigid-33_{done|blocked}.md`; if blocked, ONE statement.

No vacuous wrappers. Verify: `lake build Poincare.Global.CartanBlocksFinal` and report the actual result. Commit your work.
