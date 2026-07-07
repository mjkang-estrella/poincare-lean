Read harness/worker_contract.md first and obey it strictly.

# Task M5-rigid-40: discharge the Grönwall side conditions + the differential actions — the isometry instantiation

Context: `harness/reports/M5-rigid-39_done.md` (READ FIRST). PROVEN: `expAtChartOpenPartialHomeomorph_hasStrictFDerivAt_of_shifted_gronwall` (`ExponentialStrictClose.lean` — read its exact side hypotheses) with the CLM value. TWO discharge steps to the isometry: (1) THE SIDE CONDITIONS: instantiate the theorem's Grönwall/residual hypotheses from rigid-38's shifted Taylor estimates (`ExponentialStrictAtV.lean` — the chart-Christoffel and roundSphere closed-ball instances were built precisely as these driving bounds) — producing the UNCONDITIONAL strict derivatives `A` (source, at `v`) and `B` (target, at `L v`) on a shrunk ball; (2) THE DIFFERENTIAL ACTIONS (`hDu`-family of `cartanMap_isLocalIsometry_on_punctured_normalBall_of_hosted_scale_endpoint_pairings`, `CartanScaleGeneric.lean`): the CLM's action on the radial/transverse decomposition with the hosted scales — the CLM value IS the linearized endpoint (`linearizedEndpointCLM_apply`), whose radial action is the ray-law derivative (hosted, `CartanHomogeneity.lean`) and transverse action is the pinned sin values (`CartanIsometryTheorem/Package.lean` at `(u,T)`) — assemble.
Then 🎯 instantiate the hosted-scale theorem: THE LOCAL ISOMETRY on the shrunk punctured ball, for every constant-curvature-1 `g`, unconditional.

Deliverables in a NEW file `Poincare/Global/CartanIsometryClose.lean` (do NOT edit existing files, incl. `Poincare.lean`). Strict-partial per step; ONE isolated statement max. Report `harness/reports/M5-rigid-40_{done|blocked}.md`.

No vacuous wrappers. Verify: `lake build Poincare.Global.CartanIsometryClose` and report the actual result. Commit your work.
