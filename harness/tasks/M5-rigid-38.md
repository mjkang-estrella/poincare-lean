Read harness/worker_contract.md first and obey it strictly.

# Task M5-rigid-38: the shifted-base strict remainder — the strict derivative at v lands

Context: prerequisite (a) is DONE: `linearizedEndpointCLM` (`LinearizedCLM.lean` — the derivative candidate as an `E →L[ℝ] E` with `linearizedEndpointCLM_apply`). Prerequisite (b), per `harness/reports/M5-rigid-36_blocked.md`: the TWO-VARIABLE strict remainder at a shifted base `v` — `‖exp(y) − exp(x) − CLM(y − x)‖ = o(‖y − x‖)` as `(x,y) → (v,v)` jointly. THE TEMPLATE: `expAt_chart_hasStrictFDerivAt_zero`'s proof (`ExponentialLocalHomeo.lean` — READ IT END TO END): it combined Lipschitz dependence (`GeodesicDependence.lean` — valid on the WHOLE uniform ball, not just at 0), the uniform Taylor remainders (`GeodesicDerivative.lean` — compact-tube uniform, ANY base in the tube), and the flow derivative (`GeodesicFlowDerivative.lean` — at any hosted initial data). The zero-anchoring was a choice, not a necessity — replay with base `v` in the shrunk ball and the CLM candidate at `v`'s data.

Deliverables, in a NEW file `Poincare/Global/ExponentialStrictAtV.lean` (do NOT edit any existing file, incl. `Poincare.lean`):
1. 🎯 `expAt_chart_hasStrictFDerivAt_at`-shaped: for `v` in a positive shrunk ball, `HasStrictFDerivAt (expAtChartOpenPartialHomeomorph …) (the CLM at v's data) v`.
2. The same for `roundSphereMetric3` (the machinery is metric-generic — instantiate).
3. Report `harness/reports/M5-rigid-38_{done|blocked}.md`; if blocked, ONE estimate.

No vacuous wrappers. Verify: `lake build Poincare.Global.ExponentialStrictAtV` and report the actual result. Commit your work.
