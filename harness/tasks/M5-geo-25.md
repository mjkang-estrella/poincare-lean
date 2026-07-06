Read harness/worker_contract.md first and obey it strictly.

# Task M5-geo-25: the Fréchet upgrade — d(expAt)|₀ = id

Context: `Poincare/Global/ExponentialDerivativeZero.lean` (report `harness/reports/M5-geo-23_done.md`, READ FIRST) has the two-sided directional derivative of charted `expAt` at `0` in every direction and the criterion `expAt_chart_hasFDerivAt_zero_of_remainder`: ONE uniform velocity-variable little-o remainder upgrades it to `HasFDerivAt … (id) 0`. The uniform-remainder pattern was already closed once (geo-19: `uniform_taylor_remainder_norm_le_on_compact_convex`, Heine–Cantor on compact tubes, `Poincare/Global/GeodesicDerivative.lean`) — apply the same discipline to the velocity variable: uniform smallness of the residual over directions `w` in the ball (the flow derivative + Lipschitz dependence give equicontinuity of the family; mine `GeodesicDependence.lean` + `GeodesicFlowDerivative.lean`).

Deliverables, in a NEW file `Poincare/Global/ExponentialFrechet.lean` (do NOT edit any existing file, incl. `Poincare.lean`):
1. THE UNIFORM REMAINDER exactly as the criterion demands (spelling adaptations documented).
2. THE FRÉCHET DERIVATIVE: `HasFDerivAt (fun v ↦ extChartAt I x₀ (expAt g x₀ v)) (ContinuousLinearMap.id ℝ _) 0` (or the criterion's exact conclusion shape) — d(exp)|₀ = id.
3. If cheap: the local-injectivity/inverse-function payoff note (do NOT force — Mathlib's inverse function theorem needs `ContDiffAt`/strict derivative; state honestly in the report what the C¹-at-0 gap is).
4. Report `harness/reports/M5-geo-25_{done|blocked}.md`; if blocked, ONE statement.

No vacuous wrappers. Verify: `lake build Poincare.Global.ExponentialFrechet` and report the actual result. Commit your work.
