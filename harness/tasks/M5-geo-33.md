Read harness/worker_contract.md first and obey it strictly.

# Task M5-geo-33: the pairwise path-length lower bound — three payoffs land

Context: `harness/reports/M5-geo-32_blocked.md` (READ FIRST) isolates the LAST statement: `exists_chart_ball_pairwise_pathELength_lower_bound` — for `x, y` in the small chart ball, EVERY path from `x` to `y` has `pathELength ≥ K⁻¹ · ‖chart x − chart y‖`. Proven pieces: the in-ball integrand lower comparison (`inverseChartCurve_enorm_mfderiv_ge_of_chartMetric_sqrt_lower`) and the ball-exit lower bounds (`chart_ball_exit_pathELength_lower_bound`, `GeodesicDistanceLower.lean`); the conditional `AntilipschitzWith` assembly + path-infimum machinery (`AntilipschitzBall.lean`). The two-case argument per path: (i) the path's chart image stays in the bigger ball — its e-length dominates the eigenvalue-root times the CHART-IMAGE Euclidean length ≥ chart-distance of endpoints (the integrand comparison integrated along the path; the chart image of the path is itself a path between the chart points — Euclidean length ≥ straight-line distance); (ii) the path exits the bigger ball — the exit bound gives length ≥ margin, and for `x, y` in the SMALL ball the margin dominates `‖chart x − chart y‖` up to the constant (radius arithmetic). Mind: the exit lemma is anchored at `x₀`'s ball — restate/reuse for paths STARTING at arbitrary `x` in the small ball (triangle/radius bookkeeping).

Deliverables, in a NEW file `Poincare/Global/AntilipschitzBallFinal.lean` (do NOT edit any existing file, incl. `Poincare.lean`):
1. THE PAIRWISE BOUND exactly as isolated (spelling adaptations documented).
2. THE THREE PAYOFFS via the proven assemblies/consumers: the unconditional `AntilipschitzWith` chart-ball statement; `LocalChartAntilipschitzLowerBound` discharged + `volumeMeasure_univ_ne_zero` (consumer proven in `NormalizedFlow.lean`); the distance lower payoff `dist x₀ (expAt g x₀ v) ≥ c·‖v‖`-shaped.
3. Report `harness/reports/M5-geo-33_{done|blocked}.md`; if blocked, ONE statement.

No vacuous wrappers. Verify: `lake build Poincare.Global.AntilipschitzBallFinal` and report the actual result. Commit your work.
