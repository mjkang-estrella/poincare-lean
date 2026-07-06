Read harness/worker_contract.md first and obey it strictly.

# Task M5-geo-34: the path dichotomy — the anti-Lipschitz cluster closes

Context: `harness/reports/M5-geo-33_blocked.md` (READ FIRST). Proven: the chart-staying path estimate in exact `ENNReal.ofReal (C⁻¹ * dist)` form (`AntilipschitzBallFinal.lean`), the exit lower bounds (`GeodesicDistanceLower.lean`), the conditional assemblies (`AntilipschitzBall.lean`). LAST piece: the TWO-CASE DICHOTOMY for an arbitrary path with endpoints in the small ball — either its chart image stays in the bigger ball (chart-staying estimate applies) or it exits (exit bound ≥ radius margin ≥ endpoint chart distance times the constant, by radius arithmetic). The dichotomy is classical: the path's chart image is connected/continuous on `[0,1]`; if some parameter leaves the closed bigger ball, a first-exit time exists (continuity + closedness — `Set.mem`/`sInf` argument or Mathlib's `Continuous.exists…`/intermediate-value style lemmas); the truncated path up to first exit stays in the ball and reaches the boundary, so the exit machinery applies to it, and `pathELength` is monotone under truncation (check the PathELength API for restriction monotonicity — mine how `chart_ball_exit_pathELength_lower_bound` was proven, it likely already contains the truncation pattern).

Deliverables, in a NEW file `Poincare/Global/AntilipschitzClose.lean` (do NOT edit any existing file, incl. `Poincare.lean`):
1. THE DICHOTOMY + the pairwise bound `exists_chart_ball_pairwise_pathELength_lower_bound` (exact geo-32 spelling).
2. THE THREE PAYOFFS through the proven assemblies: unconditional `AntilipschitzWith` chart ball; `LocalChartAntilipschitzLowerBound` + `volumeMeasure_univ_ne_zero`; `dist x₀ (expAt g x₀ v) ≥ c·‖v‖`-shaped.
3. Report `harness/reports/M5-geo-34_{done|blocked}.md`; if blocked, ONE statement.

No vacuous wrappers. Verify: `lake build Poincare.Global.AntilipschitzClose` and report the actual result. Commit your work.
