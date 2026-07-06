Read harness/worker_contract.md first and obey it strictly.

# Task M5-geo-32: assemble the anti-Lipschitz bound — distance lower half + volume positivity

Context: `harness/reports/M5-geo-31_blocked.md` (READ FIRST). Proven in `Poincare/Global/GeodesicDistanceLower.lean`: the integrand lower comparison (`inverseChartCurve_enorm_mfderiv_ge_of_chartMetric_sqrt_lower`) and the ball-exit `pathELength` lower bounds (`chart_ball_exit_pathELength_lower_bound`, `exists_…`). Remaining: assemble into the per-anchor anti-Lipschitz statement (the vol-7 shape `exists_extChartAt_symm_antilipschitz_ball` / `LocalChartAntilipschitzLowerBound`, `Poincare/Global/NormalizedFlow.lean`): for `x, y` in the small ball, EVERY path from `x` to `y` either stays in the bigger ball (integrand comparison bounds its length below by the chart distance times the eigenvalue root) or exits (exit bound ≥ margin ≥ chart distance times constant) — the two-case infimum argument, then `dist ≥ K⁻¹·‖chart x − chart y‖` via the path-infimum definition of the induced distance (`induced_edist_eq_riemannianEDist`/`riemannianEDist` infimum API — mine `GeodesicDistance.lean` + Mathlib PathELength inf lemmas).

Deliverables, in a NEW file `Poincare/Global/AntilipschitzBall.lean` (do NOT edit any existing file, incl. `Poincare.lean`):
1. THE TWO-CASE INFIMUM ASSEMBLY → the anti-Lipschitz ball statement (exact vol-7/NormalizedFlow spelling; adaptations documented).
2. DISCHARGE `LocalChartAntilipschitzLowerBound` and conclude `volumeMeasure_univ_ne_zero` via the proven consumer (`volumeMeasure_univ_ne_zero_of_localChartAntilipschitzLowerBound`).
3. THE DISTANCE LOWER PAYOFF: `dist x₀ (expAt g x₀ v) ≥ c·‖v‖`-shaped on the small ball (from 1 + the chart representation of expAt).
4. Report `harness/reports/M5-geo-32_{done|blocked}.md`; if blocked, ONE statement.

No vacuous wrappers. Verify: `lake build Poincare.Global.AntilipschitzBall` and report the actual result. Commit your work.
