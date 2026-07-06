Read harness/worker_contract.md first and obey it strictly.

# Task M5-geo-31: the lower bound — paths out of a chart ball have length bounded below

Context: the sharp UPPER bound is proven (`expAt_dist_le_chartGeodesicMetric_sqrt`, `Poincare/Global/GeodesicLengthFinal.lean`). The missing half of local distance realization (and the SHARED estimate with the parked volume-positivity thread, `harness/reports/M5-vol-7_blocked.md` — READ IT: `exists_extChartAt_symm_antilipschitz_ball` with the route: bounded chart derivative on a closed neighborhood + short paths stay local + diameter/margin split): any path from `x₀` to a point outside the image of a small chart ball has `pathELength ≥ c > 0`, and more precisely the anti-Lipschitz comparison `dist(x, y) ≥ K⁻¹ · ‖chart x − chart y‖` on a small ball.

Route (from the vol-7 report + the now-richer toolkit): on a compact closed chart ball, the metric `G` has a uniform positive lower eigenvalue bound (positive-definiteness + continuity + compactness — the `chartMetric`/`fiber_inner_eq` identifications from `GeodesicLength.lean`, the continuity machinery from `VolumeDensity.lean`); a path's `pathELength` dominates the Euclidean length of its chart image times the eigenvalue root while it stays in the ball (integrand comparison — mine how `VolumeFinitenessComparison.lean` did the UPPER comparison and mirror it); a path leaving the ball has chart-image length ≥ the radius margin (continuity/connectedness exit argument).

Deliverables, in a NEW file `Poincare/Global/GeodesicDistanceLower.lean` (do NOT edit any existing file, incl. `Poincare.lean`):
1. UNIFORM METRIC LOWER BOUND on a compact chart ball (eigenvalue-root form usable in the integrand).
2. THE INTEGRAND LOWER COMPARISON + the exit argument.
3. THE ANTI-LIPSCHITZ BALL STATEMENT (the vol-7 shape) — note in the report that this DISCHARGES `LocalChartAntilipschitzLowerBound` (`Poincare/Global/NormalizedFlow.lean`), whose consumer `volumeMeasure_univ_ne_zero_of_localChartAntilipschitzLowerBound` is already proven — include the volume-positivity payoff `volumeMeasure_univ_ne_zero` if the plumbing is cheap.
4. Report `harness/reports/M5-geo-31_{done|blocked}.md`; strict-partial with ONE isolated estimate valid.

No vacuous wrappers. Verify: `lake build Poincare.Global.GeodesicDistanceLower` and report the actual result. Commit your work.
