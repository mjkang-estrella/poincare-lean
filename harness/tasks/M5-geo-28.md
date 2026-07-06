Read harness/worker_contract.md first and obey it strictly.

# Task M5-geo-28: the radial path export — germ curve smoothness and its length

Context: `harness/reports/M5-geo-27_blocked.md` (READ FIRST) isolates what the sharp distance upper bound needs: the geodesic germ curve as an honest `ContMDiffOn`/`MDifferentiableOn` path on a closed interval with its `pathELength` computed from constant speed. Available: the chart solution is C¹ (solves the C¹ ODE system — `HasDerivAt` at every interval point, `GeodesicGerm.lean`/`ExponentialFixedTime.lean` flows), the pulled-back curve stays in the chart (target-shrunk flow), the chart inverse is smooth (`extChartAt` symm on its target), constant speed (`GeodesicSpeed.lean`), and the distance bridge `induced_edist_le_pathELength` (`GeodesicDistance.lean`).

Deliverables, in a NEW file `Poincare/Global/GeodesicPathLength.lean` (do NOT edit any existing file, incl. `Poincare.lean`):
1. CURVE REGULARITY: the germ/flow curve `c : ℝ → M` on `[0, τ]` is `MDifferentiableOn`/`ContMDiffOn 1` (whatever `pathELength` consumes — inspect Mathlib's `Riemannian/PathELength.lean` integrand requirements FIRST and target exactly that; the chart representation is C¹ by the ODE, composition with the smooth chart inverse gives the manifold regularity — mine how `VolumeFinitenessComparison.lean` fed segment paths in).
2. LENGTH COMPUTATION: `pathELength` of the radial germ curve on `[0, t]` `= t * sqrt(G z₀ v₀ v₀)`-shaped (constant speed integrand — the metric pairing of the velocity is constant by `chart_geodesic_speed_constantOn`; mind the blended-vs-actual metric on the cutoff-1 zone: `blendedChartMetric = chartMetric = g.inner` there, lemmas in `GeodesicReanchor.lean`/`RoundSphereCurvature.lean` patterns).
3. THE SHARP UPPER BOUND: `dist x₀ (expAt g x₀ v) ≤ sqrt(g.inner x₀ (chart-transport of v) …)`-shaped via the bridge (exact spelling per what 1-2 produce; document).
4. Report `harness/reports/M5-geo-28_{done|blocked}.md`.

No vacuous wrappers. Verify: `lake build Poincare.Global.GeodesicPathLength` and report the actual result. Commit your work.
