Read harness/worker_contract.md first and obey it strictly.

# Task M5-geo-35: ORCHESTRATOR REROUTE — mine Mathlib's own lower comparison

Context: the anti-Lipschitz cluster (M5-geo-31..34, blocked reports) kept rebuilding the path first-exit dichotomy from scratch. REROUTE: Mathlib's `Mathlib/Geometry/Manifold/Riemannian/Basic.lean` ALREADY proves the lower-comparison direction as part of the `EMetricSpace.ofRiemannianMetric` topology equality — see the docstring near line 196: "two inclusions are proved respectively in `eventually_riemannianEDist_lt` and `setOf_riemannianEDist_lt_subset_nhds`", with the short-path argument at ~line 205 ("a short path from x…"). READ that file's section carefully: identify the PUBLIC lemmas expressing "small `riemannianEDist` forces membership in a chart-neighborhood" and any quantitative form ("path of e-length < c stays near x / chart distance controlled"). Our induced distance is definitionally this `riemannianEDist` (`induced_edist_eq_riemannianEDist`, `Poincare/Global/GeodesicDistance.lean`).

Deliverables, in a NEW file `Poincare/Global/AntilipschitzMathlib.lean` (do NOT edit any existing file, incl. `Poincare.lean`):
1. Extract/consume the Mathlib lower-comparison (public lemmas preferred; if the quantitative core is private/inline, REPLAY its proof pattern — do not reinvent the induction the previous tasks attempted) to obtain the pairwise bound `exists_chart_ball_pairwise_pathELength_lower_bound` (geo-32 spelling) OR directly the anti-Lipschitz ball statement `exists_extChartAt_symm_antilipschitz_ball` (vol-7/NormalizedFlow spelling) — whichever the Mathlib form reaches faster; the assemblies in `AntilipschitzBall.lean`/`AntilipschitzBallFinal.lean`/`AntilipschitzClose.lean` and `GeodesicDistanceLower.lean` are there to compose with.
2. THE THREE PAYOFFS: unconditional AntilipschitzWith ball; `LocalChartAntilipschitzLowerBound` + `volumeMeasure_univ_ne_zero` (consumer proven in `NormalizedFlow.lean`); `dist x₀ (expAt g x₀ v) ≥ c·‖v‖`-shaped.
3. Report `harness/reports/M5-geo-35_{done|blocked}.md`; if blocked, state exactly what Mathlib's lemmas do and do not give.

No vacuous wrappers. Verify: `lake build Poincare.Global.AntilipschitzMathlib` and report the actual result. Commit your work.
