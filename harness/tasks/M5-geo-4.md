Read harness/worker_contract.md first and obey it strictly.

# Task M5-geo-4: GOAL 9 — germ uniqueness consumption, homogeneity, exponential ray

Context: `Poincare/Global/GeodesicGerm.lean` (report `harness/reports/M5-geo-3_done.md`, namespace `Poincare.GeodesicTransport`) provides `geodesicGermAt g x₀ v₀ : ℝ → M` with `geodesicGermAt_zero`, `geodesicGermAt_eventually_mem_source`, `geodesicGermAt_spec` (exposes the chosen chart solution `geodesicGermChartSolution` on `Ioo (-r) r`, `r = geodesicGermRadius > 0`), `geodesicGermAt_chart_hasDerivAt` (chart velocity `v₀` at `0`), same-anchor uniqueness `geodesicFlowField_chartChristoffelField_eventuallyEq` and `pulledback_geodesic_eventuallyEq_of_chartChristoffelField`. `Poincare/Global/GeodesicChart.lean` has the ODE layer.

Deliverables, in a NEW file `Poincare/Global/ExponentialGerm.lean` (do NOT edit any existing file, incl. `Poincare.lean`):

1. ZERO-VELOCITY GERM IS CONSTANT: `∀ᶠ t in 𝓝 0, geodesicGermAt g x₀ 0 t = x₀`. Route: the constant curve `fun _ => (extChartAt I x₀ x₀, 0)` solves the chart system (the flow field vanishes at zero velocity: `geodesicFlowField Γ (z, 0) = (0, -Γ z 0 0) = (0,0)` — CLM applied to `0` is `0`), so Grönwall uniqueness identifies it with the chosen chart solution near `0`.
2. HOMOGENEITY (the exponential-map law): for `s : ℝ`, `∀ᶠ t in 𝓝 0, geodesicGermAt g x₀ (s • v₀) t = geodesicGermAt g x₀ v₀ (s * t)`. Route: `t ↦ γ(s*t)` with `γ` the chosen solution for `v₀`, position/velocity split `(γ₁(s t), s·γ₂(s t))` — CAREFUL: the correct reparametrized state is `η t := ((γ (s*t)).1, s • (γ (s*t)).2)`; verify `η` solves the SAME system (chain rule `HasDerivAt.comp` with `t ↦ s*t`, and the quadratic slot: `Γ z (s•v) (s•v) = s² • Γ z v v` by CLM bilinearity) with initial state `(extChartAt I x₀ x₀, s • v₀)`, then apply Grönwall uniqueness against the chosen solution for `s • v₀`. Handle `s = 0` via deliverable 1 or uniformly.
3. EXPONENTIAL RAY PACKAGING: `def expRayAt (g) (x₀ : M) (v₀ : E) : ℝ → M := geodesicGermAt g x₀ v₀` plus the restated law `expRayAt g x₀ (s • v₀) t = expRayAt g x₀ v₀ (s * t)` (eventually in `t`, for each fixed `s`) and `expRayAt g x₀ v₀ 0 = x₀` — the honest germ-level exponential API. Do NOT define a global `exp : TM x → M` yet (domain control is future work); say so in the report.
4. Report `harness/reports/M5-geo-4_{done|blocked}.md`: final signatures + next decomposition (velocity-smoothness of `(v₀, t) ↦ germ`, chart derivative of `v ↦ expRayAt g x₀ v 1`-analogue at `0` = identity via homogeneity, Gauss lemma prerequisites, chart-overlap independence).

No vacuous wrappers; hypotheses used or removed. Verify: `lake build Poincare.Global.ExponentialGerm` and report the actual result. Commit your work.
