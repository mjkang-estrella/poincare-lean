Read harness/worker_contract.md first and obey it strictly.

# Task M5-geo-12: GOAL 9 — the full-interval ray law for `expAt`

Context: `Poincare/Global/ExponentialFixedTime.lean` defines `expAt` with the ray law only in eventual form (`expAt_eventually_eq_geodesicGermAt : ∀ᶠ t in 𝓝[Icc 0 τ] 0, expAt g x₀ (t • v) = geodesicGermAt g x₀ v t`). `harness/reports/M5-geo-9_blocked.md` isolates the upgrade: interval identification between the PL flow and the chosen `geodesicGermChartSolution` — the flow solves on the full `Icc`, the germ solution on its own `Ioo (-r) r`; identify them on the INTERSECTION via `IsPicardLindelof.eqOn_Icc_of_mem_closedBall` (arrange common ball membership by continuity + shrinking, as in the geo-7 germ identification `exists_uniform_local_geodesic_chart_flow_with_mem_target_eventuallyEq_germ` — study its proof).

Deliverables, in a NEW file `Poincare/Global/ExponentialRayLaw.lean` (do NOT edit any existing file, incl. `Poincare.lean`):
1. INTERVAL IDENTIFICATION: flow solution = germ chart solution on an honest closed subinterval `[0, τ']` (`τ' > 0` uniform for `‖v‖` small).
2. THE RAY LAW: `expAt g x₀ (t • v) = geodesicGermAt g x₀ v t` for all `t ∈ Set.Icc 0 τ'` and `‖v‖` small (explicit honest quantifiers).
3. RIGHT-DERIVATIVE COROLLARY: `HasDerivWithinAt (fun t ↦ extChartAt I x₀ (expAt g x₀ (t • v))) v (Set.Ici 0) 0` (from 2 + `geodesicGermAt_chart_hasDerivAt`, restricted; adapt spelling).
4. Report `harness/reports/M5-geo-12_{done|blocked}.md` (note honestly: smoothness of `expAt` in `v` needs ODE smooth-dependence — flag Mathlib status).

Verify: `lake build Poincare.Global.ExponentialRayLaw` and report the actual result. Commit your work.
