Read harness/worker_contract.md first and obey it strictly.

# Task M5-geo-9: GOAL 9 — flow-level homogeneity on Icc, then `expAt` (the closer)

Context: `harness/reports/M5-geo-7_blocked.md` isolates the LAST lemma for the exponential map, with the proof plan: show `σ ↦ ((α (z₀, v) (s * σ)).1, s • (α (z₀, v) (s * σ)).2)` solves the chart geodesic ODE with initial velocity `s • v` on the rescaled `Icc`, stays in the common PL ball, and identify it with `α (z₀, s • v)` via `IsPicardLindelof.eqOn_Icc_of_mem_closedBall` — the `Icc`-upgrade of the `geodesicGermAt_smul_eventually` pattern (`Poincare/Global/ExponentialGerm.lean`). Available machinery: `Poincare/Global/ExponentialMap.lean` (endpoint-controlled flow + interval uniqueness), `Poincare/Global/ExponentialMapDef.lean` (target-shrunk flow `exists_uniform_local_geodesic_chart_flow_with_mem_closedBall_mem_target` + germ identification `…_eventuallyEq_germ`). Arrange parameters so `s * σ` stays in the source interval and the scaled velocity stays in the ball (restrict to `s ∈ [0,1]` — that suffices for the ray law; say so).

Deliverables, in a NEW file `Poincare/Global/ExponentialFixedTime.lean` (do NOT edit any existing file, incl. `Poincare.lean`):
1. FLOW HOMOGENEITY ON Icc: for the common geodesic flow `α` from the target-shrunk package, for `s ∈ [0,1]` (or `[0,1]`-interior; honest interval) and `‖v‖` in the shrunken ball: `(α (z₀, s • v) σ) = ((α (z₀, v) (s * σ)).1, s • (α (z₀, v) (s * σ)).2)` for `σ` in the `Icc` — via the reparametrized-solution check + interval uniqueness.
2. `noncomputable def expAt (g) (x₀ : M) : ClosedSmoothModel n → M` — fixed-positive-time endpoint of the flow with rescaled velocity (junk value outside the honest ball; document), with PROVEN: `expAt g x₀ 0 = x₀`; the ray law `expAt g x₀ (t • v) = geodesicGermAt g x₀ v t` for `t ∈ [0, τ)`-honest and `‖v‖` small (via 1 + the germ identification); chart-source membership for small `‖v‖`.
3. Report `harness/reports/M5-geo-9_{done|blocked}.md`: final signatures + next decomposition (exp continuity/smoothness in `v` — note Mathlib smooth-dependence status honestly; derivative at `0`; Gauss lemma prerequisites).

No vacuous wrappers; hypotheses used or removed. Verify: `lake build Poincare.Global.ExponentialFixedTime` and report the actual result. Commit your work.
