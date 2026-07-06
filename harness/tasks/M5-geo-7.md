Read harness/worker_contract.md first and obey it strictly.

# Task M5-geo-7: GOAL 9 — finish `expAt` from the endpoint-controlled flow

Context: `Poincare/Global/ExponentialMap.lean` (report `harness/reports/M5-geo-6_blocked.md`) landed: `IsPicardLindelof.exists_forall_mem_closedBall_eq_forall_mem_Icc_hasDerivWithinAt_mem_closedBall` (common flow with the PL closed-ball invariant), `IsPicardLindelof.eqOn_Icc_of_mem_closedBall` (interval uniqueness among ball-staying solutions), and the geodesic specialization `Poincare.GeodesicTransport.exists_uniform_local_geodesic_chart_flow_with_mem_closedBall`. The blocked report isolates what remains for `expAt`: (a) shrink the PL ball/radii so positions stay inside `(extChartAt I x₀).target`; (b) identify the flow with `geodesicGermAt`'s chart solution near `0` (both solve; both stay in a common ball after shrinking; apply interval uniqueness); (c) evaluate at a fixed positive time via the flow, with the ray law obtained from a FLOW-level homogeneity (reparametrized solution `t ↦ (pos(s t), s • vel(s t))` + interval uniqueness — the germ-level `geodesicGermAt_smul_eventually` pattern from `Poincare/Global/ExponentialGerm.lean` is the template, now upgraded to `Icc` via the endpoint control).

Deliverables, in a NEW file `Poincare/Global/ExponentialMapDef.lean` (do NOT edit any existing file, incl. `Poincare.lean`):
1. TARGET-SHRUNK FLOW: refine the geodesic specialization to also give `(flow position) ∈ (extChartAt I x₀).target` on the whole `Icc` (openness of the target + continuity/ball control; shrinking `δ`/`ε`/ball radius is sanctioned).
2. GERM IDENTIFICATION: for `‖v₀‖` small, the flow solution with initial velocity `v₀` agrees with `geodesicGermChartSolution g x₀ v₀` on a neighborhood of `0` in `[0, ε]` (interval uniqueness after arranging common ball membership).
3. `noncomputable def expAt (g) (x₀ : M) : ClosedSmoothModel n → M` — via the flow at a fixed positive time with homogeneity-rescaled velocity (junk value outside the honest ball — document the convention), with PROVEN: `expAt g x₀ 0 = x₀`; ray law `expAt g x₀ (t • v) = geodesicGermAt g x₀ v t` for `t` in an honest `[0, τ)` and `‖v‖` small (quantifier shape free, semantics frozen); `expAt g x₀ v ∈ (extChartAt I x₀).source` for `‖v‖` small.
4. Report `harness/reports/M5-geo-7_{done|blocked}.md`; strict-partial with a finer isolated blocker remains valid.

Verify: `lake build Poincare.Global.ExponentialMapDef` and report the actual result. Commit your work.
