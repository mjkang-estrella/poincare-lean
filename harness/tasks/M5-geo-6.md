Read harness/worker_contract.md first and obey it strictly.

# Task M5-geo-6: GOAL 9 — PL flow with endpoint control, then the exponential map

Context: `harness/reports/M5-geo-5_blocked.md` isolates the gap: Mathlib's exported `ContDiffAt.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt` gives a common existence ball/time but drops (i) the path-bound "solution stays in the PL closed ball on the closed interval" (the internal `ODE.FunSpace.compProj_mem_closedBall` has it) and (ii) uniqueness among ball-staying curves on the interval. With those, the fixed-time exponential `expAt g x₀ v := (solution with velocity ε⁻¹ • v evaluated at time ε)` becomes provable, with the ray law via reparametrization + interval uniqueness (`Poincare/Global/{GeodesicChart,GeodesicTransport,GeodesicGerm,ExponentialGerm,ExponentialDomain}.lean` supply the geodesic side; `exists_uniform_local_geodesic_chart_solution` is already in).

Deliverables, in a NEW file `Poincare/Global/ExponentialMap.lean` (do NOT edit existing files, incl. `Poincare.lean`):
1. PL FLOW WITH ENDPOINT CONTROL: from an `IsPicardLindelof`-style hypothesis (or rebuilding via `ODE.FunSpace` — mine `Mathlib/Analysis/ODE/PicardLindelof.lean` internals; they are public defs even when the convenience wrapper drops information), a theorem in the schematic shape of the blocked report: a common local flow `α` with, for every initial point in the small ball: initial value, `HasDerivWithinAt` on `Icc`, AND `α x t ∈ closedBall x₀ a` for all `t ∈ Icc`. State it for the autonomous case you need (the geodesic flow field) if the general version fights the API.
2. INTERVAL UNIQUENESS among ball-staying solutions on `Icc` (Grönwall route, `ODE_solution_unique_of_mem_set`-style with the Lipschitz set = the PL ball).
3. `expAt (g) (x₀ : M) : ClosedSmoothModel n → M` on an honest ball (junk value outside — document), with proven: `expAt g x₀ 0 = x₀`; ray law `expAt g x₀ (t • v) = geodesicGermAt g x₀ v t` for `t ∈ [0, small]`, `‖v‖` small (quantifier shape free; semantics frozen); chart-source membership for small `‖v‖`.
4. Report `harness/reports/M5-geo-6_{done|blocked}.md`; strict-partial (deliverables 1-2 alone) is valid if 3 still blocks — isolate exactly why.

Verify: `lake build Poincare.Global.ExponentialMap` and report the actual result. Commit your work.
