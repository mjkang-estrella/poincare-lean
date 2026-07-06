Read harness/worker_contract.md first and obey it strictly.

# Task M5-geo-1: GOAL 9 — chart-level geodesic ODE foundations

Context: the minimal conditional Poincaré path (`Poincare/Global/SphereTheorem.lean`) needs `UnitConstantCurvatureSphereRecognition3` (Killing–Hopf, κ = 1). The pinned Mathlib has NO geodesics / exponential map / Hopf–Rinow (`Mathlib/Geometry/Manifold/Riemannian/` = metrics + path e-length only; `Mathlib/Analysis/ODE/` = `PicardLindelof.lean`, `Gronwall.lean`; `Mathlib/Geometry/Manifold/IntegralCurve/` = first-order integral curves). We start the geodesic campaign at the chart level, mirroring the successful Levi-Civita strategy (model space first, transport later).

Deliverables, in a NEW file `Poincare/Global/GeodesicChart.lean` (do NOT edit any existing file, incl. `Poincare.lean` — the orchestrator wires root imports at merge):

1. `def geodesicFlowField (Γ : E → E →L[ℝ] E →L[ℝ] E) : E × E → E × E := fun p ↦ (p.2, - Γ p.1 p.2 p.2)` for `E` a real normed space (work at the generality Mathlib's ODE layer supports; `CompleteSpace`/finite-dimension assumptions are fine — instantiate to `ClosedSmoothModel n = EuclideanSpace ℝ (Fin n)` if you must specialize).
2. LOCAL EXISTENCE: for `Γ` with `ContDiff ℝ 1 Γ` (or a locally-Lipschitz hypothesis — choose what Mathlib's Picard–Lindelöf consumes cleanly), every initial condition `p₀ : E × E` admits `ε > 0` and `γ : ℝ → E × E` with `γ 0 = p₀` and `∀ t ∈ Set.Ioo (-ε) ε, HasDerivAt γ (geodesicFlowField Γ (γ t)) t`.
3. LOCAL UNIQUENESS: two such solutions with the same value at `0` agree on a neighborhood of `0` (Gronwall route; exact interval form free).
4. GEODESIC READING: for a system solution `γ` with components `x t := (γ t).1`, `v t := (γ t).2`: prove `HasDerivAt x (v t) t` and `HasDerivAt v (-(Γ (x t)) (v t) (v t)) t` on the interval — the honest second-order geodesic equation.
5. Report `harness/reports/M5-geo-1_assets.md`: inventory of Mathlib ODE / integral-curve / Riemannian assets relevant to geodesics, the exponential map, and Hopf–Rinow; final signatures of your theorems; an honest roadmap (next 3-5 tasks) toward manifold-level geodesics for `Poincare.ClosedSmoothRiemannianMetric` (its Levi-Civita connection is `g.leviCivita`, `Poincare/Global/Curvature.lean`; chart Christoffel machinery: `Poincare/ModelChristoffel.lean`, `Poincare/Global/LeviCivitaTransport.lean`).

Signature adaptation to the actual Mathlib API is sanctioned within the stated semantics; document any adaptation in the report. No vacuous wrappers; every hypothesis must be used or removed.

Verify: `lake build Poincare.Global.GeodesicChart` and report the actual result. Commit your work.
