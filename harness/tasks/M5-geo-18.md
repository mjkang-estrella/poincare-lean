Read harness/worker_contract.md first and obey it strictly.

# Task M5-geo-18: GOAL 10 — the linearized (Jacobi) comparison

Context: `harness/reports/M5-geo-17_done.md` (READ FIRST) specifies the remaining differentiability interface for the geodesic flow: the difference quotient `s⁻¹·(α(z₀, v + s·w) − α(z₀, v))` should converge to the solution `Ψ = (J, K)` of the LINEARIZED system along the base geodesic (`J' = K`, `K' = −(DΓ along γ)(J)(γ₂,γ₂) − 2Γ(γ₁)(K, γ₂)`-shaped). Available: Lipschitz dependence + uniform flow (`Poincare/Global/GeodesicDependence.lean`), endpoint control + interval uniqueness (`ExponentialMap.lean`), C¹ flow field (`GeodesicTransport.lean`).

Deliverables, in a NEW file `Poincare/Global/GeodesicLinearized.lean` (do NOT edit any existing file, incl. `Poincare.lean`):
1. THE LINEARIZED SYSTEM: define the linearized flow field along a chart geodesic solution and prove local existence/uniqueness for it (it is a LINEAR time-dependent ODE — Mathlib's `Analysis/ODE` handles it; the coefficient regularity comes from the C¹ Christoffel field along the continuous solution path).
2. FIRST COMPARISON ESTIMATE (the honest step toward differentiability, do NOT claim full differentiability unless it closes): the difference `α(z₀, v + s·w) − α(z₀, v) − s·Ψ(t)` is `o(s)` or at least `O(s²)`-bounded via a Grönwall argument on the Taylor remainder of the flow field (C¹ ⟹ the remainder is controlled by the modulus of continuity of `DΓ` on the compact tube — if only `o(s)` without rate is reachable, that suffices for differentiability; document which you achieve).
3. If 2 closes: the derivative statement `HasDerivAt (fun s ↦ α (z₀, v + s·w) t) (Ψ t) 0` — discharging the heart of `ChartGeodesicInitialVelocitySmoothDependence`. If it blocks: strict-partial with ONE isolated estimate.
4. Report `harness/reports/M5-geo-18_{done|blocked}.md`.

No vacuous wrappers. Verify: `lake build Poincare.Global.GeodesicLinearized` and report the actual result. Commit your work.
