Read harness/worker_contract.md first and obey it strictly.

# Task M5-geo-23: exp derivative at zero — d(expAt)|₀ = id

Context: the flow derivative is proven (`chartChristoffel_initialVelocity_hasDerivAt_of_uniform_geodesicFlow`, `Poincare/Global/GeodesicFlowDerivative.lean`): `s ↦ α(z₀, v + s•w) t` has derivative `Ψ t` at `0`, where `Ψ` solves the linearized system (`GeodesicLinearized.lean`) with `Ψ 0 = (0, w)`. `expAt` is the fixed-time endpoint with homogeneity-rescaled velocity (`ExponentialFixedTime.lean`), continuous on its ball (`GeodesicDependence.lean`), with ray laws (`ExponentialRayLaw*.lean`).

Deliverables, in a NEW file `Poincare/Global/ExponentialDerivativeZero.lean` (do NOT edit any existing file, incl. `Poincare.lean`):
1. JACOBI SHORT-TIME EXPANSION: for the linearized solution with `Ψ 0 = (0, w)`: the position component satisfies `J t = t • w + o(t)` near `0` (integrate `J' = K`, `K 0 = w`, `K` continuous — fundamental-theorem style; state as `HasDerivAt (fun t ↦ J t) w 0` or the isLittleO form — document).
2. THE DERIVATIVE AT ZERO along directions: `HasDerivAt (fun s ↦ extChartAt I x₀ (expAt g x₀ (s • w))) w 0` — you may already have this via `expAt_chart_hasDerivWithinAt_of_norm_lt` (`ExponentialRayLaw.lean` — check whether it IS this statement; if so, upgrade to the two-sided/`HasFDerivAt`-candidate form): the REAL target is the LINEAR approximation in the vector variable: `expAt g x₀ v = (extChartAt I x₀).symm (extChartAt I x₀ x₀ + v + o(‖v‖))`-shaped — i.e. the chart representation of `expAt` has Fréchet derivative `id` at `0`. Route: combine the flow derivative (in `w`, at fixed rescaled time) with homogeneity; the derivative candidate is the identity because `J(ε)/ε → w`-consistently under the `expAt` rescaling. Deliver the strongest form that closes; a directional (Gateaux, all directions) form + continuity is an acceptable strict-partial with the Fréchet upgrade isolated.
3. Report `harness/reports/M5-geo-23_{done|blocked}.md`.

No vacuous wrappers. Verify: `lake build Poincare.Global.ExponentialDerivativeZero` and report the actual result. Commit your work.
