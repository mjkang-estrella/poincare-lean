Read harness/worker_contract.md first and obey it strictly.

# Task M5-geo-17: GOAL 10 — attack the smooth-dependence interface (Lipschitz dependence first)

Context: the integrated transverse Gauss lemma waits on `ChartGeodesicInitialVelocitySmoothDependence` (`Poincare/Global/GaussLemmaRadial.lean`; required payload refined in `harness/reports/M5-geo-16_done.md` — READ BOTH). Mathlib lacks ODE smooth dependence, but the DIFFERENCE-QUOTIENT route is elementary: for the C¹ geodesic flow field, two solutions with initial velocities `v` and `v + s·w` differ by `O(s)` (Grönwall on the difference — `Mathlib/Analysis/ODE/Gronwall.lean` has `dist_le_of_approx_trajectories`-class lemmas; the endpoint-controlled flow `Poincare/Global/ExponentialMap.lean` supplies the common interval/ball).

Deliverables, in a NEW file `Poincare/Global/GeodesicDependence.lean` (do NOT edit any existing file, incl. `Poincare.lean`):
1. LIPSCHITZ DEPENDENCE (the honest first step, NOT full differentiability): on the uniform PL interval/ball, `dist (α (z₀,v₁) t) (α (z₀,v₂) t) ≤ C * dist v₁ v₂` for an explicit-existence constant `C` (Grönwall on the flow difference; the flow field's Lipschitz constant comes from the PL data).
2. CONTINUITY COROLLARY: `v ↦ α (z₀,v) t` is continuous (Lipschitz ⟹ continuous) on the ball, hence `v ↦ expAt g x₀ v` is continuous on the small ball (compose with the chart inverse continuity).
3. If genuinely reachable, the difference-quotient CONVERGENCE toward the linearized (Jacobi) equation as the next isolated statement — statement only if the proof blocks; do NOT fake it.
4. Report `harness/reports/M5-geo-17_{done|blocked}.md`: what full differentiability still needs (linearized-equation comparison), refined interface proposal.

No vacuous wrappers. Verify: `lake build Poincare.Global.GeodesicDependence` and report the actual result. Commit your work.
