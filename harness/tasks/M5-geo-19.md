Read harness/worker_contract.md first and obey it strictly.

# Task M5-geo-19: GOAL 10 — uniform Taylor remainder, Grönwall comparison, derivative of the flow

Context: `harness/reports/M5-geo-18_blocked.md` (READ FIRST) — `Poincare/Global/GeodesicLinearized.lean` has the linearized (Jacobi) flow with existence (`exists_chartChristoffel_linearizedGeodesicFlow_solution`) and the POINTWISE Taylor remainder `isLittleO` (`chartChristoffel_geodesicFlowField_taylor_remainder_isLittleO`). Missing: package continuity of the flow field's derivative on the COMPACT TUBE (the uniform PL ball × Icc from `ExponentialMap.lean`/`GeodesicDependence.lean`) into a UNIFORM modulus/remainder bound, then run the Grönwall comparison on `R(s,t) := α(z₀, v + s·w)(t) − α(z₀,v)(t) − s·Ψ(t)` (Lipschitz dependence bounds the difference by `O(s)`, the uniform remainder makes the driving term `o(s)` uniformly, Grönwall propagates `o(s)`).

Deliverables, in a NEW file `Poincare/Global/GeodesicDerivative.lean` (do NOT edit any existing file, incl. `Poincare.lean`):
1. UNIFORM REMAINDER on the compact tube (from `ContDiff` of the flow field: uniform continuity of the derivative on compacts — `CompactSpace`/`HeineCantor` route; state as an ε-δ or filter form usable in 2).
2. THE COMPARISON: `R(s,t) = o(s)` uniformly on the interval (Grönwall).
3. THE DERIVATIVE: `HasDerivAt (fun s ↦ α (z₀, v + s • w) t) (Ψ t) 0` (or the `HasFDerivAt`-in-`w` packaging — document) — discharging the core of `ChartGeodesicInitialVelocitySmoothDependence`; then, if cheap, the integrated transverse Gauss conclusion via `GaussLemmaTransverse.lean`'s pointwise identity.
4. Report `harness/reports/M5-geo-19_{done|blocked}.md`; if blocked, ONE isolated statement.

No vacuous wrappers. Verify: `lake build Poincare.Global.GeodesicDerivative` and report the actual result. Commit your work.
