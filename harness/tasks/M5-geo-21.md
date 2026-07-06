Read harness/worker_contract.md first and obey it strictly.

# Task M5-geo-21: GOAL 10 — instantiate the residual hypotheses: the flow derivative lands

Context: `harness/reports/M5-geo-20_blocked.md` (READ FIRST) — `Poincare/Global/GeodesicDerivativeFinal.lean` has the abstract Grönwall residual layer and `initialVelocity_hasDerivAt_of_gronwall_residual_bound`; the ONE remaining statement is the PL-flow INSTANTIATION: verify the residual `R(s,t) = α(z₀, v + s•w) t − α(z₀,v) t − s·Ψ t` satisfies the required zero-initial + derivative-inequality hypotheses (`‖R'ₛ(t)‖ ≤ K·‖R(s,t)‖ + η·‖s‖`) for the uniform geodesic flow. All inputs proven: flow ODE on Icc + ball control (`ExponentialMap.lean`, `ExponentialMapDef.lean`), linearized solution Ψ (`GeodesicLinearized.lean`), uniform Taylor remainder (`GeodesicDerivative.lean`), Lipschitz dependence (`GeodesicDependence.lean`).

Deliverables, in a NEW file `Poincare/Global/GeodesicFlowDerivative.lean` (do NOT edit any existing file, incl. `Poincare.lean`):
1. THE INSTANTIATION: differentiate `R` in `t` (three HasDerivAt's), expand via the flow field, insert the Taylor remainder around `α(z₀,v) t` and the linearized equation for Ψ, bound via uniform remainder + Lipschitz dependence — discharging the hypotheses on the common interval/ball.
2. THE FLOW DERIVATIVE: `HasDerivAt (fun s ↦ α (z₀, v + s • w) t) (Ψ t) 0` for fixed times — via the abstract layer.
3. If cheap, the integrated transverse Gauss glue; else isolate.
4. Report `harness/reports/M5-geo-21_{done|blocked}.md`; if blocked, ONE statement.

No vacuous wrappers. Verify: `lake build Poincare.Global.GeodesicFlowDerivative` and report the actual result. Commit your work.
