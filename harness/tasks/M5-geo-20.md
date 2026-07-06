Read harness/worker_contract.md first and obey it strictly.

# Task M5-geo-20: GOAL 10 — the Grönwall residual: derivative of the geodesic flow

Context: `harness/reports/M5-geo-19_blocked.md` (READ FIRST) isolates the SINGLE remaining statement for the flow derivative — the Grönwall residual comparison. All ingredients proven: uniform Taylor remainder on compact convex tubes (`Poincare/Global/GeodesicDerivative.lean`), linearized flow existence + pointwise remainder (`GeodesicLinearized.lean`), Lipschitz dependence + uniform flow (`GeodesicDependence.lean`), endpoint control + interval uniqueness (`ExponentialMap.lean`).

Deliverables, in a NEW file `Poincare/Global/GeodesicDerivativeFinal.lean` (do NOT edit any existing file, incl. `Poincare.lean`):
1. THE RESIDUAL COMPARISON exactly as isolated in the report (spelling adaptations documented): the residual `R(s,t) = α(z₀, v + s•w)(t) − α(z₀,v)(t) − s·Ψ(t)` satisfies the Grönwall-type integral/derivative bound with the uniform-remainder driving term, hence `R(s,·) = o(s)` uniformly on the interval.
2. THE DERIVATIVE: `HasDerivAt (fun s ↦ α (z₀, v + s • w) t) (Ψ t) 0` at fixed times in the interval.
3. If cheap: the integrated transverse Gauss conclusion via `GaussLemmaTransverse.lean`'s pointwise identity; else isolate its glue.
4. Report `harness/reports/M5-geo-20_{done|blocked}.md`; if blocked, ONE statement.

No vacuous wrappers. Verify: `lake build Poincare.Global.GeodesicDerivativeFinal` and report the actual result. Commit your work.
