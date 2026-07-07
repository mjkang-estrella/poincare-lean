Read harness/worker_contract.md first and obey it strictly.

# Task M5-rigid-18: discharge the smooth-dependence payload from the proven flow derivative

Context: `harness/reports/M5-rigid-17_blocked.md` (READ FIRST): the punctured source expansion needs the endpoint chart-metric/Jacobi assembly, which needs the payload of `ChartGeodesicInitialVelocitySmoothDependence` (`GaussLemmaRadial.lean`, defined BEFORE the flow derivative existed). SINCE THEN, the smooth-dependence CORE was PROVEN: `chartChristoffel_initialVelocity_hasDerivAt_of_uniform_geodesicFlow` (`GeodesicFlowDerivative.lean` — the flow derivative in initial velocity = the linearized solution `Ψ = (J, K)`), with the linearized system (`GeodesicLinearized.lean`), uniform remainders (`GeodesicDerivative.lean`), and Lipschitz dependence (`GeodesicDependence.lean`). The interface's remaining payload per `harness/reports/M5-geo-16_done.md`: fixed-time s-derivatives (= the flow derivative — PROVEN) and the MIXED-DERIVATIVE COMMUTATION `∂ₜ(∂ₛ γ) = ∂ₛ(∂ₜ γ)` (= the linearized system's defining equations: `∂ₜ Ψ = (K, …)` IS the mixed derivative statement, since `Ψ = ∂ₛ γ` by the flow derivative and `Ψ` solves the linearized ODE whose first component says `J' = K` — check the exact interface fields and map each to the proven facts).

Deliverables, in a NEW file `Poincare/Global/SmoothDependenceDischarge.lean` (do NOT edit any existing file, incl. `Poincare.lean`):
1. THE PAYLOAD MAP: each field of `ChartGeodesicInitialVelocitySmoothDependence` (or the de-facto payload the Gauss/assembly consumers need — read `GaussLemmaRadial.lean`/`GaussLemmaTransverse.lean`/rigid-17's report) discharged from the proven machinery; the interface instance/discharge theorem.
2. If reachable: the endpoint Jacobi-pairing assembly (the integrated transverse Gauss now unconditional via the discharged payload — `GaussLemmaTransverse.lean`'s conditional identity + `GaussLemmaIntegrated.lean`) → the weight identity the source expansion needs; else isolate.
3. Report `harness/reports/M5-rigid-18_{done|blocked}.md`.

No vacuous wrappers. Verify: `lake build Poincare.Global.SmoothDependenceDischarge` and report the actual result. Commit your work.
