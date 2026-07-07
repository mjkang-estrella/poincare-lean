Read harness/worker_contract.md first and obey it strictly.

# Task M5-rigid-39: the shifted Grönwall propagation — the strict derivative closes

Context: `harness/reports/M5-rigid-38_blocked.md` (READ FIRST). PROVEN: the shifted-base two-point Taylor estimate + chart-Christoffel and roundSphere closed-ball instances (`ExponentialStrictAtV.lean`), the CLM candidate (`LinearizedCLM.lean`). THE LAST PIECE: the endpoint two-variable Grönwall propagation into the shifted `linearizedEndpointCLM` — the ABSTRACT layer already exists: `GeodesicDerivativeFinal.lean` (`initialVelocity_hasDerivAt_of_gronwall_residual_bound`, the residual comparison, the uniform little-o spelling — CHECK whether these are base-agnostic; they were abstract residual statements, so instantiate at base `v`) and `GeodesicFlowDerivative.lean`'s instantiation pattern (the residual hypotheses discharged at base 0 — REPLAY at base `v` with rigid-38's shifted Taylor estimates as the driving bounds). Then the two-variable/strict upgrade mirrors `ExponentialFrechet/ExponentialLocalHomeo.lean`'s zero-anchored path — replay at `v`. Output: `HasStrictFDerivAt (expAtChartOpenPartialHomeomorph …) (linearizedEndpointCLM …) v` for `v` in the shrunk ball, BOTH metrics.

Deliverables in a NEW file `Poincare/Global/ExponentialStrictClose.lean` (do NOT edit existing files, incl. `Poincare.lean`): the propagation + 🎯 the strict derivative at every shrunk-ball `v` (both metrics). Strict-partial; ONE isolated statement max. Report `harness/reports/M5-rigid-39_{done|blocked}.md`.

No vacuous wrappers. Verify: `lake build Poincare.Global.ExponentialStrictClose` and report the actual result. Commit your work.
