Read harness/worker_contract.md first and obey it strictly.

# Task M5-rigid-36: ONE THEOREM — the strict derivative at nonzero endpoints

Context: `harness/reports/M5-rigid-35_blocked.md` (READ FIRST). THE SINGLE MISSING SURFACE: on a positive shrunk ball, the fixed-time exponential chart (`GeodesicTransport.expAtChartOpenPartialHomeomorph`) has a strict Fréchet derivative at every NONZERO `v` (currently only `expAt_chart_hasStrictFDerivAt_zero`, `ExponentialLocalHomeo.lean`). THE TEMPLATE: that zero theorem's proof — the two-variable uniform remainder (`ExponentialFrechet.lean` + `GeodesicDerivative.lean`'s compact-tube uniform Taylor remainders + Lipschitz dependence `GeodesicDependence.lean`) — REPLAY IT AT `v`: the flow derivative in initial velocity exists at every initial pair in the uniform ball (`chartChristoffel_initialVelocity_hasDerivAt_of_uniform_geodesicFlow`, `GeodesicFlowDerivative.lean` — check its basepoint generality; it was proven for the uniform flow at any hosted initial data); the two-variable strictness upgrade is the SAME Heine–Cantor/equicontinuity argument centered at `v` instead of `0`. The derivative VALUE at `v`: the linearized solution map `w ↦ Ψ_w(T)`-shaped (do NOT force a scale decomposition here — that's the NEXT task; the raw strict derivative with its linearized-flow value is THE deliverable).

Deliverables, in a NEW file `Poincare/Global/ExponentialStrictAt.lean` (do NOT edit any existing file, incl. `Poincare.lean`):
1. 🎯 `expAt_chart_hasStrictFDerivAt`-shaped: strict Fréchet derivative at every `v` in a positive shrunk ball, with the linearized-flow derivative value.
2. Report `harness/reports/M5-rigid-36_{done|blocked}.md`; if blocked, ONE estimate isolated.

No vacuous wrappers. Verify: `lake build Poincare.Global.ExponentialStrictAt` and report the actual result. Commit your work.
