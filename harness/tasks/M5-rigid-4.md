Read harness/worker_contract.md first and obey it strictly.

# Task M5-rigid-4: instantiate the oscillator along constant-curvature geodesics

Context: `harness/reports/M5-rigid-3_done.md` + the "Remaining boundary" of `Poincare/Global/JacobiConstantCurvature.lean` (READ BOTH FIRST). Proven: the linearized-flow/Jacobi-operator identity, the covariant Jacobi-second identities, the KN contraction seed `R(v,J)v = −J`, the sin/cos oscillator solution + PL uniqueness. MISSING: the manifold instantiation — for `g` with `HasConstantSectionalCurvature3 g 1` and a chart geodesic of `g` (via `chartChristoffelField`), feed the CURVATURE BRIDGE (`ChartCurvatureBridge6.chartCurvatureOf_chartChristoffelField_eq_chartTransported_curvatureOp` + the manifold link, plus the `HasConstantSectionalCurvature3` KN identity transported to chart form — the `RoundSphereCurvature.lean`/`RoundSphereWitness.lean` files show the reverse transport; run it forward) and the Gauss orthogonality (`GaussLemmaIntegrated.lean`) into the covariant second-derivative theorem, concluding: the transverse Jacobi field along a unit-speed chart geodesic of ANY constant-curvature-1 closed metric satisfies the oscillator equation, hence equals `sin t · w` (uniqueness).

Deliverables, in a NEW file `Poincare/Global/JacobiInstantiate.lean` (do NOT edit any existing file, incl. `Poincare.lean`):
1. THE CHART CONSTANT-CURVATURE IDENTITY for `g`: `chartCurvatureOf (chartChristoffelField g x₀)` at the anchor satisfies the KN-form κ=1 identity (from `HasConstantSectionalCurvature3 g 1` + the curvature bridge — the forward transport).
2. THE OSCILLATOR INSTANTIATION: transverse Jacobi fields along unit-speed geodesics of `g` (in the linearized-flow sense of `GeodesicLinearized/GeodesicFlowDerivative`) satisfy `J'' = −J` near the anchor; conclude `J t = sin t · w` on the honest interval.
3. Report `harness/reports/M5-rigid-4_{done|blocked}.md`; strict-partial with ONE isolated statement valid (expected hard core: the covariant-vs-coordinate second derivative bookkeeping away from the anchor point — say exactly where it bites).

No vacuous wrappers. Verify: `lake build Poincare.Global.JacobiInstantiate` and report the actual result. Commit your work.
