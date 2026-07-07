Read harness/worker_contract.md first and obey it strictly.

# Task M5-rigid-7: the interval oscillator — J = sin t · w along constant-curvature geodesics

Context: every ingredient is proven. (a) The unconditional ZONE constant-curvature identity: `ChartCurvatureBridgeZoneClose.chartCurvatureOf_chartChristoffelField_constantCurvature_one_zone` (`ChartCurvatureBridgeZoneClose.lean` — read its exact statement/hypotheses). (b) The linearized-flow/Jacobi-operator identities + covariant second identities + KN contraction + the sin/cos oscillator with uniqueness (`JacobiConstantCurvature.lean`). (c) The anchor instantiation pattern + lowered contractions (`JacobiInstantiate.lean` — its blocked report described exactly this assembly waiting on the zone identity). (d) Geodesic flow machinery: solutions stay in the cutoff-one zone (`GeodesicLengthFinal.lean` cutoff-one-shrunk flow), Gauss orthogonality (`GaussLemmaIntegrated.lean`), constant speed (`GeodesicSpeed.lean`).

THE TASK: assemble — for `g` with `HasConstantSectionalCurvature3 g 1`, along a unit-speed chart geodesic (cutoff-one-shrunk flow) with transverse initial data (`J(0)=0, J'(0)=w`, `w ⊥ γ'(0)` in the chart metric): the coordinate Jacobi second-derivative theorem + the zone KN identity + Gauss orthogonality propagation give `J'' = −J` on the honest interval, hence `J t = sin t · w` by the proven uniqueness.

Deliverables, in a NEW file `Poincare/Global/JacobiOscillator.lean` (do NOT edit any existing file, incl. `Poincare.lean`):
1. ORTHOGONALITY PROPAGATION: `J(t) ⊥ γ'(t)` along the interval (from the integrated Gauss pairing law with zero initial pairing — `GaussLemmaIntegrated.lean`'s orthogonal case, adapted to the linearized `J`).
2. THE OSCILLATOR ON THE INTERVAL: `J'' = −J` (assembly per above).
3. THE SIN FORMULA: `J t = sin t · w` on the interval (uniqueness wrapper from `JacobiConstantCurvature.lean`).
4. Report `harness/reports/M5-rigid-7_{done|blocked}.md`; if blocked, ONE statement.

No vacuous wrappers. Verify: `lake build Poincare.Global.JacobiOscillator` and report the actual result. Commit your work.
