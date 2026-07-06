Read harness/worker_contract.md first and obey it strictly.

# Task M5-model-8: GOAL 9 — ASSEMBLE THE SPHERE WITNESS

THE CURVATURE BRIDGE IS COMPLETE: `ChartCurvatureBridge6.chartCurvatureOf_chartChristoffelField_eq_chartTransported_curvatureOp` (+ `chartLeviCivita_curvatureOp_extend_eq_chartTransported_curvatureOp`, `Poincare/Global/ChartCurvatureBridge6.lean`). `harness/reports/M5-bridge-6_done.md` (READ FIRST) names the EXACT two remaining glue pieces for the sphere witness:
1. Curvature congruence `chartCurvatureOf (chartChristoffelField roundSphereMetric3 x₀) = chartCurvatureOf sphereChristoffel` near the anchor (from `roundSphereMetric3_chartChristoffelField_anchor_eq_sphereChristoffel` / its `eventuallyEq` form in `RoundSphereCurvature.lean` — chart curvature is germ-local in the Christoffel field: `fderiv` congruence + pointwise terms).
2. The lowered chart/global algebra bridge `roundSphereMetric3_inner_chartTransported_curvature_eq_chartMetric` combining (per the report): the bridge theorem, `CovariantDerivative.chartMetric_chartTransportedLeviCivitaSection`, `chartTransportedLeviCivitaSection_extend_apply_chart`, `roundSphereMetric3_chartMetric_eq`, and the definitional comparison `tensorKulkarniNomizuAt` vs `chartTensorKulkarniNomizu` at the anchor image.

Then compose with `conformalChartMetric_chartCurvatureOf_sphereChristoffel` (`ConformalCurvature.lean`, the κ=1 identity) to prove, in a NEW file `Poincare/Global/RoundSphereWitness.lean` (do NOT edit any existing file, incl. `Poincare.lean`):

`theorem roundSphereMetric3_hasConstantSectionalCurvature_one : HasConstantSectionalCurvature3 roundSphereMetric3 1`

If it closes cheaply, add the corollaries: `∀ x, roundSphereMetric3.IsEinsteinAt 2 x`-shaped statement IF the constant-curvature→Einstein direction is available or short (check `RicciNorm.lean`/`ScalarVariation.lean`; do NOT force it — the witness theorem is the frozen deliverable), and `PositiveEinsteinMetric3 RoundSphere3` (`EinsteinInterface.lean`) if the Einstein step lands. Report `harness/reports/M5-model-8_{done|blocked}.md`; if blocked, ONE isolated statement.

No vacuous wrappers. Verify: `lake build Poincare.Global.RoundSphereWitness` and report the actual result. Commit your work.
