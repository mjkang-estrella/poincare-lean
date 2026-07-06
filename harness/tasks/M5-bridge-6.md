Read harness/worker_contract.md first and obey it strictly.

# Task M5-bridge-6: GOAL 9 — ONE theorem: `chartLeviCivita_curvatureOp_extend_eq_chartTransported_curvatureOp`

Everything else is proven. `harness/reports/M5-bridge-5_blocked.md` (READ FIRST) states the SINGLE remaining theorem verbatim — model-side `curvatureOp (GeodesicTransport.chartLeviCivita g x₀)` on model `FiberBundle.extend` fields at `extChartAt I x₀ x₀` equals `CovariantDerivative.chartTransportedLeviCivitaSection x₀` applied to the M-side `curvatureOp g.leviCivita` on `extend` fields.

Proven toolkit (use it; do not re-derive): `ChartCurvatureBridge5` (namespace `Poincare.ChartCurvatureBridge5`): `chartTransportedLeviCivitaSection_congr_of_eventuallyEq{,_at}`, `chartTransportedLeviCivitaHom_congr_of_eventuallyEq`, `chartTransportedLeviCivitaSection_hom_apply_chart` (arbitrary-field hom naturality); `ChartCurvatureBridge4.chartTransportedLeviCivitaSection_inner_extend_eventuallyEq` (+ `_apply_chart`); `ChartCurvatureBridge3.chartTransportedLeviCivitaSection_extend_eventuallyEq_const`, `…Hom_extend_eventuallyEq_closed`; `mlieBracket_extend_extend_eventually_eq_zero`; the term-by-term template `constSMul_curvatureOp_extend_apply` (`MetricRescale.lean:226`). Expand `curvatureOp` on both sides (`curvatureOp_apply`-style unfolding), transport each of the three terms (two outer covariant-derivative terms via the inner-field naturality + hom naturality + locality congr lemmas; the bracket term via extend-bracket vanishing on both sides), and close.

Deliverables, in a NEW file `Poincare/Global/ChartCurvatureBridge6.lean` (do NOT edit any existing file, incl. `Poincare.lean`):
1. THE theorem (statement verbatim from the report; spelling adaptations documented).
2. THE FULL BRIDGE: composition with `ChartCurvatureBridge2.chartCurvatureOf_chartChristoffelField_eq_chartLeviCivita_curvature`.
3. THE SPHERE WITNESS `roundSphereMetric3_hasConstantSectionalCurvature_one : HasConstantSectionalCurvature3 roundSphereMetric3 1` if it closes (pieces in `RoundSphereCurvature.lean` / `ConformalCurvature.lean` / `RoundSphereChartMetric.lean`); else isolate its exact remaining glue.
4. Report `harness/reports/M5-bridge-6_{done|blocked}.md`.

No vacuous wrappers. Verify: `lake build Poincare.Global.ChartCurvatureBridge6` and report the actual result. Commit your work.
