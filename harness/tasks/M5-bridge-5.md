Read harness/worker_contract.md first and obey it strictly.

# Task M5-bridge-5: GOAL 9 — the outer glue: assemble the curvature bridge and the sphere witness

Context: FOUR gated iterations (ChartCurvatureBridge/2/3/4) have proven every named ingredient of the chart↔manifold curvature bridge; `harness/reports/M5-bridge-4_blocked.md` (READ FIRST) reduces what remains to GENERIC OUTER TRANSPORT/LOCALITY GLUE and gives the four-bullet combination plan verbatim:
- `ChartCurvatureBridge4.chartTransportedLeviCivitaSection_inner_extend_eventuallyEq` for the `w`/`u` inner fields;
- `ChartCurvatureBridge3.chartTransportedLeviCivitaHom_extend_eventuallyEq_closed` applied to `extend` directions (transported hom → `g.leviCivita` hom);
- `CovariantDerivative.congr_of_eventuallyEq` for the two outer connection terms;
- `mlieBracket_extend_extend_eventually_eq_zero` for the canonical bracket term.
Template for the whole term-by-term assembly: the proof of `constSMul_curvatureOp_extend_apply` (`Poincare/Global/MetricRescale.lean:226`). Packaging half already proven: `ChartCurvatureBridge2.chartCurvatureOf_chartChristoffelField_eq_chartLeviCivita_curvature`.

Deliverables, in a NEW file `Poincare/Global/ChartCurvatureBridge5.lean` (do NOT edit any existing file, incl. `Poincare.lean`):
1. THE ASSEMBLED LINK: `curvatureOp (GeodesicTransport.chartLeviCivita g x₀)` on model `extend` fields at the anchor image = (chart identification of) `curvatureOp g.leviCivita (extend E u) (extend E w) (extend E a) x₀` — by the four-bullet plan.
2. THE FULL BRIDGE: composition with the ChartCurvatureBridge2 theorem.
3. THE SPHERE WITNESS: `theorem roundSphereMetric3_hasConstantSectionalCurvature_one : HasConstantSectionalCurvature3 roundSphereMetric3 1` — assembling with `roundSphereMetric3_chartChristoffelField_anchor_eq_sphereChristoffel`, `conformalChartMetric_chartCurvatureOf_sphereChristoffel`, `roundSphereMetric3_inner_chartAt_symm_eq` (see `RoundSphereCurvature.lean` / `ConformalCurvature.lean` / `RoundSphereChartMetric.lean`). If (3) needs one more small identification (e.g. tensorKulkarniNomizuAt vs chartTensorKulkarniNomizu through the chart), prove it here.
4. Report `harness/reports/M5-bridge-5_{done|blocked}.md`; if anything remains, isolate it to ONE statement.

No vacuous wrappers; hypotheses used or removed. Verify: `lake build Poincare.Global.ChartCurvatureBridge5` and report the actual result. Commit your work.
