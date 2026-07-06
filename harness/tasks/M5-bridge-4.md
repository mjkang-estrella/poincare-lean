Read harness/worker_contract.md first and obey it strictly.

# Task M5-bridge-4: GOAL 9 — inner-field naturality, then assemble the curvature bridge

Context: the bridge chain (ChartCurvatureBridge/2/3) has reduced the chart↔manifold curvature transport to ONE missing eventual-equality: transporting the INNER covariant-derivative field through the anchor chart (exact statement: `harness/reports/M5-bridge-3_blocked.md` — READ IT FIRST; the shape is an `eventuallyEq` between the model-side connection applied to the model `FiberBundle.extend` field and the chart-read of the M-side covariant derivative of the corresponding `extend` field, anchored at `extChartAt I x₀ x₀`). Already proven in `Poincare/Global/ChartCurvatureBridge3.lean` (namespace `Poincare.ChartCurvatureBridge3`): `chartTransportedLeviCivitaSection_extend_eventuallyEq_const` and `chartTransportedLeviCivitaHom_extend_eventuallyEq_closed`. The report states the assembly plan verbatim: with the inner-field naturality for `w` and `u`, apply the `constSMul_curvatureOp_extend_apply` term-by-term pattern (`Poincare/Global/MetricRescale.lean:226`): connection `congr_of_eventuallyEq` for the two outer terms, the new hom germ for the bracket term, `mlieBracket_extend_extend_eventually_eq_zero` for the canonical first-slot fields.

Deliverables, in a NEW file `Poincare/Global/ChartCurvatureBridge4.lean` (do NOT edit any existing file, incl. `Poincare.lean`):
1. THE INNER-FIELD NATURALITY lemma exactly as isolated in the report (adapt only spelling).
2. THE ASSEMBLED LINK: `curvatureOp (GeodesicTransport.chartLeviCivita g x₀)` on model `extend` fields at the anchor image = (chart identification of) `curvatureOp g.leviCivita (extend E u) (extend E w) (extend E a) x₀`, via the term-by-term plan.
3. THE FULL BRIDGE: compose with `ChartCurvatureBridge2.chartCurvatureOf_chartChristoffelField_eq_chartLeviCivita_curvature` into `chartCurvatureOf (chartChristoffelField g x₀) … = (identification of) curvatureOp g.leviCivita …`.
4. THE SPHERE WITNESS if it now closes: `HasConstantSectionalCurvature3 roundSphereMetric3 1` (pieces: `roundSphereMetric3_chartChristoffelField_anchor_eq_sphereChristoffel`, `conformalChartMetric_chartCurvatureOf_sphereChristoffel`, `roundSphereMetric3_inner_chartAt_symm_eq`); else isolate its final glue precisely.
5. Report `harness/reports/M5-bridge-4_{done|blocked}.md`.

No vacuous wrappers; hypotheses used or removed. Verify: `lake build Poincare.Global.ChartCurvatureBridge4` and report the actual result. Commit your work.
