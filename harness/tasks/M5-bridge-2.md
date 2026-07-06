Read harness/worker_contract.md first and obey it strictly.

# Task M5-bridge-2: GOAL 9 — the packaging step of the curvature bridge

Context: `harness/reports/M5-bridge-1_blocked.md` — after M5-bridge-1's lemmas (`Poincare/Global/ChartCurvatureBridge.lean`: `fderiv_clm_family_apply`, `chartCurvatureOf_eq_fderiv_apply`, `eventually_christoffelOneForm_symm`, slot-convention rewrite), the remaining obstruction to the chart↔manifold curvature bridge is EXPLICITLY PACKAGING, not algebra: expressing the dependent tangent-space model connection as the plain `E → E →L[ℝ] E →L[ℝ] E` family that `chartCurvatureOf` consumes, with `extend` fields anchored at the same model point.

READ THE BLOCKED REPORT FIRST and choose the packaging that closes. Strong hint: `GeodesicTransport.chartChristoffelField g x₀ : E → E →L[ℝ] E →L[ℝ] E` IS already a plain family (built from `christoffelOneForm` of the blended chart metric) — state and prove the bridge AGAINST IT rather than against a dependent model connection: the manifold `curvatureOp g.leviCivita` on `extend` fields at `x₀`, read through the chart identification (`inTangentCoordinates` / the constant model identification `TangentSpace 𝓘(ℝ,E) z = E`), equals `chartCurvatureOf (chartChristoffelField g x₀)` at `extChartAt I x₀ x₀` on the corresponding model vectors. The eventual-agreement bridge (`chartLeviCivita_eventuallyEq_closed`), the cutoff-1 coefficient lemmas (`GeodesicReanchor.lean`, `RoundSphereCurvature.lean`), and curvature germ-locality (`constSMul_curvatureOp_extend_apply`'s technique in `MetricRescale.lean:226`) are the assembled toolkit.

Deliverables, in a NEW file `Poincare/Global/ChartCurvatureBridge2.lean` (do NOT edit any existing file, incl. `Poincare.lean`):
1. The packaging lemma(s) — whatever plain-family reformulation closes the gap.
2. THE BRIDGE: manifold `curvatureOp` on `extend` fields at the anchor = `chartCurvatureOf (chartChristoffelField g x₀)` at the anchor image (identification spelling documented). Any closed `g`, general `n` preferred.
3. If it closes cheaply, add the sphere assembly: `HasConstantSectionalCurvature3 roundSphereMetric3 1` via `roundSphereMetric3_chartChristoffelField_anchor_eq_sphereChristoffel` + `conformalChartMetric_chartCurvatureOf_sphereChristoffel` + `roundSphereMetric3_inner_chartAt_symm_eq` (from `RoundSphereCurvature.lean` / `ConformalCurvature.lean` / `RoundSphereChartMetric.lean`); else isolate its final glue.
4. Report `harness/reports/M5-bridge-2_{done|blocked}.md`.

No vacuous wrappers; hypotheses used or removed. Verify: `lake build Poincare.Global.ChartCurvatureBridge2` and report the actual result. Commit your work.
