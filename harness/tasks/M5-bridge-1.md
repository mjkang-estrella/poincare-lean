Read harness/worker_contract.md first and obey it strictly.

# Task M5-bridge-1: GOAL 9 — the chart↔manifold curvature bridge at the anchor

Context: `harness/reports/M5-model-7_blocked.md` isolates THE bridge blocking the sphere witness (and, in sibling form, the parked geodesic re-anchoring): for `g : ClosedSmoothRiemannianMetric n M` and anchor `x : M`,

```
chart curvature of (GeodesicTransport.chartLeviCivita g x) at extChartAt I x x, on constant model vectors
  =  (mfderiv/chart identification of) CovariantDerivative.curvatureOp g.leviCivita (extend E u) (extend E w) (extend E a) x
```

(exact identification spelling free; semantics frozen: the manifold curvature on canonical `extend` fields at the anchor is computed by the chart curvature `chartCurvatureOf` (`Poincare/Global/ConformalCurvature.lean`) of the transported Christoffel field (`chartChristoffelField`, `Poincare/Global/GeodesicTransport.lean`) at the anchor image).

Assets to mine (reuse-first): `christoffelOneForm_congr_of_eventuallyEq` (just landed, `Poincare/Global/RoundSphereCurvature.lean`) and that file's cutoff-1 coefficient lemmas; the curvature germ-locality technique of `constSMul_curvatureOp_extend_apply` (`Poincare/Global/MetricRescale.lean:226` — curvature at `x` depends only on the connection germ; `congr_of_eventuallyEq` + `exists_mdifferentiableOn_extend`); the eventual-agreement bridge `chartLeviCivita_eventuallyEq_closed` (`GeodesicTransport.lean`) tying the transported connection to `g.leviCivita` near the anchor; the transport/uniqueness machinery of `Poincare/Global/LeviCivitaTransport.lean` (how `chartTransportedLeviCivitaHom` is DEFINED from the chart connection — the bridge may be mostly definitional there + chain rule); `extend`-field chart representation lemmas (the extend fields are chart-constant near their anchor — `mlieBracket_extend_extend_eventually_eq_zero`-adjacent machinery, `Poincare/Global/BumpExtend.lean`).

Deliverables, in a NEW file `Poincare/Global/ChartCurvatureBridge.lean` (do NOT edit any existing file, incl. `Poincare.lean`):
1. THE BRIDGE, at whatever generality closes (any closed `g`, general `n` preferred; the identification through `inTangentCoordinates`/`mfderivWithin` of the chart is yours to spell — document precisely).
2. Whatever intermediate germ-locality/representation lemmas it needs (standalone, reusable).
3. Report `harness/reports/M5-bridge-1_{done|blocked}.md`: final statement, and (if done) the two-line assembly plan for `HasConstantSectionalCurvature3 roundSphereMetric3 1` via `roundSphereMetric3_chartChristoffelField_anchor_eq_sphereChristoffel` + `conformalChartMetric_chartCurvatureOf_sphereChristoffel` + `roundSphereMetric3_inner_chartAt_symm_eq`. Strict-partial with the sharpest sub-lemma isolated remains valid.

No vacuous wrappers; hypotheses used or removed. Verify: `lake build Poincare.Global.ChartCurvatureBridge` and report the actual result. Commit your work.
