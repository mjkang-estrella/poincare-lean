Read harness/worker_contract.md first and obey it strictly.

# Task M5-model-6: GOAL 9 — curvature of the conformal chart metric (the sphere constant)

Context: `Poincare/Global/ConformalChristoffel.lean` (report `harness/reports/M5-model-5_done.md`) proved the chart Christoffel formula for conformally flat metric data (`christoffelOneForm_conformalFlatMetric_apply`, slot conventions documented in the report — READ IT FIRST) plus the sphere factor's derivative (`fderiv_stereoInvFunAuxConformalFactor`, factor `f z = 16/(‖z‖²+4)²` from `Poincare/Global/RoundSphereChart.lean`). `Poincare/Global/RoundSphereChartMetric.lean` ties this factor to `roundSphereMetric3`'s chart coefficients.

Goal: the CHART-LEVEL curvature computation showing the sphere factor has constant sectional curvature 1.

Deliverables, in a NEW file `Poincare/Global/ConformalCurvature.lean` (do NOT edit any existing file, incl. `Poincare.lean`):

1. CHART CURVATURE OPERATOR from a Christoffel field: `def chartCurvatureOf (Γ : E → E →L[ℝ] E →L[ℝ] E) (z : E) (u v w : E) : E := (fderiv ℝ Γ z u) v w − (fderiv ℝ Γ z v) u w + Γ z u (Γ z v w) − Γ z v (Γ z u w)` — FIRST check whether the repo already has a chart/model curvature-from-Christoffel definition (`Poincare/RiemannCurvatureOperator.lean`, `Poincare/ModelChristoffel.lean`, `Poincare/Global/LeviCivitaTransport.lean` — if one exists with fixed conventions, REUSE it and adapt; document which). Slot/sign conventions must match the repo's `CovariantDerivative.curvatureOp` orientation — derive on paper, document.
2. CONFORMAL CURVATURE FORMULA: for the conformal Christoffel field of a positive `C²` factor `f`, compute `chartCurvatureOf` in closed form (the classical conformal curvature: Hessian/gradient terms of `log f` in Kulkarni–Nomizu arrangement). You may specialize immediately to the concrete sphere factor if the general formula fights the API — the frozen goal is deliverable 3.
3. THE SPHERE CONSTANT: for `f z = 16/(‖z‖²+4)²` (i.e. `stereoInvFunAuxConformalFactor`), prove the constant-curvature identity in the chart: `⟪chartCurvatureOf Γf z u v w, a⟫`-form equals `-(1/2) * (KN of the conformal metric)`-form matching the repo's `HasConstantSectionalCurvature3` convention with κ = 1 (see `tensorKulkarniNomizuAt` usage in `Poincare/Global/ScalarVariation.lean:22318` and `SphereTheorem.lean:273` for the exact target shape; the CHART-LEVEL analogue with `G z = f z • ⟪·,·⟫` is the frozen deliverable — the manifold transport is the NEXT task, not this one). If the derived constant differs from 1, prove the derived one and DOCUMENT the derivation (sanctioned correction) — but derive carefully first: Mathlib's `stereoInvFunAux` parametrizes the UNIT sphere, so κ = 1 is expected.
4. Report `harness/reports/M5-model-6_{done|blocked}.md`: conventions, derivation, final signatures, and the manifold-transport roadmap (chart curvature ↔ `curvatureOp` of `roundSphereMetric3` via the transported connection bridges).

No vacuous wrappers; hypotheses used or removed. Verify: `lake build Poincare.Global.ConformalCurvature` and report the actual result. Commit your work.
