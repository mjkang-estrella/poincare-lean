Read harness/worker_contract.md first and obey it strictly.

# Task M5-model-5: GOAL 9 — conformal chart Christoffel formula

Context: `roundSphereMetric3`'s chart coefficients are now the conformal form `stereoInvFunAuxConformalFactor * ⟪·,·⟫` (`Poincare/Global/RoundSphereChartMetric.lean`, factor `16/(‖z‖²+4)²` from `Poincare/Global/RoundSphereChart.lean`). The curvature computation needs the chart Christoffel symbols of a CONFORMALLY FLAT chart metric. The repo's chart-side Christoffel machinery: `CovariantDerivative.christoffelOneForm` + `chartBilin` + nondegeneracy (consumed in `Poincare/Global/GeodesicTransport.lean:150` — read that call site for the exact API), model-space regularity in `Poincare/ModelChristoffel.lean`.

Deliverables, in a NEW file `Poincare/Global/ConformalChristoffel.lean` (do NOT edit existing files, incl. `Poincare.lean`):
1. THE CLASSICAL CONFORMAL FORMULA at the model-space level: for chart metric data `G : E → E →L[ℝ] E →L[ℝ] ℝ` of the form `G z = f z • innerSL ℝ` (or the repo's preferred encoding) with `f : E → ℝ` positive and differentiable at `z`, compute `christoffelOneForm G … z` (against the appropriate bilinear/nondegeneracy data) in closed form: the classical `Γ(u,v) = (u(f)/2f) v + (v(f)/2f) u − (⟪u,v⟫/2f) ∇f`-shaped identity, adapted to the repo's exact `christoffelOneForm` convention and slot order (FIRST inspect the definition and document the convention; derive the formula on paper against it before proving; a slot/sign refutation with derivation is a sanctioned-correction outcome). `E` may be a general finite-dimensional real inner-product space or `ClosedSmoothModel n` — choose what the machinery supports.
2. SPECIALIZATION HOOK: instantiate `f z := 16 / (‖z‖² + 4)²` (i.e. `stereoInvFunAuxConformalFactor`) far enough to have the derivative data ready (e.g. `fderiv` of `f` computed as a named lemma). Full curvature is NOT in scope.
3. Report `harness/reports/M5-model-5_{done|blocked}.md`: the convention notes, final signatures, and the remaining curvature-computation roadmap.

Verify: `lake build Poincare.Global.ConformalChristoffel` and report the actual result. Commit your work.
