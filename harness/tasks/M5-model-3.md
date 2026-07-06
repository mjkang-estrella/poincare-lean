Read harness/worker_contract.md first and obey it strictly.

# Task M5-model-3: GOAL 9 — stereographic conformal factor of the round S³ metric

Context: `Poincare/Global/RoundSphereMetric.lean` now has the COMPLETE `roundSphereMetric3 : ClosedSmoothRiemannianMetric 3 RoundSphere3` (pullback of the ambient ℝ⁴ inner product along the inclusion `mfderiv`; defining lemmas `roundSphereMetric3_inner_apply` / `_mfderiv_eq` / `_eq`). Goal of this task: the first CONCRETE coefficient computation — the stereographic conformal-factor formula — as step 1 toward computing this metric's curvature (the eventual Einstein/constant-curvature witness).

Deliverables, in a NEW file `Poincare/Global/RoundSphereChart.lean` (do NOT edit existing files, incl. `Poincare.lean`):

1. AMBIENT PARAMETRIZATION CALCULUS (the core, pure Euclidean): using Mathlib's stereographic machinery for `Metric.sphere (0:E) 1` (`Mathlib/Geometry/Manifold/Instances/Sphere.lean`: `stereographic`, `stereographic'`, `stereoInvFun`, `stereoInvFunAux` with its explicit formula `w ↦ (‖w‖² + 4)⁻¹ • (4 • w + (‖w‖² - 4) • v)`), prove the conformal pullback formula for the parametrization: for the relevant inverse-chart map `ψ` (composed with the inclusion into the ambient `EuclideanSpace ℝ (Fin 4)`, i.e. `stereoInvFunAux v` restricted appropriately), the Fréchet derivative satisfies
   `⟪fderiv ℝ ψ z u, fderiv ℝ ψ z w⟫_ℝ = C z * ⟪u, w⟫`
   for an EXPLICIT rational conformal factor `C z` (expected shape `16 / (‖z‖² + 4)²` for Mathlib's `stereoInvFunAux` normalization — DERIVE the exact constant from the actual formula first; the explicit-rational-function shape is frozen, the constant is sanctioned-adjustable with the derivation documented). Intermediate lemmas for `fderiv ℝ (stereoInvFunAux v) z` are the expected bulk; `u, w` range over the orthogonal complement `(ℝ ∙ v)ᗮ` exactly as in Mathlib's chart setup — state honestly against that domain.
2. TIE-IN (if reachable): connect (1) to `roundSphereMetric3` via `roundSphereMetric3_inner_mfderiv_eq` and the chain rule (`mfderiv` of `(↑) ∘ (chartAt _ x₀).symm` versus `fderiv` of the ambient parametrization): a lemma expressing `roundSphereMetric3.inner ((chartAt (EuclideanSpace ℝ (Fin 3)) x₀).symm z) v w` through `C` and the chart's model identification. If the bundle plumbing exceeds the run, deliver (1) alone — that is a valid strict-partial — and isolate the tie-in as a precisely-stated next lemma.
3. Report `harness/reports/M5-model-3_{done|blocked}.md`: derivation of the constant, final signatures, and the roadmap to the curvature computation (conformal-metric Christoffels in the chart → curvatureOp coefficients → `HasConstantSectionalCurvature3 roundSphereMetric3 1` or the correctly-derived constant).

No vacuous wrappers; hypotheses used or removed. Verify: `lake build Poincare.Global.RoundSphereChart` and report the actual result. Commit your work.
