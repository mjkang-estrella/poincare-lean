Read harness/worker_contract.md first and obey it strictly.

# Task M5-vol-1: GOAL 9 — Riemannian volume: scoping + first construction

Context: the normalized Ricci flow (∂ₜg = −2Ric + (2/3)·r̄·g, r̄ = mean scalar curvature), Perelman functionals, and every volume argument need INTEGRATION over closed manifolds against the Riemannian volume measure. Neither the repo's `Global/` layer nor (as of the last survey) core Mathlib had manifold integration — RE-VERIFY against the pinned Mathlib first.

Deliverables:
1. REPORT-FIRST `harness/reports/M5-vol-1_assets.md`: inventory the pinned Mathlib for: measures on manifolds (search `MeasureTheory` + `Manifold`, `hausdorffMeasure`, smooth measures/densities, `Mathlib/Geometry/Manifold/Measure*`, `MeasureTheory.Measure.hausdorff`), integration of functions on charted spaces, partitions of unity for gluing measures (`Mathlib/Geometry/Manifold/PartitionOfUnity.lean` EXISTS — assess), determinant/`abs det` machinery for the volume density `sqrt (det G)` in charts. Honest verdict per ingredient + a 3-5 task construction roadmap for `volumeMeasure (g : ClosedSmoothRiemannianMetric n M) : MeasureTheory.Measure M`.
2. FIRST CONSTRUCTION, in a NEW file `Poincare/Global/VolumeDensity.lean` (do NOT edit existing files, incl. `Poincare.lean`): the CHART-LEVEL volume density — `def chartVolumeDensity (G : E → E →L[ℝ] E →L[ℝ] ℝ) (z : E) : ℝ := Real.sqrt |(LinearMap.toMatrix … (bilinear-to-endomorphism of G z)).det|`-shaped (spelling free; semantics: `sqrt |det|` of the metric coefficient matrix in an orthonormal basis), with proven: positivity for positive-definite `G z`; the conformal specialization `chartVolumeDensity (f z • innerSL) = (f z)^(n/2)`-shaped for `f z > 0` (careful with `n/2` on ℝ — use `(f z) ^ (n : ℝ) / …` rpow or the squared form `density² = (f z)^n` if cleaner — document); continuity/smoothness in `z` for continuous/smooth `G` IF the machinery cooperates (else isolate).
3. If Mathlib already HAS a usable manifold measure route (e.g. Hausdorff measure of the induced metric space!), say so prominently in the report — the induced `MetricSpace` from `RiemannianContext.lean` + Hausdorff measure may be the shortcut; assess its usability for integration of scalar curvature.
4. Report `harness/reports/M5-vol-1_{done|blocked}.md` may be merged into the assets file; include the roadmap.

Verify: `lake build Poincare.Global.VolumeDensity` and report the actual result. Commit your work.
