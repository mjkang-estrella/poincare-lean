Read harness/worker_contract.md first and obey it strictly.

# Task M1-riemannian-context: standard Riemannian context wrapper

Per the gap survey (harness/reports/mathlib_gaps.md §2-4), pinned Mathlib has: `ContMDiffRiemannianMetric`, `IsContMDiffRiemannianBundle`, `RiemannianBundle`, `IsRiemannianManifold`, `EMetricSpace.ofRiemannianMetric` (Geometry/Manifold/{VectorBundle/Riemannian,Riemannian/Basic,Riemannian/PathELength}.lean), plus `CovariantDerivative` with torsion (VectorBundle/CovariantDerivative/).

Deliverable: NEW file `Poincare/Global/RiemannianContext.lean` (+ import in `Poincare.lean`) providing the project's standard working context for tier M1:

1. A variable-section template (documented) for "closed smooth Riemannian n-manifold": `[TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M] [CompactSpace M] [ConnectedSpace M]` + a `ContMDiffRiemannianMetric`-based metric. Investigate the exact instance chain Mathlib needs to get from a `ContMDiffRiemannianMetric` on the tangent bundle to `IsRiemannianManifold` / the induced `EMetricSpace`, and package it as defs/instances/lemmas so downstream files can assume ONE clean context.
2. Prove 3-8 small genuine plumbing lemmas that downstream work will need, e.g.: the metric's inner product is smooth (`ContMDiff.inner_bundle` specialization); symmetry/positivity access lemmas; compactness consequences that come free (e.g. the induced emetric is finite / the space is a metric space — only if genuinely reachable from current Mathlib API; do NOT force it, blocked-report any wall you hit).
3. NO new axioms, no Prop-field certificate structures, every instance genuinely derived.

This is instance plumbing — the value is a clean, honest foundation, not depth. Keep it under ~200 lines. Build `lake build Poincare.Global.RiemannianContext`, verify, commit. Report final declaration names.
