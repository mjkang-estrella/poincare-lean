# Worker contract

You are a Lean 4 formalization worker on the Poincaré project (toolchain leanprover/lean4:v4.30.0-rc2,
Mathlib pinned). Isolated worktree on branch `worker/uniform-nonzero-metric-pullback`, cloned `.lake` cache.
Rules: NO sorry/admit/axiom/native_decide; do not edit existing Lean files or `Poincare.lean`; exactly one new
file `Poincare/Global/FixedChartUniformJacobiComparison.lean`; no vacuous definitions; report actual command
output; commit each verified lemma on the branch; report to
`harness/reports/uniform-nonzero-metric-pullback_{done|blocked}.md`. Stop conditions as in
`harness/tasks/M5-glob-69.md` (proved, or the strongest verified partial plus ONE exact resisting `def` and a
`target_of_<resisting>` theorem; never weaken the quantifier order: one radius before all moving parameters).

# Task: the uniform nonzero metric pullback (uniform Jacobi comparison on a fixed-chart patch)

This is the isolated analytic core of the unit-recognition route. Read first:
`harness/reports/uniform-differential-pullback_blocked.md` (sections "Verified progress", "One exact resisting
definition", and everything after), then `Poincare/Global/FixedChartUniformDifferentialPullback.lean`
(`exists_uniform_differential_radius`, `metric_pullback_zero`, `UniformNonzeroMetricPullback`,
`uniformDifferentialPullback_of_uniformNonzeroMetricPullback`, `target_of_uniformNonzeroMetricPullback`), the
per-anchor proof it must be made uniform: `RigidityComplete.cartanMap_isLocalIsometry_of_selector_aop_bound`
and `cartanMap_isLocalIsometry` (`Poincare/Global/RigidityComplete.lean`) with their inputs
(`EnrichedCascade.BaseCurvePackage`, `LinearizedFamilyPackage`, the Jacobi/Gauss-lemma and curvature-1
comparison modules they import — follow the import graph and read the statements you will reuse), and the
patch machinery (`FixedChartUniformSourceNormal.Patch`: retained flow `α`, time `T`, `endpoint`,
`normal`; `GeodesicFlowJointDerivative.exists_flow_initialState_C1`: the fundamental solution `Φ`, which is
the family of Jacobi fields along every patch geodesic, jointly continuous in the initial state).

Target (frozen): prove

```lean
theorem uniformNonzeroMetricPullback (g : ClosedSmoothRiemannianMetric 3 M) :
    FixedChartUniformDifferentialPullback.UniformNonzeroMetricPullback g
```

with the definition used verbatim from the landed module, in that module's instance context. Then restate and
prove, in your file, the two consequences already reduced to it there:
`uniformDifferentialPullback_of_constantCurvature` (the task-8 remainder, via
`uniformDifferentialPullback_of_uniformNonzeroMetricPullback`) and `exists_radius` (the frozen task-8 target, via
`target_of_uniformNonzeroMetricPullback`).

Mathematics. For a geodesic `γ(t) = (α (c, v) t).1` of the source patch starting at `c = extChartAt I x₀ x` with
velocity `v`, and the corresponding sphere geodesic starting at `D`'s anchor image with velocity `l v`, the
derivative of the exponential at `v` applied to `a` is the Jacobi field `J_a(T)` with `J_a(0) = 0`,
`J_a'(0) = a`, given by the position component of `Φ (c, v) T (0, a)`. For curvature 1 on both sides, the Jacobi
equation in a parallel frame is `J'' + J = 0` for the component orthogonal to `γ'` and `J'' = 0` along `γ'`, so
`g(J_a(t), J_b(t))` is determined by `g(a, b)`, `g(a, γ'(0))`, `g(b, γ'(0))`, and `|γ'(0)|` alone; since the
alignment `l` preserves the anchor metric, the two sides agree. The per-anchor proof in `RigidityComplete`
does exactly this computation for the anchor-centered flow; here the flow starts at the moving position `c`
inside the fixed chart `x₀`, so the parallel-frame/Jacobi identities must be established for the fixed-chart
Christoffel field along geodesics with moving initial position, with all constants coming from the patch
(uniform `T`, uniform velocity balls, joint continuity of `Φ`) and compactness of `K × H`.

Order of work (commit each): (1) identify `fderiv ℝ (sourceExp Q x) v a` with the position component of the
fundamental solution (`Φ (c, v) T (0, a)`) using `geodesic_flow_hasFDerivAt_initialState` and the time
rescaling; same for the target; (2) the Jacobi inner-product identity along a single patch geodesic for the
fixed-chart Christoffel field under `HasConstantSectionalCurvature3 g 1` (reuse the per-anchor machinery's
curvature-1 comparison lemmas by re-instantiating them on the fixed-chart flow with moving initial position;
state precisely which lemma needs moving initial position and prove it); (3) the same on the sphere patch;
(4) equality of the two inner products via `linear_metric`/`FixedChartLocalSuccessorExistence.linear_metric`
and the alignment law; (5) uniformity: every radius above is chosen from the patch data and compactness
before `x, p, L, z`; assemble the frozen theorem and the two consequences.
If step (2) resists, deliver (1) and the exact resisting `def` (the Jacobi identity with moving initial
position) with `target_of_<resisting>`.
