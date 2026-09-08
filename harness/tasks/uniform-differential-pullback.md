# Worker contract

You are a Lean 4 formalization worker on the Poincaré project (toolchain leanprover/lean4:v4.30.0-rc2,
Mathlib pinned). Isolated worktree on branch `worker/uniform-differential-pullback`, cloned `.lake` cache.
Rules: NO sorry/admit/axiom/native_decide; do not edit existing Lean files or `Poincare.lean`; exactly one new
file `Poincare/Global/FixedChartUniformDifferentialPullback.lean`; no vacuous definitions; report actual command
output; commit each verified lemma on the branch; report to
`harness/reports/uniform-differential-pullback_{done|blocked}.md`. Stop conditions as in
`harness/tasks/M5-glob-69.md` (proved, or the strongest verified partial plus ONE exact resisting `def` and a
`target_of_<resisting>` theorem).

# Task: the uniform differential pullback on a fixed-chart patch (curvature-only)

Read first: `harness/reports/fixed-chart-local-successor-existence_blocked.md` (the previous worker's exact
remainder; sections "Exact resisting statement" and "Routes examined and why they stop"), then
`Poincare/Global/FixedChartLocalSuccessorExistence.lean` (`UniformDifferentialPullback`,
`exists_uniform_domain_radius`, `exists_onCompact_of_uniformDifferentialPullback`, the host metric comparison and
`linear_metric`), `Poincare/Global/CartanSuppliedDifferentialSuccessor.lean` (`Interpretation`, `patch`,
`sourceExp`, `targetExp`, `linear`, `chartDifferential`), `Poincare/Global/FixedChartUniformSourceNormal.lean`
(`Patch`: the retained flow `α`, time `T`, product inverse `P`, `endpoint`, `normal`, C¹ and strict-derivative
fields), `Poincare/Global/GeodesicFlowJointDerivative.lean` (`exists_flow_initialState_C1`,
`geodesic_flow_hasFDerivAt_initialState`), `Poincare/Global/FixedChartUniformNormalRadius.lean`, and the existing
per-anchor local isometry proof `RigidityComplete.cartanMap_isLocalIsometry` /
`cartanMap_isLocalIsometry_of_selector_aop_bound` (`Poincare/Global/RigidityComplete.lean`, and its inputs
`EnrichedCascade.BaseCurvePackage`, `LinearizedFamilyPackage`, the Jacobi/Gauss-lemma modules it imports).

Target (frozen), in the instance context of `FixedChartLocalSuccessorExistence.lean`:

```lean
theorem uniformDifferentialPullback_of_constantCurvature
    (x₀ : M) (p₀ : RoundSphere3) (U V : Set E)
    (C : FixedChartUniformSourceNormal.Patch g x₀ U)
    (D : FixedChartUniformSourceNormal.Patch roundSphereMetric3 p₀ V)
    (hcurv : HasConstantSectionalCurvature3 g 1)
    (hU : U ⊆ IsometryInstantiate.cutoffOneLocus x₀)
    (hV : V ⊆ IsometryInstantiate.cutoffOneLocus p₀)
    (K : Set M) (H : Set RoundSphere3) (hK : IsCompact K) (hKC : K ⊆ C.anchors)
    (hH : IsCompact H) (hHD : H ⊆ D.anchors) :
    FixedChartLocalSuccessorExistence.UniformDifferentialPullback
      (CartanSuppliedDifferentialSuccessor.patch C D) K H
```

(this is exactly the previous worker's `resisting_spec`; use its exact definition of
`UniformDifferentialPullback`). Consequently, via `exists_onCompact_of_uniformDifferentialPullback`, the frozen
task-8 target `FixedChartLocalSuccessorExistence.exists_radius` follows; state and prove it as the final theorem
`exists_radius` in your file (copy its exact statement from the task-8 specification in
`harness/reports/parametrization-plan-2.md`, section 8).

Route, in order (commit each):
1. Uniform strict differentiability of the patch exponentials `sourceExp` and `targetExp` at every vector of a
   uniform ball, with the derivative a continuous linear equivalence: from the patch's C¹ endpoint field
   (`exists_flow_initialState_C1` gives `ContDiffOn ℝ 1` on the open state ball, hence `HasStrictFDerivAt` at
   each point) and invertibility of the derivative for small velocities by continuity from the identity at
   zero velocity (`hasFDerivAt_F_at_zero_velocity`, `endpointDerivative`), with the radius chosen by
   compactness of `K` before `x, p, L, z`.
2. The metric pullback identity: this is the local-isometry content of the Cartan map, uniform in the anchor.
   Re-derive the argument of `cartanMap_isLocalIsometry_of_selector_aop_bound` for the retained patch flow with
   moving initial position: the Jacobi (first-variation) fields along the geodesic from `extChartAt I x₀ x`
   with velocity `v`, the curvature-1 Jacobi equation on both sides, and the Gauss lemma. The patch's
   fundamental solution `Φ` (joint in initial position and velocity) is the Jacobi field family; the uniform
   time `T` replaces the per-anchor `T`; the anchor-dependent normalization is `patchFrame`/`linear`
   (`linear_metric` already identifies the frame metric transport). Prove the identity first at the anchor
   (`v = 0`, where it reduces to `linear_metric`), then along radial geodesics by the constancy of the
   Jacobi-field inner products for curvature 1 (the same ODE comparison the per-anchor proof uses), with all
   constants taken uniform over `K × H` by compactness.
3. Assemble `uniformDifferentialPullback_of_constantCurvature` and `exists_radius`.
If step 2 resists, deliver step 1 and the exact resisting `def` for the pullback with `target_of_<resisting>`;
do not weaken the quantifier order (one radius before `x, p, L, z`).
