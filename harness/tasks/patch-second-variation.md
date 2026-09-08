# Worker contract

You are a Lean 4 formalization worker on the Poincaré project (toolchain leanprover/lean4:v4.30.0-rc2,
Mathlib pinned). Isolated worktree on branch `worker/patch-second-variation`, cloned `.lake` cache.
Rules: NO sorry/admit/axiom/native_decide; do not edit existing Lean files or `Poincare.lean`; exactly one new
file `Poincare/Global/FixedChartPatchSecondVariation.lean`; no vacuous definitions; report actual command
output; commit each verified lemma on the branch; report to
`harness/reports/patch-second-variation_{done|blocked}.md`. Stop conditions as in
`harness/tasks/M5-glob-69.md` (proved, or the strongest verified partial plus ONE exact resisting `def` and a
`target_of_<resisting>` theorem; never weaken the quantifier order).

# Task: second-order regularity of the patch endpoint map and the mapped geodesic equation

Read first: `harness/reports/uniform-endpoint-reanchoring_blocked.md` (sections "Verified mathematical
progress", "One exact remaining statement", "Why the producer remains blocked"), then
`Poincare/Global/FixedChartUniformEndpointReanchoring.lean` (`UniformMappedGeodesicEquation`,
`target_of_uniformMappedGeodesicEquation`, `exists_uniform_christoffel_transition_of_differentiable_fderiv`,
the mapped-state chain rule with differentiable derivative, `normalizedFlow_hasDerivWithinAt`,
`geodesic_eqOn_unitInterval`, and the two conditional consequences
`exists_onCompact_of_uniformMappedGeodesicEquation`-style theorems), `Poincare/Global/GeodesicFlowJointDerivative.lean`
(`exists_flow_initialState_C1`, `exists_flow_initialState_C1_of_contDiffAt`,
`geodesic_flow_hasFDerivAt_initialState`, `linearizedGeodesicFlowOperator`), `FixedChartUniformSourceNormal.lean`
(`Patch`: `α`, `T`, `r`, `endpoint_C1`, the retained state ball), `FixedChartMovingPositionJacobi.lean`
(`exists_radius`, the flow membership lemmas), and Mathlib's `ContDiffAt.toOpenPartialHomeomorph` /
`OpenPartialHomeomorph.contDiffAt_symm` (regularity of local inverses) and `ContDiffAt.comp`.

Target (frozen), in the instance context of `FixedChartUniformEndpointReanchoring.lean`:

```lean
theorem uniformMappedGeodesicEquation_of_constantCurvature
    (x₀ : M) (p₀ : RoundSphere3) (U V : Set E)
    (C : FixedChartUniformSourceNormal.Patch g x₀ U)
    (D : FixedChartUniformSourceNormal.Patch roundSphereMetric3 p₀ V)
    (hcurv : HasConstantSectionalCurvature3 g 1)
    (hU : U ⊆ IsometryInstantiate.cutoffOneLocus x₀)
    (hV : V ⊆ IsometryInstantiate.cutoffOneLocus p₀)
    (K : Set M) (H : Set RoundSphere3) (hK : IsCompact K) (hKC : K ⊆ C.anchors)
    (hH : IsCompact H) (hHD : H ⊆ D.anchors) :
    FixedChartUniformEndpointReanchoring.UniformMappedGeodesicEquation C D K H
```

with the definition used verbatim, then restate and prove the consequences already reduced to it there:
`uniformEndpointReanchoring_of_constantCurvature` (via `target_of_uniformMappedGeodesicEquation`),
`exists_onCompact` (the H2 `OnCompact`), and the frozen task-9 `exists_radii`.

Route, in order (commit each):
1. Second variation by the augmented-system trick: the pair `(α q t, Φ q t)` solves the augmented ODE
   `(state, operator)' = (geodesicFlowField Γ state, (linearizedGeodesicFlowOperator Γ state).comp operator)` on
   `(E × E) × ((E × E) →L[ℝ] (E × E))`, whose field is `C¹` because `Γ` is `C²` on the cutoff-one zone (the
   repository has `geodesicFlowField_chartChristoffelField_contDiff_two` and the linearized operator is built from
   `fderiv Γ`, which is `C¹`); apply `exists_flow_initialState_C1_of_contDiffAt` (or the general
   `exists_flow_initialState_C1`) to the augmented system to obtain `C¹` dependence of `q ↦ Φ q t` on the initial
   state, hence `ContDiffOn ℝ 2 (fun q => C.α q C.T)` on a sub-ball of the retained state ball (state the exact
   ball you obtain; it must be chosen from the patch data, not per anchor). Do this for a general patch so it
   applies to both `C` and `D`.
2. `C²` of the supplied chart map `chartMap (patch C D) ⟨x,p,L⟩ = (D.endpoint p) ∘ l ∘ (C.endpoint x).symm` near
   the anchors: composition of `C²` maps and the `C²` local inverse of the source endpoint
   (`ContDiffAt.toOpenPartialHomeomorph`/`contDiffAt_symm`), uniformly on a ball chosen before `x, p, L`.
3. From step 2 discharge the hypothesis of `exists_uniform_christoffel_transition_of_differentiable_fderiv`
   (differentiability of `fderiv ℝ F`) to get the uniform Christoffel transition law, then apply the
   mapped-state chain rule to the normalized retained geodesic to prove the initial-value problem of
   `UniformMappedGeodesicEquation` (initial condition from the data's alignment law, ODE on `Icc 0 1`).
4. Assemble the frozen theorem and the three consequences.
If step 1 resists, deliver the exact resisting `def` (the augmented-system regularity statement) with
`target_of_<resisting>`.
