# Worker contract

You are a Lean 4 formalization worker on the Poincaré project (toolchain leanprover/lean4:v4.30.0-rc2,
Mathlib pinned). Isolated worktree on branch `worker/uniform-endpoint-reanchoring`, cloned `.lake` cache.
Rules: NO sorry/admit/axiom/native_decide; do not edit existing Lean files or `Poincare.lean`; exactly one new
file `Poincare/Global/FixedChartUniformEndpointReanchoring.lean`; no vacuous definitions; report actual command
output; commit each verified lemma on the branch; report to
`harness/reports/uniform-endpoint-reanchoring_{done|blocked}.md`. Stop conditions as in
`harness/tasks/M5-glob-69.md` (proved, or the strongest verified partial plus ONE exact resisting `def` and a
`target_of_<resisting>` theorem; never weaken the quantifier order).

# Task: uniform endpoint reanchoring (exponential naturality of the supplied Cartan map, uniform in the anchor)

Read first: `harness/reports/fixed-chart-local-successor-equality_blocked.md` (the exact remainder
`UniformEndpointReanchoring` and its reduction `exists_onCompact_of_uniformEndpointReanchoring`), then
`Poincare/Global/FixedChartLocalSuccessorEquality.lean`, `Poincare/Global/FixedChartMovingPositionJacobi.lean`
(landed: `uniformDifferentialPullback_of_constantCurvature` — the supplied Cartan map is a local isometry with
one radius before all moving parameters — and `exists_radius`, the H1 replacement), the flow lemmas in
`FixedChartUniformJacobiComparison.lean` and `FixedChartMovingPositionJacobi.lean` (`flow_mem_target_cutoffOne`,
speed preservation, full-interval fundamental solutions), the per-anchor naturality proof to be made uniform:
`DifferentialSuccessorNaturality.exists_map_expAt_ray_naturality_radius` and
`DifferentialSuccessorIntervalNaturality.exists_uniform_reanchoredChartMap_expAtChart_naturality_ball`
(`Poincare/Global/DifferentialSuccessorNaturality.lean`, `DifferentialSuccessorIntervalNaturality.lean`), and
the ODE engine `FTransitionGeodesicMap.mappedState_hasDerivAt_of_F_transition` /
`mappedState_eqOn_Icc_target_of_F_transition` with the Christoffel transition law
`UniformAnchoredFTransition.exists_cartanChartMap_christoffelAt_F_transition_law_curvature_only` and
`LCNaturality.christoffelAt_map_eq_signed_transport_of_differentiated_pullback` (the chart-level Koszul
argument: a C² map with the metric pullback identity transports Christoffel symbols).

Target (frozen): in the instance context of `FixedChartLocalSuccessorEquality.lean`,

```lean
theorem uniformEndpointReanchoring_of_constantCurvature
    (x₀ : M) (p₀ : RoundSphere3) (U V : Set E)
    (C : FixedChartUniformSourceNormal.Patch g x₀ U)
    (D : FixedChartUniformSourceNormal.Patch roundSphereMetric3 p₀ V)
    (hcurv : HasConstantSectionalCurvature3 g 1)
    (hU : U ⊆ IsometryInstantiate.cutoffOneLocus x₀)
    (hV : V ⊆ IsometryInstantiate.cutoffOneLocus p₀)
    (K : Set M) (H : Set RoundSphere3) (hK : IsCompact K) (hKC : K ⊆ C.anchors)
    (hH : IsCompact H) (hHD : H ⊆ D.anchors) :
    FixedChartLocalSuccessorEquality.UniformEndpointReanchoring
      (CartanSuppliedDifferentialSuccessor.patch C D) K H
```

with the definition used verbatim, and then the two consequences already reduced to it in that module:
`exists_onCompact` (the H2 `OnCompact` with radii before all moving parameters) and the frozen task-9
target `exists_radii` (H1 and H2 together, using the landed `exists_radius` for the H1 conjunct).

Mathematics and route (commit each step): the supplied Cartan map `map Q ⟨x,p,L⟩` is, in the fixed charts, a
C² map with the uniform metric pullback identity (from `uniformDifferentialPullback_of_constantCurvature` plus
the patch's C¹/C² data — establish C² of the chart map from the patch's joint regularity, or, if only C¹ with
differentiable derivative is available, state exactly what `christoffelAt_map_eq_signed_transport_of_differentiated_pullback`
needs and prove it). (1) The Christoffel transition law for the chart map at every point of a uniform
neighbourhood, from the pullback identity by the chart-level Koszul argument. (2) Geodesic transport: the chart
map sends the source patch geodesic from `z` with velocity `v` to the sphere patch geodesic from `map z` with
velocity `l_d v` (`mappedState_eqOn_Icc_target_of_F_transition`, ODE uniqueness on the retained interval, using
the patch flows and cutoff-one containment). (3) Evaluate at time `T`: that is exactly the endpoint identity of
`UniformEndpointReanchoring`; all radii come from the patch data and compactness, chosen before `x, p, L, z, d`.
(4) Assemble the frozen theorem and the two consequences. If (1) resists, deliver the exact resisting `def`.
