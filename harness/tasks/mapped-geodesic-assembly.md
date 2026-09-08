# Worker contract

You are a Lean 4 formalization worker on the Poincaré project (toolchain leanprover/lean4:v4.30.0-rc2,
Mathlib pinned). Isolated worktree on branch `worker/mapped-geodesic-assembly`, cloned `.lake` cache.
Rules: NO sorry/admit/axiom/native_decide; do not edit existing Lean files or `Poincare.lean`; exactly one new
file `Poincare/Global/FixedChartMappedGeodesicAssembly.lean`; no vacuous definitions; report actual command
output; commit each verified lemma on the branch; report to
`harness/reports/mapped-geodesic-assembly_{done|blocked}.md`. Stop conditions as in
`harness/tasks/M5-glob-69.md` (proved, or the strongest verified partial plus ONE exact resisting `def` and a
`target_of_<resisting>` theorem; never weaken the quantifier order).

# Task: assemble the H2 replacement — chart-map C², transition law, mapped geodesic equation, exists_radii

Now landed on `main` (read all): `FixedChartAugmentedSystemRegularity.lean` (`patch_endpoint_contDiffOn_two`:
`ContDiffOn ℝ 2 (fun q => C.α q C.T)` on the full retained ball, for any patch — including the sphere patch `D`),
`FixedChartUniformEndpointReanchoring.lean` (`UniformMappedGeodesicEquation`, `target_of_uniformMappedGeodesicEquation`,
`exists_uniform_christoffel_transition_of_differentiable_fderiv` — the uniform Koszul transition law conditional
only on `DifferentiableAt ℝ (fderiv ℝ F) q` near the moving anchors, the mapped-state chain rule needing only a
differentiable derivative, `normalizedFlow_hasDerivWithinAt`, `geodesic_eqOn_unitInterval`,
`exists_uniform_endpoint_displacement_radius`, and the two conditional consequences of the mapped geodesic
equation), `FixedChartMovingPositionJacobi.lean` (`exists_radius`, the H1 replacement, and
`uniformDifferentialPullback_of_constantCurvature`), `FixedChartLocalSuccessorEquality.lean`
(`exists_uniform_common_source_radii`, `exists_onCompact_of_uniformEndpointReanchoring`,
`exists_radii_of_uniformDifferentialPullback_of_uniformEndpointReanchoring`),
`CartanSuppliedDifferentialSuccessor.lean` (`chartMap`, `linear`, `patch`, `Data`), and the report
`harness/reports/uniform-endpoint-reanchoring_blocked.md`.

Targets (frozen), in the instance context of `FixedChartUniformEndpointReanchoring.lean`:

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

then `uniformEndpointReanchoring_of_constantCurvature` (via `target_of_uniformMappedGeodesicEquation`),
`exists_onCompact` (the H2 `OnCompact` of `FixedChartLocalSuccessorEquality`), and the frozen task-9 target
`exists_radii` (H1 and H2 together; the H1 conjunct from the landed `exists_radius`). Copy the exact frozen
statements from `harness/reports/parametrization-plan-2.md` section 9 and the landed reductions.

Route (commit each): (1) `C²` of the supplied chart map `chartMap (patch C D) ⟨x, p, L⟩` on a ball chosen before
`x, p, L`: it is `(D.endpoint p) ∘ (linear) ∘ (C.endpoint x).symm` in coordinates; both endpoints are `C²` by
`patch_endpoint_contDiffOn_two` (composed with the fixed time rescaling), the local inverse of a `C²` map with
invertible derivative is `C²` (`ContDiffAt.toOpenPartialHomeomorph` and `OpenPartialHomeomorph.contDiffAt_symm`,
or the repository's inverse-function regularity lemmas), and `linear` is a continuous linear equivalence; hence
`DifferentiableAt ℝ (fderiv ℝ F) q` on that ball. (2) Discharge the hypothesis of
`exists_uniform_christoffel_transition_of_differentiable_fderiv` to get the uniform transition law. (3) Apply the
mapped-state chain rule to the normalized retained source geodesic (`normalizedFlow_hasDerivWithinAt`) to prove
the initial-value problem in `UniformMappedGeodesicEquation` (initial condition: the data's alignment law
`Data.alignment` / `linear (patch C D) d.successor v` at time zero; the ODE on `Icc 0 1` from the transition law),
with all radii from the patch data and compactness. (4) Assemble the four theorems. If (1) resists, deliver the
exact resisting `def` with `target_of_<resisting>`.
