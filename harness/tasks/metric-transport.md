# Worker contract

You are a Lean 4 formalization worker on the Poincaré project (toolchain leanprover/lean4:v4.30.0-rc2,
Mathlib pinned). Isolated worktree on branch `worker/metric-transport`, cloned `.lake` cache.
Rules: NO sorry/admit/axiom/native_decide; do not edit existing Lean files or `Poincare.lean`; one new file
`Poincare/Global/RiemannianMetricInstanceTransport.lean`; no vacuous definitions; report actual command output;
commit each verified lemma on the branch; report to `harness/reports/metric-transport_{done|blocked}.md`.
Stop conditions as in `harness/tasks/M5-glob-69.md` (proved, or strongest verified partial plus one exact
resisting `def`).

# Task: transport a closed smooth Riemannian metric across charted-space instances with the same maximal atlas

Context. `harness/reports/M5-glob-72_statement_refutation.md` explains why the Cartan development must run on a
controlled `ChartedSpace` instance. `Poincare/Global/ControlledChartInstance.lean` (read it fully) proves the
existence of such an instance `inst'` with `inst'.atlas ⊆ maximalAtlas inst`, equal maximal atlases, uniform-ball
chart sources, and the scalar transport `scalarContMDiff_iff_of_atlas_subset` (`ContMDiff I 𝓘(ℝ) n f` agrees for
`inst` and `inst'`). To run the existing chain on `inst'` we need the metric there.

Definitions to read: `ClosedSmoothRiemannianMetric` (`Poincare/Global/RiemannianContext.lean`; it bundles
`inner : ∀ x, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ` with symmetry, positivity, von Neumann boundedness,
and `contMDiff` of the section in the hom bundle — check the exact field types and which instances they mention),
`ClosedSmoothModel`, `closedSmoothModelWithCorners`, and Mathlib's `TangentSpace`, `TangentBundle`,
`Bundle.ContinuousLinearMap` trivializations, `contMDiffAt_section`, `contMDiffWithinAt_iff_source_of_mem_maximalAtlas`,
`ContMDiffWithinAt.congr`, `inTangentCoordinates`, and the tangent-bundle core coordinate changes
(`tangentBundleCore`, `TangentBundle.symmL_trivializationAt_eq_core`, `tangentBundleCore_coordChange_achart`).

Target (frozen). With `E := ClosedSmoothModel 3`, `I := closedSmoothModelWithCorners 3`,
`{M : Type u} [TopologicalSpace M] [T2Space M] [inst : ChartedSpace E M] [IsManifold I ∞ M]`, and
`(inst' : ChartedSpace E M) (h : @StructureGroupoid.maximalAtlas E M _ _ inst' (contDiffGroupoid ∞ I) =
@StructureGroupoid.maximalAtlas E M _ _ inst (contDiffGroupoid ∞ I))` (or the one-sided inclusion if it suffices):

```lean
noncomputable def transport (g : @ClosedSmoothRiemannianMetric 3 M _ inst _) :
    @ClosedSmoothRiemannianMetric 3 M _ inst' (isManifold_of_maximalAtlas_eq ...)   -- same `inner` values
theorem transport_inner (g) (x : M) : (transport g).inner x = g.inner x               -- as functions on E, via the canonical identification TangentSpace I x = E
```

(state the `IsManifold` instance for `inst'` as an explicit argument or derive it from `h`; name things so that the
result composes with `ControlledChartInstance.exists_controlled_chartedSpace_source_persistence`). The substance is
the smoothness of the metric section for `inst'`: prove a general lemma that `ContMDiff` of a section of the hom
bundle `TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ` is invariant under change of instance with the same maximal
atlas (both instances give the same tangent-bundle coordinate changes on chart overlaps because the charts are the
same maximal-atlas charts), generalizing `scalarContMDiff_iff_of_atlas_subset` from scalar functions to
bundle sections. Prove first the pointwise bridge (the trivializations for `inst'` at `x` are trivializations for
`inst` in the maximal atlas), then the section smoothness, then assemble `transport`. If the hom-bundle step resists,
deliver the tangent-bundle (vector-field) transport and the exact resisting `def` for the hom bundle.

Also prove, as a separate theorem, that `g.toMetricSpace` distances are unchanged by transport if that is cheap
(`(transport g).toMetricSpace = g.toMetricSpace` or `dist` equality); if not cheap, skip and say so.
