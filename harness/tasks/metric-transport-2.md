# Worker contract

You are a Lean 4 formalization worker on the Poincaré project (toolchain leanprover/lean4:v4.30.0-rc2,
Mathlib pinned). Isolated worktree on branch `worker/metric-transport-2`, cloned `.lake` cache.
Rules: NO sorry/admit/axiom/native_decide; do not edit existing Lean files or `Poincare.lean`; one new file
`Poincare/Global/RiemannianMetricInstanceTransportGeometric.lean`; no vacuous definitions; report actual command
output; commit each verified lemma on the branch; report to `harness/reports/metric-transport-2_{done|blocked}.md`.
Stop conditions as in `harness/tasks/M5-glob-69.md` (proved, or strongest verified partial plus one exact resisting
`def` and a `target_of_<resisting>` theorem).

# Task: geometric transport of a closed smooth Riemannian metric across charted-space instances

Read first: `harness/reports/metric-transport_blocked.md` (the previous attempt; its "exact first action" is this
task), `Poincare/Global/RiemannianMetricInstanceTransport.lean` (the verified trivialization formula
`inner_trivialization_apply`), `Poincare/Global/ControlledChartInstance.lean` (the controlled instance and scalar
transport), `Poincare/Global/RiemannianContext.lean` (`ClosedSmoothRiemannianMetric`), and Mathlib's tangent bundle
(`tangentBundleCore`, `tangentBundleCore_coordChange_achart`, `TangentBundle.trivializationAt_apply`,
`TangentBundle.symmL_trivializationAt_eq_core`, `contMDiffAt_section`, `contMDiffWithinAt_iff_source_of_mem_maximalAtlas`).

Setting. `E := ClosedSmoothModel 3`, `I := closedSmoothModelWithCorners 3`, `{M : Type u} [TopologicalSpace M]
[T2Space M] [inst : ChartedSpace E M] [IsManifold I ∞ M]`, and a second instance `inst' : ChartedSpace E M` with
`inst'.atlas ⊆ maximalAtlas inst` (equal maximal atlases follow; `ControlledChartInstance` supplies such an
`inst'` and its `IsManifold` proof — reuse those names, do not re-prove them).

Target (frozen, replacing the invalid raw-fiber contract). Write `c_x := @chartAt E _ M _ inst x` and
`c'_x := @chartAt E _ M _ inst' x`, and let
`J x : E ≃L[ℝ] E` be the derivative of the chart change `c_x ∘ (c'_x).symm` at `c'_x x`
(from `inst'`-coordinates to `inst`-coordinates; it is invertible because both charts lie in the same smooth maximal
atlas; obtain it from `tangentBundleCore` coordinate changes or `fderiv` of the transition map — choose the form
that makes the trivialization lemmas apply). Deliver:

```lean
noncomputable def transport (g : @ClosedSmoothRiemannianMetric 3 M _ inst _) :
    @ClosedSmoothRiemannianMetric 3 M _ inst' _
theorem transport_inner (g) (x : M) (v w : E) :
    (transport g).inner x v w = g.inner x (J x v) (J x w)
```

where the `inner` fields are read through the definitional identification `TangentSpace I x = E`. The
smoothness field is the substance: prove that the `inst'` hom-bundle trivialization coefficients of `transport g`
at an anchor `a` equal the `inst` coefficients of `g` at `a` composed with the (smooth, in `a`-coordinates)
identifications, and conclude `ContMDiff` for `inst'` from `ContMDiff` for `inst` using the maximal-atlas chart
independence (`contMDiffWithinAt_iff_source_of_mem_maximalAtlas`, as in
`ControlledChartInstance.scalarContMDiff_iff_of_atlas_subset`). Symmetry, positivity, and boundedness transfer
through the linear equivalence `J x`.

Order of work (commit each): (1) define `J` and prove it intertwines the `inst` and `inst'` tangent trivializations
at every anchor (the pointwise bridge); (2) the coefficient identity for the hom-bundle section; (3) the
`ContMDiff` transfer; (4) assemble `transport`, prove `transport_inner`; (5) if cheap, prove that `J x` is a
linear isometry between `g.inner x` and `(transport g).inner x` and that the induced distances agree
(`(transport g).toMetricSpace` vs `g.toMetricSpace`); if not cheap, state the exact resisting `def`. Do not
introduce a raw-fiber identification anywhere: every fiber comparison goes through `J`.
