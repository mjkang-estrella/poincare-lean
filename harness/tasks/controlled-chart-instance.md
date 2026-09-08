# Worker contract

You are a Lean 4 formalization worker on the Poincaré project (toolchain leanprover/lean4:v4.30.0-rc2,
Mathlib pinned). Isolated worktree on branch `worker/controlled-chart-instance`, cloned `.lake` cache.
Rules: NO sorry/admit/axiom/native_decide; do not edit existing Lean files or `Poincare.lean`; one new file
`Poincare/Global/ControlledChartInstance.lean`; no vacuous definitions; report actual command output; commit on
the branch; report to `harness/reports/controlled-chart-instance_{done|blocked}.md`. Stop conditions as in
`harness/tasks/M5-glob-69.md` (proved, or strongest verified partial plus one exact resisting `def`).

# Task: a controlled ChartedSpace instance with uniform-ball chart sources

Read first: `harness/reports/M5-glob-72_statement_refutation.md` and the three modules it names; the
`GenericJointRegularityCounterexample.lean` construction shows what must be avoided;
`Poincare/Global/CartanSourceExponentialFamily.lean` (the `Family`/`genericFamily` abstraction and the four
clauses of `GenericJointRegularity`); Mathlib `Mathlib/Geometry/Manifold/ChartedSpace.lean`
(`ChartedSpace`, `StructureGroupoid.maximalAtlas`, `ChartedSpace.HasGroupoid`, `ClosedUnderRestriction`,
`OpenPartialHomeomorph.restr`, `restrOpen`), `IsManifold` (`Mathlib/Geometry/Manifold/IsManifold/Basic.lean`),
and `lebesgue_number_lemma_of_metric`.

Target (frozen). With `E := ClosedSmoothModel 3`, `I := closedSmoothModelWithCorners 3`, for
`{M : Type u} [TopologicalSpace M] [T2Space M] [inst : ChartedSpace E M] [IsManifold I ∞ M] [CompactSpace M]`
and any metric structure `[MetricSpace M]` compatible with the topology (take it as a hypothesis
`(hd : ‹MetricSpace M›.toUniformSpace.toTopologicalSpace = ‹TopologicalSpace M›)` or work with a
`ClosedSmoothRiemannianMetric 3 M` and its `g.toMetricSpace`, whichever is cleanest; state clearly):

```lean
theorem exists_controlled_chartedSpace :
    ∃ (inst' : ChartedSpace E M) (δ : ℝ), 0 < δ ∧
      (∀ x : M, Metric.ball x δ ⊆ (@chartAt E _ M _ inst' x).source) ∧
      (∀ x : M, @chartAt E _ M _ inst' x ∈ (contDiffGroupoid ∞ I).maximalAtlas M) ∧
      @IsManifold E _ _ _ I M _ inst' ∞
```

(adjust the exact spelling of the maximal-atlas membership and the `IsManifold` instance for `inst'` to what
elaborates; the mathematical content is: the new preferred charts are restrictions of charts of the original
smooth structure, every new chart contains the uniform `δ`-ball about its anchor, and the new instance is
smooth with the same maximal atlas). Also prove the immediate corollary that for the new instance
`∀ x, {y | x ∈ (@chartAt E _ M _ inst' y).source} ∈ 𝓝 x` (the clause that `GenericJointRegularity` needs and
that the punctured instance violates), and, if it is cheap, that the two instances have the same
`ContMDiff` functions to `ℝ` (`ContMDiff I 𝓘(ℝ) n f` for one iff for the other) — that lemma is the first
brick of the metric transport that the next task needs; isolate it as a separate `def`+theorem if it resists.

Route: cover `M` by the original chart sources; extract a finite subcover by compactness; take a Lebesgue
number `δ` for it; define `chartAt' x` as the original chart of the subcover member containing `ball x δ`
(choose with `Classical.choose` on the Lebesgue statement), restricted with `restrOpen` to that source (or
unrestricted, if the subcover chart already works); `atlas' := image of the finite index set`; membership in
the maximal atlas is inherited from the original atlas; `IsManifold` for `inst'` follows since all new
charts belong to the original maximal atlas (`StructureGroupoid.compatible_of_mem_maximalAtlas`).
Commit each verified lemma.
