# Controlled chart instance: done

Date: 2026-09-07, America/Los_Angeles.
Worker branch: `worker/controlled-chart-instance`.
Recorded base: `c7338a642d2cf5bf3044f1ed5ca1a90bb86cf075`.
Proof head: `df7b3ed3`.
Status: theorem proved, awaiting independent orchestrator review. No merge or
acceptance status was written.

## Result

New file: `Poincare/Global/ControlledChartInstance.lean`.
All declarations are in `Poincare.ControlledChartInstance`.

`exists_controlled_chartedSpace` proves the frozen existential and additionally
proves that the new atlas is finite, is contained in the original atlas, and
has exactly the original smooth maximal atlas. Every preferred chart is an
unchanged original chart selected from a finite subcover. No restriction is
needed because the Lebesgue lemma supplies containment of the whole ball.
The construction works for an empty manifold without a nonemptiness premise.

`exists_controlled_chartedSpace_source_persistence` gives the same witness
with `∀ x, {y | x ∈ (chartAt' y).source} ∈ 𝓝 x`. Its proof is the distance
symmetry lemma `source_slice_mem_nhds_of_ball_subset`.

`exists_controlled_chartedSpace_of_compatibleMetric` retains the original
`[t : TopologicalSpace M]`, original charted-space instance, smoothness, and
compactness, and accepts

```lean
(d : MetricSpace M) (hd : d.toUniformSpace.toTopologicalSpace = t)
```

Its conclusion installs `d.replaceTopology hd.symm`, which preserves the
distance of `d` and has topology definitionally equal to `t`. Thus chart
sources and neighborhoods refer to the original topology. The metric-only
version uses the topology bundled in its `MetricSpace` instance. A separate
`T2Space` hypothesis is unnecessary because the compatible metric supplies it.
The frozen-target probe also passed with the requested explicit `T2Space`.

The additional scalar transport is proved, with no resisting statement:

```lean
scalarContMDiff_iff_of_atlas_subset
    (inst' : ChartedSpace E M)
    (h : inst'.atlas ⊆ originalSmoothMaximalAtlas)
    (hn : n ≤ ∞) (f : M → ℝ) :
    scalarContMDiff inst n f ↔ scalarContMDiff inst' n f
```

Here `scalarContMDiff` is exactly `ContMDiff I 𝓘(ℝ) n f` with the supplied
source instance. `chartedSpaceOfCover_scalarContMDiff_iff` specializes this to
the actual finite-cover constructor. The bound `n ≤ ∞` is essential: smooth
chart compatibility does not imply analytic compatibility.

## Proof and instance checks

1. Compactness gives a finite subcover of original preferred-chart sources.
2. `lebesgue_number_lemma_of_metric` gives one positive radius for that cover.
3. `Classical.choose` selects a finite-subcover index for each anchor.
4. `chartedSpaceOfCover` uses the image of the finite set as its atlas.
5. `isManifold_and_maximalAtlas_eq` proves smooth compatibility and both
   inclusions of maximal atlases by groupoid compatibility and locality.
6. Scalar transport expresses both smoothness predicates using the same
   replacement chart through
   `contMDiffWithinAt_iff_source_of_mem_maximalAtlas`.

Both original and replacement maximal-atlas arguments are explicit in the
exported declarations. This matters because Lean automatically considers
local charted-space arguments during instance search. A temporary version
emitted an unused-original-instance warning; it was corrected before the
verified commit. The final module emits no warnings. A separate probe checks
the frozen existential and the scalar equivalence with visibly distinct
`original` and `replacement` instances.

## Verification

Exact final commands and actual outputs follow. `LEAN_NUM_THREADS=1` was set
for every Lean invocation. The focused build is the only Lake build launched.

```text
$ LEAN_NUM_THREADS=1 lake build Poincare.Global.ControlledChartInstance
✔ [2702/2702] Built Poincare.Global.ControlledChartInstance (2.5s)
Build completed successfully (2702 jobs).

EXIT_CODE=0

$ LEAN_NUM_THREADS=1 lake env lean Poincare/Global/ControlledChartInstance.lean
EXIT_CODE=0
```

Direct elaboration produced no stdout or stderr.

```text
$ rg -n '\b(sorry|admit|axiom)\b|native_decide' Poincare/Global/ControlledChartInstance.lean
EXIT_CODE=1
$ git diff --check
EXIT_CODE=0
```

The scan produced no matches; exit 1 is the expected empty-search result.

The axiom probe imports the new module and executes `#print axioms` on every
new theorem:

```text
$ LEAN_NUM_THREADS=1 lake env lean /tmp/controlled-chart-instance-evidence/axioms.lean
'Poincare.ControlledChartInstance.isManifold_and_maximalAtlas_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.ControlledChartInstance.scalarContMDiff_iff_of_atlas_subset' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.ControlledChartInstance.exists_finite_uniform_chart_cover' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.ControlledChartInstance.chartedSpaceOfCover_ball_subset' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.ControlledChartInstance.chartedSpaceOfCover_scalarContMDiff_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.ControlledChartInstance.source_slice_mem_nhds_of_ball_subset' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.ControlledChartInstance.exists_controlled_chartedSpace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.ControlledChartInstance.exists_controlled_chartedSpace_source_persistence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.ControlledChartInstance.exists_controlled_chartedSpace_of_compatibleMetric' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]

EXIT_CODE=0
```

```text
$ LEAN_NUM_THREADS=1 lake env lean /tmp/controlled-chart-instance-evidence/frozen-target.lean
EXIT_CODE=0
```

The frozen-target probe produced no stdout or stderr. The probe also checks
that the scalar theorem elaborates as the direct `ContMDiff` equivalence,
without mentioning its named adapter.

## Attempts and evidence

Early elaborations failed on a subtype coercion for `Classical.choose`, the
parameter order of `StructureGroupoid.maximalAtlas`, selection of the wrong
local charted-space instance, and an underconstrained scalar-chart membership.
The fixes were `.val`, the actual exported parameter order, explicit original
instance arguments and local instance restoration, and a typed membership
lemma. An intermediate constructor commit was amended after the corrected
constructor and maximal-atlas lemma compiled. All seven final proof commits
contain verified Lean code.

Compiler excerpts are preserved in
`/tmp/controlled-chart-instance-evidence/failed-compiler-excerpts.log`.
Final build, Lean, axiom, declaration, frozen-target, and scan logs and probes
are in that directory. The final diff against the recorded base is preserved
as `/tmp/controlled-chart-instance-evidence/final.diff`.

Proof commits, in order:

```text
0c4db296 Prove finite original-chart cover with uniform source balls
c0a29d5f Construct controlled chart selection and prove maximal-atlas preservation
bdf71de5 Prove existence of a finite controlled smooth charted-space instance
dfcac5fc Derive fixed-endpoint source persistence from uniform chart balls
8fdcdc07 Expose source-persistent controlled charts for any compatible metric
a75411d1 Prove scalar smoothness transport between compatible charted instances
df7b3ed3 Specialize scalar smoothness transport to the controlled finite cover
```

## Scope and next action

No existing Lean file or `Poincare.lean` was edited. The only additional
tracked changes are this report and the required dated `HANDOFF.md` entry.
No mission, task, ledger, service, or other worktree was changed.
Root integration audits and a full project build remain the orchestrator's
responsibility and were not run by this worker.

This closes the controlled preferred-chart task. It does not prove joint
regularity of the generic exponential family, H1, H2, metric or curvature
transport, or the Poincare conjecture. In particular, a finite chart selection
need not vary continuously with its anchor.

Exact first action for the orchestrator after applying these commits to the
recorded base:

```sh
LEAN_NUM_THREADS=1 lake build Poincare.Global.ControlledChartInstance
```

Then review the two explicit instance arguments and re-run the axiom and
frozen-target probes before accepting. The next mathematical task is transport
of `ClosedSmoothRiemannianMetric` across the compatible charted structures.
