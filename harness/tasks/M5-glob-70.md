# Worker Contract (prepended to every task prompt)

You are a Lean 4 formalization worker on the Poincaré Conjecture project.
Toolchain: leanprover/lean4:v4.30.0-rc2, Mathlib pinned by lake-manifest.json.
You work in an isolated git worktree with a prebuilt `.lake` cache.

Hard rules — violating any of these means your work is rejected automatically:
1. NO `sorry`, NO new `axiom`, NO `native_decide`.
2. Do NOT alter the frozen target statement given in the task. If you believe
   the statement is wrong or unprovable as stated, STOP and write your analysis
   to `harness/reports/<task_id>_blocked.md` instead — that is a valid, valuable outcome.
3. NO vacuous content: no `Prop`-valued structure fields holding arbitrary
   propositions, no `True`-instantiable certificates, no definitions whose
   theorems could be satisfied trivially. Every hypothesis must be used or removed.
4. Verify with `lake build <module>` before declaring done. Report the actual
   build result honestly. A failed build reported as failed is acceptable;
   a failed build reported as success is the one unforgivable outcome.
5. Commit your work with a descriptive message (git is available in the worktree).
6. Prefer many small proven lemmas over one monolithic attempt. Partial verified
   progress committed > complete unverified attempt.

Style: follow the existing file's conventions. Mathlib naming conventions for
new lemmas. Keep proofs terse but readable.

# Shared context (read before writing anything)

Base commit: main at `d08f4a52`. Read, in this order: `harness/reports/M5-glob-68_closure.md`,
`Poincare/Global/CartanTwoNeighborhoodDevelopment.lean`, the HANDOFF.md section
"2026-09-07 Boundary correction", and then the files named below. Lean is the source of
truth; reports before M5-glob-68 are historical and describe boundaries that are closed.

Environment: you are in an isolated git worktree on branch `worker/<task>` with a cloned
`.lake` cache, so `lake build Poincare.Global.<NewModule>` is incremental (a few seconds
plus your file). Probe exact types with `lake env lean` on scratch files under `/tmp`.
Some Global files are large; grep and read ranges. Do NOT edit any existing Lean file and
do NOT edit `Poincare.lean`; put everything in ONE new file under `Poincare/Global/`.
Do not touch `harness/` except to write your report. Commit your work on the branch.

Acceptance (the orchestrator reruns this; report the actual output):
  lake build Poincare.Global.<NewModule>
  grep -nE "\\b(sorry|admit)\\b|^\\s*axiom\\b|native_decide" Poincare/Global/<NewModule>.lean   # must be empty
  printf "import Poincare.Global.<NewModule>\\n#print axioms <each new theorem>\\n" > /tmp/ax.lean && lake env lean /tmp/ax.lean
  # every closure must be exactly [propext, Classical.choice, Quot.sound]

Stop conditions: (a) the target theorem is proved; or (b) you have proved the strongest
strictly smaller VERIFIED partial and isolated ONE remaining resisting statement as an exact
Lean `def` (a Prop) plus a conditional theorem `target_of_<resisting>` that derives the
target from it, with a report explaining mathematically why it resists. Both outcomes are
valuable; a hypothesis-shifting wrapper with no new verified content is not.
Report to `harness/reports/<task>_{done|blocked}.md` with the exact commands and outputs.

# Task M5-glob-70: H1 — fixed-chart persistence of successor data

Target (frozen), in `Poincare/Global/FixedChartSuccessorDataPersistence.lean`:

```lean
theorem fixedChartLocalGenericDataPersistence_of_constantCurvature
    (g : ClosedSmoothRiemannianMetric 3 M) (hcurv : HasConstantSectionalCurvature3 g 1) :
    CartanGenericSuccessorDataLocalCover.FixedChartLocalGenericDataPersistence g
```

in the instance context of `Poincare/Global/CartanGenericSuccessorDataLocalCover.lean` (check with #check).
Through `universalSuccessorDataNeighborhood_of_fixedChartLocalGenericDataPersistence` this discharges H1
(`UniversalSuccessorDataNeighborhood g`), the open obligation `successor-data-neighborhood` of
`harness/v2/missions/unit-recognition.json`.

Already proved from curvature (verify): the fixed-center patch
`CartanGenericSuccessorDataLocalCover.exists_open_fixedChartCenter_genericSuccessorDataPatch_of_curvature`
(read the whole statement and the `FixedChartAnchorEndpointPackage` structure), the vertical patch
`exists_open_vertical_genericSuccessorDataPatch_of_curvature`,
`DifferentialInducedSuccessor.exists_data_on_punctured_ball` and `DifferentialSuccessorZero.exists_data_on_ball`
(what a `DifferentialInducedSuccessor.Data` needs: chart memberships, strict derivatives of both
exponential charts, the chart-metric pullback identity), and the alignment-uniform local isometry
`UniformTangentAlignmentRigidity.exists_uniform_cartanMap_isLocalIsometry`.

What is missing: the set `controlledGenericSuccessorLocusOn C.rawLocalFamily targets radius` must lie in the
data locus for anchors (y, q) NEAR (x₀, p₀), not only at the center. Every field of `Data` is an open condition
or a strict-derivative fact at a point that moves continuously with (y, q, z); the expected proof is an
open-set argument in the fixed chart of x₀ using the chart-transition agreement for the source and a
neighborhood argument on `RoundSphere3` for the target. Attack: (1) persistence in z for fixed (y, q) near the
center — likely already implied by the vertical patch; (2) persistence in the source anchor y inside the
fixed chart; (3) persistence in the target anchor q; (4) assemble. Isolate the exact resisting shape if a step
resists.
