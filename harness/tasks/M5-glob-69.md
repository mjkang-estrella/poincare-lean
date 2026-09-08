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

# Task M5-glob-69: H2 — persistence of the successor-equality radius under motion of the anchors

Target (frozen), in `Poincare/Global/SuccessorEqualityRadiusPersistence.lean`:

```lean
theorem actualSuccessorEqualityRadiusLocalPersistence_of_constantCurvature
    (g : ClosedSmoothRiemannianMetric 3 M) (hcurv : HasConstantSectionalCurvature3 g 1) :
    DifferentialSuccessorEqualityStabilityReduction.ActualSuccessorEqualityRadiusLocalPersistence g
```

in the instance context of that definition's file (`Poincare/Global/DifferentialSuccessorEqualityStabilityReduction.lean`,
typically `[TopologicalSpace M] [T2Space M] [ChartedSpace (ClosedSmoothModel 3) M] [IsManifold (closedSmoothModelWithCorners 3) ∞ M] [CompactSpace M] [ConnectedSpace M]`; check with #check).
By `actualSuccessorEqualityRadiusLocalPersistence_iff_uniform` this is exactly H2
(`UniversalSuccessorEqualityNeighborhood g`), the open obligation `successor-equality-neighborhood`
of `harness/v2/missions/unit-recognition.json`.

What is already proved from curvature (verify each with #check):
- `DifferentialSuccessorEqualityStabilityReduction.fixedAnchorActualSuccessorEqualityNeighborhood_of_constantCurvature`:
  for fixed (x, p) a radius ε such that every datum at z with dist z x < ε has equality on SOME neighborhood of z.
- `DifferentialSuccessorIntervalNaturality.exists_uniform_local_eqOn_differentialSuccessor_all`:
  the fixed-(x,p) equality with radius uniform over alignments L and data d (read its exact form).
- `DifferentialSuccessorFiniteAnchorRadius.exists_uniform_distance_radius_with_datum_eqOn_ball_on_finite_family`:
  one ε for a finite family of (x_i, p_i), still with datum-dependent output radius.
- `UniformTangentAlignmentRigidity.exists_uniform_cartanMap_isLocalIsometry`,
  `UniformAnchoredGeodesicTransition.exists_cartanChartMap_chartChristoffelField_self_F_transition_law`,
  `FTransitionGeodesicMap.mappedState_eqOn_Icc_target_of_F_transition` (ODE-uniqueness engine),
  `ChartTransitionGeodesicMap.chartTransitionState_hasDerivAt_of_cutoff_eq_one_nhds` (geodesics of the
  chart at x and at x' agree on the double cutoff-one zone), and the PL/Grönwall flow packages
  (`expAt_uniform_pl_flow_eq_on_Icc`, `exists_uniform_local_geodesic_chart_flow_variableInitialState_continuousOn`).

What is missing: one radius that stays admissible for all (y, q) near (x, p). The datum-dependent
output radius comes from a PL interval whose length depends on the anchor's chart data; the
mathematical content is that these radii are locally bounded below as the source anchor moves within
one preferred chart (use the chart-transition agreement to compare the flows of nearby anchors in the
fixed chart of x) and as the target anchor moves on the round sphere. Attack in this order and commit
each verified step: (1) persistence under motion of the source anchor with the target fixed, inside the
cutoff-one zone of one preferred chart; (2) persistence under motion of the target anchor on
`RoundSphere3`; (3) the joint statement. If (1) or (2) resists, isolate the exact resisting shape as
described above.
