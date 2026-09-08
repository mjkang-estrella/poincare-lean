# Worker contract (Lean task)

You are a Lean 4 formalization worker on the Poincaré project (toolchain leanprover/lean4:v4.30.0-rc2, Mathlib pinned). Isolated worktree on branch `worker/hamilton-compact-family-invariant-continuity`, cloned `.lake` cache. Rules: NO sorry/admit/axiom/native_decide/opaque; do not edit existing Lean files or `Poincare.lean`; exactly one new file as named below; no vacuous definitions and no new analytic premises hidden in definitions; commit each verified lemma on the branch; report actual command output to `harness/reports/hamilton-compact-family-invariant-continuity_{done|blocked}.md`. Gate: `LEAN_NUM_THREADS=1 lake env lean <file>` exit 0; `rg -n '\b(sorry|admit|axiom)\b|native_decide|\bopaque\b' <file>` empty (also avoid these words in comments); `#print axioms` of every new declaration exactly `[propext, Classical.choice, Quot.sound]`; `git diff --check`. Every declaration name you cite must be verified by grep in the repo or the pinned Mathlib tree; record every probe with its actual output. If blocked, the report must display the exact resisting statement and the strongest compiled partial result; never weaken the target silently. The frozen contract files (`Poincare/Statement.lean`, `Poincare/TopologyExtraction.lean`, `Poincare/Surgery.lean`, `Poincare/RicciFlowInterface.lean`, `Poincare/ProofProgress/GroundedTopologyStatements.lean`, `Poincare/ProofProgress/GroundedPerelmanSingularityControl.lean`) are read-only.

Context: read `HANDOFF.md` top section and `harness/reports/reaction-record-decomposition_done.md` (sections 2, 3, 4 and the evidence appendix) first. `Poincare/Global/HamiltonReactionCoreReduction.lean` defines the residual core `HamiltonReactionCore3`; this task removes one of its remaining explicit clauses.

# Task hamilton-compact-family-invariant-continuity

Module: `Poincare/Global/HamiltonCompactFamilyInvariantContinuity.lean`. Namespace: `Poincare.HamiltonCompactFamilyInvariantContinuity`. Imports: `Poincare.Global.ClosedMetricThirdJetTopology`, `Poincare.Global.NormalizedFlowCompactMeanEnergyMeasureContinuity`, `Poincare.Global.NormalizedFlowInvariantPairJointContinuity`, `Poincare.Global.HamiltonReactionCoreReduction` (and whatever landed modules you need).

Objective: prove the three compact-family continuity clauses of `HamiltonReactionCore3` from joint continuity of every scalar third-jet profile of the family, so the three clauses can be replaced by that single hypothesis (or, better, dropped if you find a landed producer for the jet-profile continuity from a topology on metrics).

Target (probed by the previous worker as `compactFamilyContinuityTarget`; prove it as a theorem with these exact hypotheses and conclusion):

```lean
theorem invariantContinuity_of_thirdJetProfiles_continuous
    (K : Type v) [TopologicalSpace K] [CompactSpace K]
    (metric : K → ClosedSmoothRiemannianMetric 3 M)
    (hjet : ∀ slot : MetricEntryThirdJetSlot 3 M,
      Continuous (fun p : K × ClosedSmoothModel 3 ↦
        metricEntryThirdJetProfile (metric p.1) slot p.2)) :
    Continuous (fun k ↦ closedMetricFiniteVolumeMeasure (metric k)) ∧
    Continuous (fun p : K × M ↦ (metric p.1).scalarAt p.2) ∧
    Continuous (fun p : K × M ↦ (metric p.1).tracelessRicciNormSqAt p.2)
```

with the section variables of `HamiltonReactionCoreReduction.lean`. Study how the landed time-family results (`continuous_joint_scalarAt_and_tracelessRicciNormSqAt_of_global_metricEntriesJointContDiffAt_three` in `NormalizedFlowInvariantPairJointContinuity.lean`, and the weak measure continuity in `NormalizedFlowCompactMeanEnergyMeasureContinuity.lean`) obtain continuity for `gt` on `ℝ × M` from jet regularity, and generalize the coordinate-to-intrinsic step from the parameter `ℝ` to an arbitrary compact `K`. The topology on `closedMetricFiniteVolumeMeasure` values is whatever the landed clause uses (check `HamiltonReactionCore3`); do not change it.

Then add: a definition `HamiltonReactionCore3Jet` (the core with the three continuity clauses replaced by the single jet-profile continuity hypothesis) and `theorem hamiltonReactionCore3_of_jet` proving the original core from it, plus `theorem hamiltonConvergencePinchedLimit3_of_hamiltonReactionCore3Jet` and the universal versions.

Exact stop condition: the displayed theorem compiles with no extra hypothesis and the jet-form core with its endpoint theorem passes the gate. If only two of the three conclusions are provable, land those and report exactly the missing coordinate-to-intrinsic or measure-continuity implication.
