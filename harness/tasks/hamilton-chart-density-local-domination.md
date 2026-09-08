# Worker contract (Lean task)

You are a Lean 4 formalization worker on the Poincaré project (toolchain leanprover/lean4:v4.30.0-rc2, Mathlib pinned). Isolated worktree on branch `worker/hamilton-chart-density-local-domination`, cloned `.lake` cache. Rules: NO sorry/admit/axiom/native_decide/opaque; do not edit existing Lean files or `Poincare.lean`; exactly one new file as named below; no vacuous definitions and no new analytic premises hidden in definitions; commit each verified lemma on the branch; report actual command output to `harness/reports/hamilton-chart-density-local-domination_{done|blocked}.md`. Gate: `LEAN_NUM_THREADS=1 lake env lean <file>` exit 0; `rg -n '\b(sorry|admit|axiom)\b|native_decide|\bopaque\b' <file>` empty (also avoid these words in comments); `#print axioms` of every new declaration exactly `[propext, Classical.choice, Quot.sound]`; `git diff --check`. Every declaration name you cite must be verified by grep in the repo or the pinned Mathlib tree; record every probe with its actual output. If blocked, the report must display the exact resisting statement and the strongest compiled partial result; never weaken the target silently. The frozen contract files (`Poincare/Statement.lean`, `Poincare/TopologyExtraction.lean`, `Poincare/Surgery.lean`, `Poincare/RicciFlowInterface.lean`, `Poincare/ProofProgress/GroundedTopologyStatements.lean`, `Poincare/ProofProgress/GroundedPerelmanSingularityControl.lean`) are read-only.

Context: read `HANDOFF.md` top section and `harness/reports/reaction-record-decomposition_done.md` (sections 2, 3, 4 and the evidence appendix) first. `Poincare/Global/HamiltonReactionCoreReduction.lean` defines the residual core `HamiltonReactionCore3`; this task removes one of its remaining explicit clauses.

# Task hamilton-chart-density-local-domination

Module: `Poincare/Global/HamiltonChartDensityLocalDomination.lean`. Namespace: `Poincare.HamiltonChartDensityLocalDomination`. Imports: `Poincare.Global.HamiltonReactionCoreReduction`, `Poincare.Global.HausdorffInverseChartGramContinuity` (and whatever landed modules you need).

Objective: prove the local integrable domination clause of `HamiltonReactionCore3` from the all-real-time joint C³ metric entries and compactness alone, so it can be dropped from the core.

Target (probed by the previous worker as `localBoundTarget`; prove it as a theorem with these exact hypotheses and conclusion):

```lean
theorem localBound_of_jointMetricEntries
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    (hjoint : ∀ t x, MetricEntriesJointContDiffAt gt t x 3) :
    let C := compactFiniteExtendedChartCover (n := 3) (M := M)
    ∀ t : ℝ, ∃ s ∈ 𝓝 t,
      ∃ B : (i : Fin C.chartCount) → C.coordinateDomain i → ℝ,
        (∀ i, Integrable (B i) (coordinateLebesgueMeasure (C.coordinateDomain i))) ∧
        (∀ i, ∀ᵐ z ∂(coordinateLebesgueMeasure (C.coordinateDomain i)),
          ∀ τ ∈ s, ‖finiteExtendedChartFrameDensityDerivative C gt τ i z‖ ≤ B i z)
```

with the section variables of `HamiltonReactionCoreReduction.lean` (`M : Type u`, topological, T2, second countable, measurable/Borel, charted, smooth, compact, connected, simply connected). Plausible route: the density derivative is jointly continuous in `(τ, z)` (derive from joint C³ entries through the landed density-variation lemmas `FiniteExtendedChartCover.hasDerivAt_inverseChartDensity` and the Gram-continuity module); the coordinate pieces of `compactFiniteExtendedChartCover` are precompact (check its definition and landed lemmas), so a compact time interval around `t` times the closure of each piece gives a uniform bound, which is integrable on a finite-measure piece. If the pieces are not precompact or the derivative is only measurable, report exactly which lemma is missing.

Then add the corollary: a definition `HamiltonReactionCore3'` (the core without the domination clause) and `theorem hamiltonReactionCore3_of_core'` proving the original `HamiltonReactionCore3` from it, plus `theorem hamiltonConvergencePinchedLimit3_of_hamiltonReactionCore3'` and the universal versions `UniversalHamiltonReactionCoreStatement'` and `universalHamiltonConvergence_of_universalHamiltonReactionCore'`.

Exact stop condition: the displayed theorem compiles with no extra hypothesis, and the reduced core with its endpoint theorem passes the gate. A version that assumes uniform derivative bounds, or a core that re-adds the clause under another name, is only partial; say so.
