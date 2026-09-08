# Worker contract (Lean task)

You are a Lean 4 formalization worker on the Poincaré project (toolchain leanprover/lean4:v4.30.0-rc2, Mathlib pinned). Isolated worktree on branch `worker/hamilton-family-volume-measure-continuity`, cloned `.lake` cache. Rules: NO sorry/admit/axiom/native_decide/opaque (also avoid these words in comments); do not edit existing Lean files or `Poincare.lean`; exactly one new file as named below; no new analytic premises hidden in definitions; commit each verified lemma on the branch; report actual command output to `harness/reports/hamilton-family-volume-measure-continuity_{done|blocked}.md`. Gate: `LEAN_NUM_THREADS=1 lake env lean <file>` exit 0; `rg -n '\b(sorry|admit|axiom|opaque)\b|native_decide' <file>` empty; `#print axioms` of every new declaration exactly `[propext, Classical.choice, Quot.sound]`; `git diff --check`. Verify every name you use by grep in the repo or `.lake/packages/mathlib`. If blocked, display the exact resisting goal and the strongest compiled partial result; never weaken the target silently. Frozen contract files are read-only.

Context: read `HANDOFF.md` top section, `harness/reports/hamilton-compact-family-invariant-continuity_blocked.md` (sections 1-2: two of three continuity clauses are proved in the landed `Poincare/Global/HamiltonCompactFamilyInvariantContinuity.lean`; the weak volume-measure continuity is the open remainder, with the inspected routes), and `harness/reports/reaction-record-decomposition_done.md` sections 3-4. `Poincare/Global/HamiltonReactionCoreReduction.lean` defines `HamiltonReactionCore3`.

# Task hamilton-family-volume-measure-continuity

Module: `Poincare/Global/HamiltonFamilyVolumeMeasureContinuity.lean`. Namespace: `Poincare.HamiltonFamilyVolumeMeasureContinuity`. Imports: `Poincare.Global.HamiltonCompactFamilyInvariantContinuity`, `Poincare.Global.HamiltonReactionCoreReduction`, `Poincare.Global.HausdorffInverseChartGramContinuity`, `Poincare.Global.HausdorffFiniteAtlasRestrictedAreaFormula`, `Poincare.Global.NormalizedFlowCompactMeanEnergyMeasureContinuity` (add what you need).

Objective: prove the remaining clause, weak continuity of the finite volume measure along a metric family with jointly continuous scalar third-jet profiles, then define the jet-form core and its endpoint adapters.

Target 1 (exact remaining goal from the blocked report; section variables as in `HamiltonReactionCoreReduction.lean`):

```lean
theorem continuous_closedMetricFiniteVolumeMeasure_of_thirdJetProfiles_continuous
    (K : Type v) [TopologicalSpace K] [CompactSpace K]
    (metric : K → ClosedSmoothRiemannianMetric 3 M)
    (hjet : ∀ slot : MetricEntryThirdJetSlot 3 M,
      Continuous (fun p : K × ClosedSmoothModel 3 ↦
        metricEntryThirdJetProfile (metric p.1) slot p.2)) :
    Continuous (fun k ↦ closedMetricFiniteVolumeMeasure (metric k))
```

Route: `FiniteMeasure.continuous_iff_forall_continuousMap_continuous_integral` reduces to continuity of `k ↦ ∫ f d(volumeMeasure (metric k))` for every continuous bounded `f`. Use the landed finite genuine chart cover (`compactFiniteExtendedChartCover`) and area formula (`FiniteExtendedChartCover.restrictedInverseChartPullbackHausdorffAreaFormula` / `hausdorffChartDensityEquality`) to write the integral as a finite sum over disjointized coordinate pieces of `∫ (f ∘ inverseChart) · density_k dz`; the density is the square root of the Gram determinant of the metric entries in the chart, which depends continuously on `(k, z)` by hjet (`continuous_inverseChartPullbackVolumeDensity` in `HausdorffInverseChartGramContinuity.lean` is the fixed-metric version; generalize its argument to the parameter). Continuity of the parametrized integral then follows from dominated convergence (`MeasureTheory.continuous_of_dominated` or `continuousAt_of_dominated`) with a dominating function obtained from compactness of `K` times the closure of each coordinate piece (check whether the pieces are precompact; if not, use the bounded-density-on-compact-parameter argument on each piece with its finite Lebesgue measure). If a landed theorem already expresses the volume integral as such a sum, use it; do not re-prove the area formula.

Target 2: define `HamiltonReactionCore3Jet M : Prop` as `HamiltonReactionCore3` with the three continuity clauses replaced by the single hypothesis `∀ slot, Continuous (fun p : K × ClosedSmoothModel 3 ↦ metricEntryThirdJetProfile (metric p.1) slot p.2)`, and prove `hamiltonReactionCore3_of_jet : HamiltonReactionCore3Jet M → HamiltonReactionCore3 M` using Target 1 and the landed `curvatureContinuity_of_thirdJetProfiles_continuous`; then `hamiltonConvergencePinchedLimit3_of_hamiltonReactionCore3Jet`, `UniversalHamiltonReactionCoreJetStatement`, and `universalHamiltonConvergence_of_universalHamiltonReactionCoreJet` (mirror the universal statement shape in `HamiltonReactionCoreReduction.lean`).

Exact stop condition: Target 1 compiles with exactly the displayed hypotheses, and Target 2's core with its endpoint theorems passes the gate. If Target 1 is blocked, land Target 2 conditionally is NOT acceptable; instead report the exact resisting goal and the strongest compiled partial result (for example continuity of each chartwise density integral).
