# Worker contract (Lean task, exploratory)

You are a Lean 4 formalization worker on the Poincaré project (toolchain leanprover/lean4:v4.30.0-rc2, Mathlib pinned). Isolated worktree on branch `worker/closed-ricci-flow-normalization`, cloned `.lake` cache. Rules: NO sorry/admit/axiom/native_decide/opaque (also avoid these words in comments); do not edit existing Lean files or `Poincare.lean`; exactly one new file as named below; no new analytic premises hidden in definitions; commit each verified lemma on the branch; report actual command output to `harness/reports/closed-ricci-flow-normalization_{done|blocked}.md`. Gate: `LEAN_NUM_THREADS=1 lake env lean <file>` exit 0; `rg -n '\b(sorry|admit|axiom|opaque)\b|native_decide' <file>` empty; `#print axioms` of every new declaration exactly `[propext, Classical.choice, Quot.sound]`; `git diff --check`. Verify every name you use by grep in the repo or `.lake/packages/mathlib`. This task is exploratory (class C in the survey): a blocked report displaying the exact resisting statement with the strongest compiled partial lemmas is acceptable; never weaken the target silently. Frozen contract files are read-only.

Context: read `HANDOFF.md` top section and `harness/reports/ricci-flow-existence-interface-survey_done.md` (section 3 Task 8, section 4, Appendix D for the exact definitions `regularRicciFlowGoal`, `normalizedFlowGoal`, `normalizationGoal` and their context) first. Relevant landed modules: `Poincare/Global/NormalizedFlowRescaling.lean`, `MetricRescaleFiniteAtlasIntegrals.lean`, `MetricRescaleFiniteAtlasForwardFlow.lean`, `NormalizedFlow.lean`, `RicciFlow.lean`, `MetricFlowJointRegularity.lean`, `VolumeFinitenessComparison.lean`, `HamiltonReactionCoreReduction.lean` (density integrability from joint regularity), `HamiltonChartDensityLocalDomination.lean`.

# Task closed-ricci-flow-normalization

Module: `Poincare/Global/ClosedRicciFlowNormalization.lean`. Namespace: `Poincare.ClosedRicciFlowNormalization`. Imports: the landed rescaling and finite-atlas modules named above plus `Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus` (add what you need).

Objective: prove that regular (unnormalized) short-time Ricci flows with joint C³ metric entries on the same family produce normalized short-time flows with the same initial metric, i.e. the survey's `normalizationGoal`:

```lean
-- Appendix D definitions, reproduce verbatim in the module (context: M closed smooth 3-manifold with a compatible Borel structure as in Appendix D)
def regularRicciFlowGoal (g₀ : ClosedSmoothRiemannianMetric 3 M) : Prop := ...   -- copy from Appendix D
def normalizedFlowGoal (g₀ : ClosedSmoothRiemannianMetric 3 M) : Prop := ...     -- copy from Appendix D

theorem normalization
    (h : ∀ g₀ : ClosedSmoothRiemannianMetric 3 M, regularRicciFlowGoal g₀) :
    ∀ g₀ : ClosedSmoothRiemannianMetric 3 M, normalizedFlowGoal g₀
```

Route (standard): given the regular flow `gt` on `[0,T)` with joint C³ entries, define the scale `λ(t) := exp((2/3) ∫₀ᵗ r(s) ds)` with `r` the mean scalar curvature of `gt` (continuity of `t ↦ meanScalar (gt t)` along the family must be proved from joint regularity and the landed finite-atlas integral/density results; the mean requires positive finite volume, which the landed volume finiteness and positivity results supply for nonempty `M`), define the new time `τ(t) := ∫₀ᵗ λ(s) ds` (strictly increasing, continuous, with `τ(0) = 0`), and set `ht(τ(t)) := λ(t) • gt t`; prove it is a normalized Ricci flow solution on `[0, S)` with `S := sup` of the reached times (or any positive `S` below it), with `ht 0 = g₀` and joint C³ entries. Use the landed rescaling lemmas (`NormalizedFlowRescaling`, `MetricRescaleFiniteAtlasForwardFlow`) for the scaling behaviour of Ricci, scalar and mean scalar under `c • g` and for the reparametrized derivative; do not set the mean scalar to zero.

Exact stop condition: `normalization` compiles with exactly the displayed statement; or a blocked report displays the exact resisting lemma (for example mean-scalar continuity along the family, reached-time containment, or initial differentiability) with compiled partial lemmas committed.
