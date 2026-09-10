# Hamilton mean-floor reduction: blocked with verified partial results

Date: 2026-09-10. Base: `73b9bb2266283688de5fdafcc9a113f0c99e0873`.
Branch: `worker/hamilton-mean-floor-reduction`.
Proof commits: `5eedb953`, `5916abea`.

The requested infinite-time reduction is blocked by a mathematical obstruction, not a compiler failure. The proposed bounded normalization primitive is **inconsistent** with a jointly C³ forward normalized Ricci flow having positive initial scalar curvature. The new module proves this inconsistency. Defining `HamiltonReactionCore3Init` with that residual would create an uninhabitable core and vacuous endpoint implications, contrary to the worker contract.

Seven proved declarations are delivered in `Poincare/Global/HamiltonMeanFloorReduction.lean`. They establish forward mean continuity, a continuous extension of that mean, a normalization antiderivative with the ordinary derivative at zero, an explicit positive mean profile, positive floors on every compact forward interval, unbounded primitive growth from any uniform mean floor, and the refutation of the proposed bounded-primitive residual. All seven pass the exact foundational dependency check.

Step 1's requested uniform infinite-ray theorem and every Step 2 declaration are intentionally absent. The task's done condition is not met. No existence obligation is discharged. The finite-interval theorem is explicitly named `meanScalar_floor_on_Icc_of_initial_scalar_pos`; its quantifier order is `∀ T ≥ 0, ∃ c > 0`, not `∃ c > 0, ∀ T ≥ 0`. The target has not been silently weakened or renamed.

## 1. Exact obstruction and strongest partial result

Write `r(t) = meanScalar (gt t)`. The normalization primitive in the landed comparison theorem satisfies

```lean
∀ t ∈ Ici (0 : ℝ), HasDerivAt P ((2 / 3 : ℝ) * meanScalar (gt t)) t
```

It integrates `(2/3) * r`, not `r` without the factor. The canonical landed `normalizedMeanScalarPrimitive` is precisely `∫ s in 0..t, (2/3) * meanScalar (gt s)`.

If `c > 0` and `c ≤ r(t)` throughout the ray, the mean value inequality gives

```text
(2/3) * c * t ≤ P(t) - P(0),  for every t ≥ 0.
```

Thus every proposed bound `C` is exceeded, for example at `t = (|C| + 1) / ((2/3)*c)`. This is proved as `normalizationPrimitive_unbounded_of_meanScalar_floor`.

The landed scalar comparison says that initial scalar positivity, scalar evolution and regularity, and bounded increments of `P` give a uniform pointwise positive scalar floor. `le_meanScalar_of_forall_le_scalarAt` transfers that very same numerical floor to the mean. Combining these proved implications yields the new refutation:

```lean
theorem not_exists_bounded_normalizationPrimitive_of_initial_scalar_pos
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    (hflow : ∀ t ∈ Ici (0 : ℝ), ∀ x, IsClosedNormalizedRicciFlowSolutionAt gt t x)
    (hjoint : ∀ t x, MetricEntriesJointContDiffAt gt t x 3)
    (hinit : ∀ x, 0 < (gt 0).scalarAt x) :
    ¬ ∃ (P : ℝ → ℝ) (C : ℝ), Continuous P ∧
      (∀ t ∈ Ici (0 : ℝ), HasDerivAt P ((2 / 3 : ℝ) * meanScalar (gt t)) t) ∧
      ∀ t ∈ Ici (0 : ℝ), P t - P 0 ≤ C
```

All ambient variables are those of `HamiltonReactionCoreFinal.lean`: `M : Type u`, topology, T2, second countability, measurable and Borel structures, the dimension-three charted smooth manifold, compactness, connectedness and simple connectivity. No additional connection regularity instance is assumed in the new declarations.

This refutes the proposed residual under these hypotheses. It does **not** refute the desired uniform mean-floor conclusion from some other analytic argument. The resisting target remains exactly:

```lean
(gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
(hflow : ∀ t ∈ Ici (0 : ℝ), ∀ x, IsClosedNormalizedRicciFlowSolutionAt gt t x)
(hjoint : ∀ t x, MetricEntriesJointContDiffAt gt t x 3)
(hinit : ∀ x, 0 < (gt 0).scalarAt x)
⊢ ∃ c : ℝ, 0 < c ∧ ∀ t : Ici (0 : ℝ), c ≤ meanScalar (gt t.1)
```

No proof of this target without a further viable analytic estimate was found. Its strongest compiled partial version requires no residual hypotheses and provides

```lean
∃ (rho : ℝ) (P : ℝ → ℝ), 0 < rho ∧ Continuous P ∧ P 0 = 0 ∧
  (∀ t ∈ Ici (0 : ℝ), HasDerivAt P ((2 / 3 : ℝ) * meanScalar (gt t)) t) ∧
  ∀ t ∈ Ici (0 : ℝ), (rho / 2) * Real.exp (-P t) ≤ meanScalar (gt t)
```

Consequently, for every fixed `T ≥ 0`, it gives `∃ c > 0, ∀ t ∈ Icc 0 T, c ≤ meanScalar (gt t)`. The proof takes a maximum of the continuous `P` on that compact interval. It claims no maximum on `Ici 0`.

## 2. Residual classification and regularity audit

Here A means derived by proved repository material or the new module; B means an analytic estimate still needed for a viable route; C means an implication not established by this survey. The rejected boundedness residual is identified separately as refuted, rather than misleadingly classified as an attainable missing estimate.

| Input or proposed residual | Classification | Actual status |
| --- | --- | --- |
| Positive numerical initial scalar floor | A | `exists_pos_scalar_floor_of_forall_scalarAt_pos`, from positive scalar on the compact initial slice. |
| Spatial C² time variation | A | `timeVariationExtContMDiffAt_two_of_metricEntriesJointContDiffAt_three`. |
| Spatial C² scalar on each forward slice | A | `scalarAt_contMDiffAt_two_of_normalizedRicciFlow`, using the preceding time-variation result. |
| Global Lichnerowicz regularity | A | `globalLichnerowiczAssemblyRegularity_of_jointMetricEntriesThree`. This provides time differentiability, nearby metric-flow regularity, mixed derivative commutation and C² time-variation entries. |
| Normalized Hamilton scalar evolution on the forward ray | A | `satisfiesNormalizedHamiltonScalarEvolutionAt_of_normalizedFlow_of_globalLichnerowicz`, applied separately at each nonnegative time. No negative-time flow equation is introduced. |
| Joint scalar continuity on all real times | A | `continuousAt_scalarAt_joint_of_metricEntriesJointContDiffAt_three` applied to global joint C³ entries. |
| C¹ Levi-Civita connection | A | The registered theorem `closedLeviCivitaConnection_contMDiff` in `Global/LeviCivitaRegularity.lean` supplies the instance. The new signatures have no additional connection premise. |
| Mean-scalar continuity on `Ici 0` | A, newly proved | `continuousOn_meanScalar_of_normalizedRicciFlow`. |
| Continuous primitive and its ordinary derivative, including zero | A, newly proved | `exists_normalizationPrimitive_of_normalizedRicciFlow`. |
| `∃ C, ∀ t ≥ 0, P t - P 0 ≤ C` | Refuted in this setting | The seventh theorem proves no continuous primitive can have this property under the supplied positive-initial-scalar flow hypotheses. It cannot be retained as a useful B residual. |
| An alternative global estimate implying a positive mean floor | B | Not supplied by the scalar exponential comparison. S9's integrated energy domination is a possible different route, with its own hypotheses. |
| Deriving S9 energy domination from this task's hypotheses | C | No such implication was found or claimed. |

The key new continuity argument avoids any extra hypothesis about differentiating moving integrals. Fix a point `x`. On the forward ray, the normalized equation gives

```text
meanScalar(gt t) = scalarAt(gt t, x) + (1/2) * traceMetricVariationAt(gt t, timeDerivAt gt t, x).
```

The right side defines a continuous function on all real times, by joint scalar continuity and `HamiltonChartDensityLocalDomination.continuous_trace_timeDeriv`. It agrees with the actual mean only where the flow equation is assumed. Integrating this extension constructs an ordinary antiderivative at zero. On every forward integration interval its integrand is exactly `(2/3) * meanScalar`. No assertion about negative-time mean curvature is made.

For comparison, `ClosedRicciFlowNormalization.continuousOn_meanScalar_of_ricciFlow` is landed for an **unnormalized** flow on `Icc 0 U`, using dominated moving integrals. The new theorem is the normalized analogue on the whole forward ray, under this task's stronger all-time joint regularity. Also landed is `continuous_meanScalar_of_movingTotalScalarVolume_derivatives`, which assumes those derivative identities; they are unnecessary for the new continuity proof.

The raw unnormalized `satisfiesHamiltonScalarEvolutionAt_of_ricciFlow` has genuine hypotheses: nearby Ricci-flow and extension regularity, metric-flow regularity, time differentiability, metric-raise derivative, divergence and contraction assemblies, trace and scalar gradient regularity, scalar C²/extensional derivatives, and Ricci differentiability/divergence differentiability. The stronger landed `satisfiesHamiltonScalarEvolutionAt_of_ricciFlow_joint_metric_entries_three` reduces this to the flow equation at the time slice plus joint C³ entries, with the connection instance. `satisfiesRicciEvolutionAt_of_ricciFlow_traceSecondRegularity` separately requires a delta-Gamma bridge, mixed and second tensor derivatives, nearby unnormalized flow and extension regularity, scalar C² and further trace regularity; its complete signature is recorded below. Neither raw unnormalized theorem can be applied merely by substituting the normalized predicate. The implemented proof uses the normalized Lichnerowicz producer.

### Why the proposed weaker bounds do not fix the primitive

A nonpositive mean derivative, a bounded mean derivative, or a uniform upper bound on the mean does not imply a uniformly bounded primitive on an infinite interval. Already the scalar track `r(t)=1` has derivative zero and upper bound one, while its primitive is `(2/3)t`. This is a scalar calculus counterexample to those proposed inference rules, not a newly formalized geometric example.

S9 proves a **nonnegative** mean derivative under the additional moving scalar/volume derivative identities and

```lean
∀ t : Ici (0 : ℝ),
  normalizedFlowScalarVarianceTrack gt t.1 ≤
    6 * normalizedFlowTracelessRicciEnergyTrack gt t.1
```

The exact numerator is `2*E - (1/3)*V`. Its sign is not implied by initial scalar positivity. If S9 and the differentiability/continuity needed for monotonicity are supplied, positive initial mean can instead yield a uniform mean floor directly. That would be a different, potentially viable reduction. It does not bound the normalization primitive; with a positive mean floor it forces that primitive to grow. This attempt does not install S9 hypotheses under another name or claim to derive them.

## 3. Reaction domination survey

The two named preservation theorems are proved in the repository, not Mathlib. `hamilton_pinching_preserved` needs joint quotient continuity, spatial C² quotient regularity, and the actual quotient evolution predicate on every point of a compact interval. It concludes that the maximum quotient does not increase. `hamilton_eigenvalue_pinching_floor_preserved` additionally needs scalar positivity on that interval and initial eigenvalue bounds `ε * scalar ≤ μᵢ`, with `ε ≤ 1/3`. Its conclusion is `(2*ε - 1/3) * scalar ≤ μᵢ`, not the identical initial factor. For example, initial `1/4` yields `1/6`; this exact use is landed in `hamilton_forward_preserved_and_improved_pinching_of_global_one_fourth_initial_floor`.

These outputs do not state the uniform absolute decay rate required by the core:

```lean
∃ rate : ℝ, 0 < rate ∧ ∀ t ∈ Ici (0 : ℝ), ∀ x : M,
  normalizedTracelessRicciEvolutionReactionAt (gt t) x ≤
    -rate * (gt t).tracelessRicciNormSqAt x
```

A relevant landed algebraic reduction is

```lean
normalizedTracelessRicciEvolutionReactionAt_le_neg_rate_mul_of_cubic_domination
```

It asks, at each slice and point, for

```lean
(g.pinchingTracelessRicciReactionTrace3At x
    (g.pinchingRicciNormReactionMotionTraceCubicAt x)) ≤
  ((4 / 3 : ℝ) * meanScalar g - rate) * g.tracelessRicciNormSqAt x
```

and proves the desired reaction inequality, using the landed gradient estimate. Thus the algebraic conversion is A. A uniform positive rate and a sufficiently strong cubic bound over the ray remain B inputs; an implication from a chosen initial pinching condition through the two preservation theorems to precisely this bound is C in this survey. No such producer was found in the reaction/pinching searches. The absence finding is scoped to those searches, not a proof that no equivalent declaration exists. The survey does not implement a reaction reduction or claim initial pinching alone supplies uniform reaction domination.

## 4. Provenance, validation and handoff

The named task, README, HANDOFF top section, project map, AGENTS, Harness v2 specification, mission, prior reports and direct source/import chains were inspected. Initial `git status --short --branch` was `## worker/hamilton-mean-floor-reduction`; HEAD was the base above, and the worktree inventory confirmed isolation from main and the parallel Schauder survey worktree. The mission's internal historical base differs from live HEAD, so live declarations and the compiler determined this report.

Only the one authorized new Lean module and this report are changed. The task-specific branch and file scope override the general codex-branch and HANDOFF-edit instructions. Existing Lean sources, `Poincare.lean`, frozen contracts, audits, missions, ledgers and HANDOFF remain unchanged. There was no merge or acceptance action and no full or overlapping build.

Verification commands were run with `LEAN_NUM_THREADS=1`. Both direct module compilations exited zero. No compiler error occurred. Lean reported only two unused-section-variable warnings, for the extension and primitive-growth theorems; the requested ambient section context was retained. Each of seven new declarations printed exactly `[propext, Classical.choice, Quot.sound]`, also checked by a parser. The forbidden-token search produced no output and exited 1, the expected no-match status. `git diff --check` exited zero. The source was committed after the corresponding checks, then the refutation was added and separately checked and committed.

Repository-versus-Mathlib classification: geometric comparison, scalar/mean integration, Lichnerowicz assembly, normalization, connection regularity and pinching results are repository theorems. The FTC and convex mean-value inequality are pinned Mathlib results. A viable infinite-ray initial-scalar mean-floor producer, the requested Init core and its universal endpoint reductions are absent from this deliverable. The compact-interval result is not substituted for them.

Every Lean probe from this attempt is reproduced below with its actual compiler output, including both direct compilations and both module-wide dependency probes. Scratch probe files and raw logs are retained under `/tmp/hamilton-mean-floor-reduction`; their contents are embedded here for durable evidence. No failed Lean attempt was discarded. A few exploratory reads guessed nonexistent legacy metric filenames; subsequent repository search located the actual regularity source at `Poincare/Global/LeviCivitaRegularity.lean`. No theorem claim relies on those failed filename guesses.

First action for the orchestrator:

```sh
git diff 73b9bb2266283688de5fdafcc9a113f0c99e0873..5916abea -- Poincare/Global/HamiltonMeanFloorReduction.lean
```

Independently rerun the focused gate, review the refutation, and revise the task's bounded-primitive route before dispatching an Init-core implementation. A next analytic task could target S9's integrated variance/energy inequality and the precise mean derivative prerequisites. It should retain the frozen final core and explicitly prove any replacement estimate.

## Probe signatures

Command: `LEAN_NUM_THREADS=1 lake env lean /tmp/hamilton-mean-floor-reduction/signatures.lean`.

```lean
import Poincare.Global.HamiltonReactionCoreFinal
import Poincare.Global.NormalizedFlowScalarLowerProfile
import Poincare.Global.MetricFlowJointScalarContinuity
import Poincare.Global.ClosedRicciFlowNormalization
import Poincare.Global.NormalizedFlowForwardFiniteTimePositiveEinsteinMeanScalarEnergyDomination
open Poincare
#check exists_uniform_normalizedFlow_scalar_lower_of_initial_scalar_pos_of_normalizationPrimitive_bddAbove
#check normalizedFlow_scalarAt_gt_exponential_normalizationPrimitive_Ici
#check le_meanScalar_of_forall_le_scalarAt
#check meanScalar_pos_of_forall_scalarAt_ge
#check satisfiesNormalizedHamiltonScalarEvolutionAt_of_normalizedFlow_of_globalLichnerowicz
#check globalLichnerowiczAssemblyRegularity_of_jointMetricEntriesThree
#check scalarAt_contMDiffAt_two_of_normalizedRicciFlow
#check timeVariationExtContMDiffAt_two_of_metricEntriesJointContDiffAt_three
#check continuousAt_scalarAt_joint_of_metricEntriesJointContDiffAt_three
#check HamiltonChartDensityLocalDomination.continuous_trace_timeDeriv
#check traceMetricVariationAt_timeDeriv_of_isClosedNormalizedRicciFlowSolutionAt
#check satisfiesHamiltonScalarEvolutionAt_of_ricciFlow
#check satisfiesRicciEvolutionAt_of_ricciFlow_traceSecondRegularity
#check ClosedRicciFlowNormalization.continuousOn_meanScalar_of_ricciFlow
#check hamilton_pinching_preserved
#check hamilton_eigenvalue_pinching_floor_preserved
#check meanScalar_deriv_nonneg_of_normalizedFlow_Ici_of_scalarVarianceTrack_le_six_tracelessRicciEnergyTrack
#check normalizedTracelessRicciEvolutionReactionAt_le_neg_rate_mul_of_cubic_domination
#check Convex.mul_sub_le_image_sub_of_le_deriv
#check intervalIntegral.integral_hasDerivAt_right
#check intervalIntegral.differentiable_integral_of_continuous
```

Actual output:

```text
Poincare.exists_uniform_normalizedFlow_scalar_lower_of_initial_scalar_pos_of_normalizationPrimitive_bddAbove.{u}
  {M : Type u} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [CompactSpace M] [ConnectedSpace M]
  [MeasurableSpace M] [BorelSpace M] [ChartedSpace (ClosedSmoothModel 3) M]
  [IsManifold (closedSmoothModelWithCorners 3) (↑⊤) M] [Nonempty M] {gt : ℝ → ClosedSmoothRiemannianMetric 3 M}
  {t0 C : ℝ} [∀ (s : ℝ), (gt s).leviCivita.ContMDiffCovariantDerivative 1]
  (hScalarContinuous : Continuous ↿fun tau x => (gt (t0 + tau)).scalarAt x)
  (hScalarEvolution : ∀ tau ∈ Set.Ici 0, ∀ (x : M), SatisfiesNormalizedHamiltonScalarEvolutionAt gt (t0 + tau) x)
  (hScalarTwo :
    ∀ tau ∈ Set.Ici 0,
      ∀ (x : M),
        ContMDiffAt (closedSmoothModelWithCorners 3) (modelWithCornersSelf ℝ ℝ) 2 (fun y => (gt (t0 + tau)).scalarAt y)
          x)
  (normalizationPrimitive : ℝ → ℝ) (hPrimitiveContinuous : Continuous normalizationPrimitive)
  (hPrimitiveDerivative : ∀ tau ∈ Set.Ici 0, HasDerivAt normalizationPrimitive (2 / 3 * meanScalar (gt (t0 + tau))) tau)
  (hPrimitiveUpper : ∀ tau ∈ Set.Ici 0, normalizationPrimitive tau - normalizationPrimitive 0 ≤ C)
  (hInitialPos : ∀ (x : M), 0 < (gt t0).scalarAt x) :
  ∃ rhoFloor, 0 < rhoFloor ∧ ∀ tau ∈ Set.Ici 0, ∀ (x : M), rhoFloor ≤ (gt (t0 + tau)).scalarAt x
Poincare.normalizedFlow_scalarAt_gt_exponential_normalizationPrimitive_Ici.{u} {M : Type u} [TopologicalSpace M]
  [T2Space M] [SecondCountableTopology M] [CompactSpace M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (ClosedSmoothModel 3) M] [IsManifold (closedSmoothModelWithCorners 3) (↑⊤) M] [Nonempty M]
  {gt : ℝ → ClosedSmoothRiemannianMetric 3 M} {t0 rho : ℝ} [∀ (s : ℝ), (gt s).leviCivita.ContMDiffCovariantDerivative 1]
  (hrho : 0 < rho) (hScalarContinuous : Continuous ↿fun tau x => (gt (t0 + tau)).scalarAt x)
  (hScalarEvolution : ∀ tau ∈ Set.Ici 0, ∀ (x : M), SatisfiesNormalizedHamiltonScalarEvolutionAt gt (t0 + tau) x)
  (hScalarTwo :
    ∀ tau ∈ Set.Ici 0,
      ∀ (x : M),
        ContMDiffAt (closedSmoothModelWithCorners 3) (modelWithCornersSelf ℝ ℝ) 2 (fun y => (gt (t0 + tau)).scalarAt y)
          x)
  (normalizationPrimitive : ℝ → ℝ) (hPrimitiveContinuous : Continuous normalizationPrimitive)
  (hPrimitiveDerivative : ∀ tau ∈ Set.Ici 0, HasDerivAt normalizationPrimitive (2 / 3 * meanScalar (gt (t0 + tau))) tau)
  (hInitial : ∀ (x : M), rho ≤ (gt t0).scalarAt x) (tau : ℝ) :
  tau ∈ Set.Ici 0 →
    ∀ (x : M),
      rho / 2 * Real.exp (-(normalizationPrimitive tau - normalizationPrimitive 0)) < (gt (t0 + tau)).scalarAt x
Poincare.le_meanScalar_of_forall_le_scalarAt.{u} {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] [ChartedSpace (ClosedSmoothModel n) M]
  [IsManifold (closedSmoothModelWithCorners n) (↑⊤) M] [Nonempty M] (g : ClosedSmoothRiemannianMetric n M) (c : ℝ)
  (hlower : ∀ (x : M), c ≤ g.scalarAt x) : c ≤ meanScalar g
Poincare.meanScalar_pos_of_forall_scalarAt_ge.{u} {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] [ChartedSpace (ClosedSmoothModel n) M]
  [IsManifold (closedSmoothModelWithCorners n) (↑⊤) M] [Nonempty M] (g : ClosedSmoothRiemannianMetric n M) {c : ℝ}
  (hc : 0 < c) (hlower : ∀ (x : M), c ≤ g.scalarAt x) : 0 < meanScalar g
Poincare.satisfiesNormalizedHamiltonScalarEvolutionAt_of_normalizedFlow_of_globalLichnerowicz.{u} {M : Type u}
  [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [CompactSpace M] [ConnectedSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ClosedSmoothModel 3) M] [IsManifold (closedSmoothModelWithCorners 3) (↑⊤) M]
  [Nonempty M] {gt : ℝ → ClosedSmoothRiemannianMetric 3 M} {t : ℝ} {x : M}
  [∀ (s : ℝ), (gt s).leviCivita.ContMDiffCovariantDerivative 1]
  (hFlow : ∀ (y : M), IsClosedNormalizedRicciFlowSolutionAt gt t y)
  (hLichnerowicz : GlobalLichnerowiczAssemblyRegularity gt) : SatisfiesNormalizedHamiltonScalarEvolutionAt gt t x
Poincare.globalLichnerowiczAssemblyRegularity_of_jointMetricEntriesThree.{u} {n : ℕ} {M : Type u} [TopologicalSpace M]
  [T2Space M] [ChartedSpace (ClosedSmoothModel n) M] [IsManifold (closedSmoothModelWithCorners n) (↑⊤) M]
  {gt : ℝ → ClosedSmoothRiemannianMetric n M} (hJoint : ∀ (t : ℝ) (y : M), MetricEntriesJointContDiffAt gt t y 3) :
  GlobalLichnerowiczAssemblyRegularity gt
Poincare.scalarAt_contMDiffAt_two_of_normalizedRicciFlow.{u} {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [CompactSpace M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] [ChartedSpace (ClosedSmoothModel n) M]
  [IsManifold (closedSmoothModelWithCorners n) (↑⊤) M] {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ}
  (hFlow : ∀ (y : M), IsClosedNormalizedRicciFlowSolutionAt gt t₀ y)
  (hEntries : ∀ (y : M), TimeVariationExtContMDiffAt gt t₀ y 2) (x : M) :
  ContMDiffAt (closedSmoothModelWithCorners n) (modelWithCornersSelf ℝ ℝ) 2 (fun y => (gt t₀).scalarAt y) x
Poincare.timeVariationExtContMDiffAt_two_of_metricEntriesJointContDiffAt_three.{u} {n : ℕ} {M : Type u}
  [TopologicalSpace M] [T2Space M] [ChartedSpace (ClosedSmoothModel n) M]
  [IsManifold (closedSmoothModelWithCorners n) (↑⊤) M] {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
  (hJoint : MetricEntriesJointContDiffAt gt t₀ x 3) : TimeVariationExtContMDiffAt gt t₀ x 2
Poincare.continuousAt_scalarAt_joint_of_metricEntriesJointContDiffAt_three.{u} {n : ℕ} {M : Type u} [TopologicalSpace M]
  [T2Space M] [ChartedSpace (ClosedSmoothModel n) M] [IsManifold (closedSmoothModelWithCorners n) (↑⊤) M]
  {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M} (hJoint : MetricEntriesJointContDiffAt gt t₀ x 3) :
  ContinuousAt (fun p => (gt p.1).scalarAt p.2) (t₀, x)
Poincare.HamiltonChartDensityLocalDomination.continuous_trace_timeDeriv.{u} {n : ℕ} {M : Type u} [TopologicalSpace M]
  [T2Space M] [ChartedSpace (ClosedSmoothModel n) M] [IsManifold (closedSmoothModelWithCorners n) (↑⊤) M]
  (gt : ℝ → ClosedSmoothRiemannianMetric n M) (hjoint : ∀ (t : ℝ) (x : M), MetricEntriesJointContDiffAt gt t x 3) :
  Continuous fun p => traceMetricVariationAt (gt p.1) (timeDerivAt gt p.1) p.2
Poincare.traceMetricVariationAt_timeDeriv_of_isClosedNormalizedRicciFlowSolutionAt.{u} {n : ℕ} {M : Type u}
  [TopologicalSpace M] [T2Space M] [CompactSpace M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (ClosedSmoothModel n) M] [IsManifold (closedSmoothModelWithCorners n) (↑⊤) M]
  {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M} (hflow : IsClosedNormalizedRicciFlowSolutionAt gt t₀ x)
  (hn : ↑n ≠ 0) : traceMetricVariationAt (gt t₀) (timeDerivAt gt t₀) x = 2 * (meanScalar (gt t₀) - (gt t₀).scalarAt x)
Poincare.satisfiesHamiltonScalarEvolutionAt_of_ricciFlow.{u} {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (ClosedSmoothModel n) M] [IsManifold (closedSmoothModelWithCorners n) (↑⊤) M]
  {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
  [∀ (t : ℝ), (gt t).leviCivita.ContMDiffCovariantDerivative 1]
  {raise' :
    (TangentSpace (closedSmoothModelWithCorners n) x →L[ℝ] ℝ) →L[ℝ] TangentSpace (closedSmoothModelWithCorners n) x}
  (hNearFlow : ∀ᶠ (y : M) in nhds x, IsClosedRicciFlowSolutionAt gt t₀ y ∧ ClosedRicciFlowExtensionRegularAt gt t₀ y)
  (hreg : MetricFlowRegularAt gt t₀ x) (hgt : TimeDifferentiableAt gt t₀ x)
  (hRaise : HasDerivAt (fun t => (gt t).metricRaiseContinuousAt x) raise' t₀)
  (hDiv : DeltaGammaDivergenceTraceAssemblyAt gt t₀ x) (hCon : DeltaGammaContractionTraceAssemblyAt gt t₀ x)
  (hTraceGrad :
    have g := gt t₀;
    have H := timeDerivAt gt t₀;
    have f := fun y => traceMetricVariationAt g H y;
    (MDiffAt fun x => ⟨x, g.gradient f x⟩) x)
  (hNegScalarGrad :
    let g := gt t₀;
    have f := fun y => -2 * g.scalarAt y;
    (MDiffAt fun x => ⟨x, g.gradient f x⟩) x)
  (hScalarDiff : ∀ (y : M), (MDiffAt fun z => (gt t₀).scalarAt z) y)
  (hScalar₂ : ContMDiffAt (closedSmoothModelWithCorners n) (modelWithCornersSelf ℝ ℝ) 2 (fun y => (gt t₀).scalarAt y) x)
  (hScalarExt₂ :
    ∀ (w : TangentSpace (closedSmoothModelWithCorners n) x),
      (MDiffAt fun y => (extDerivFun (fun z => (gt t₀).scalarAt z) y) (FiberBundle.extend (ClosedSmoothModel n) w y)) x)
  (hRicDiff : ∀ (y : M), CovTensor2ExtDifferentiableAt (ricciVariationField (gt t₀)) y)
  (hRicDivDiff :
    ∀ (w : TangentSpace (closedSmoothModelWithCorners n) x),
      (MDiffAt fun y =>
          tensorDivergenceOneFormAt (gt t₀) (ricciVariationField (gt t₀)) y
            (FiberBundle.extend (ClosedSmoothModel n) w y))
        x) :
  SatisfiesHamiltonScalarEvolutionAt gt t₀ x
Poincare.satisfiesRicciEvolutionAt_of_ricciFlow_traceSecondRegularity.{u} {n : ℕ} {M : Type u} [TopologicalSpace M]
  [T2Space M] [ChartedSpace (ClosedSmoothModel n) M] [IsManifold (closedSmoothModelWithCorners n) (↑⊤) M]
  {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
  [∀ (t : ℝ), (gt t).leviCivita.ContMDiffCovariantDerivative 1] (hreg : MetricFlowRegularAt gt t₀ x)
  (hgt : ∀ (y : M), TimeDifferentiableAt gt t₀ y)
  (hExt :
    ∀ (a b c : TangentSpace (closedSmoothModelWithCorners n) x),
      HasDerivAt
        (fun t =>
          (extDerivFun
              (fun y =>
                (((gt t).inner y) (FiberBundle.extend (ClosedSmoothModel n) b y))
                  (FiberBundle.extend (ClosedSmoothModel n) c y))
              x)
            a)
        ((extDerivFun
            (fun y =>
              timeDerivAt gt t₀ y (FiberBundle.extend (ClosedSmoothModel n) b y)
                (FiberBundle.extend (ClosedSmoothModel n) c y))
            x)
          a)
        t₀)
  (hNear :
    ∀ᶠ (y : M) in nhds x,
      MetricFlowRegularAt gt t₀ y ∧
        ∀ (a b c : TangentSpace (closedSmoothModelWithCorners n) y),
          HasDerivAt
            (fun t =>
              (extDerivFun
                  (fun z =>
                    (((gt t).inner z) (FiberBundle.extend (ClosedSmoothModel n) b z))
                      (FiberBundle.extend (ClosedSmoothModel n) c z))
                  y)
                a)
            ((extDerivFun
                (fun z =>
                  timeDerivAt gt t₀ z (FiberBundle.extend (ClosedSmoothModel n) b z)
                    (FiberBundle.extend (ClosedSmoothModel n) c z))
                y)
              a)
            t₀)
  (hBridge : DeltaGammaEntryDerivativeBridgeAt gt t₀ x)
  (hSecond : CovTensor2DerivExtDifferentiableAt (gt t₀) (timeDerivAt gt t₀) x)
  (hFlowNear : ∀ᶠ (y : M) in nhds x, IsClosedRicciFlowSolutionAt gt t₀ y ∧ ClosedRicciFlowExtensionRegularAt gt t₀ y)
  (hRicSecond : CovTensor2DerivExtDifferentiableAt (gt t₀) (ricciVariationField (gt t₀)) x)
  (hRicC2 : CovTensor2ExtContMDiffAt (ricciVariationField (gt t₀)) x 2)
  (hScalar₂ : ContMDiffAt (closedSmoothModelWithCorners n) (modelWithCornersSelf ℝ ℝ) 2 (fun y => (gt t₀).scalarAt y) x)
  (hScalarExt₂ :
    ∀ (w : TangentSpace (closedSmoothModelWithCorners n) x),
      (MDiffAt fun y => (extDerivFun (fun z => (gt t₀).scalarAt z) y) (FiberBundle.extend (ClosedSmoothModel n) w y))
        x) :
  SatisfiesRicciEvolutionAt gt t₀ x
Poincare.ClosedRicciFlowNormalization.continuousOn_meanScalar_of_ricciFlow.{u} {M : Type u} [TopologicalSpace M]
  [T2Space M] [ChartedSpace (ClosedSmoothModel 3) M] [IsManifold (closedSmoothModelWithCorners 3) (↑⊤) M]
  [CompactSpace M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
  {U : ℝ} (hU : 0 ≤ U) (hflow : ∀ t ∈ Set.Icc 0 U, ∀ (x : M), IsClosedRicciFlowSolutionAt gt t x)
  (hjoint : ∀ t ∈ Set.Icc 0 U, ∀ (x : M), MetricEntriesJointContDiffAt gt t x 3) :
  ContinuousOn (fun t => meanScalar (gt t)) (Set.Icc 0 U)
Poincare.hamilton_pinching_preserved.{u} {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (ClosedSmoothModel n) M] [IsManifold (closedSmoothModelWithCorners n) (↑⊤) M] [CompactSpace M]
  [Nonempty M] {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ T : ℝ}
  [∀ (t : ℝ), (gt t).leviCivita.ContMDiffCovariantDerivative 1] (hn : n = 3) (hT0 : 0 ≤ T)
  (hQ_cont : Continuous ↿fun τ x => (gt (t₀ + τ)).pinchingQuotientAt x)
  (hQ₂ :
    ∀ τ ∈ Set.Icc 0 T,
      ∀ (x : M),
        ContMDiffAt (closedSmoothModelWithCorners n) (modelWithCornersSelf ℝ ℝ) 2
          (fun y => (gt (t₀ + τ)).pinchingQuotientAt y) x)
  (hEvol :
    ∀ τ ∈ Set.Icc 0 T,
      ∀ (x : M),
        ClosedSmoothRiemannianMetric.SatisfiesPinchingQuotientEvolutionAt gt (t₀ + τ) x
          ((gt (t₀ + τ)).pinchingRicciNormReactionMotionTraceCubicAt x))
  (τ : ℝ) : τ ∈ Set.Icc 0 T → pinchingMaximumTrack gt t₀ τ ≤ pinchingMaximumTrack gt t₀ 0
Poincare.hamilton_eigenvalue_pinching_floor_preserved.{u} {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (ClosedSmoothModel n) M] [IsManifold (closedSmoothModelWithCorners n) (↑⊤) M] [CompactSpace M]
  [Nonempty M] {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ T ε : ℝ}
  [∀ (t : ℝ), (gt t).leviCivita.ContMDiffCovariantDerivative 1] (hn : n = 3) (hεle : ε ≤ 1 / 3) (hT0 : 0 ≤ T)
  (hQ_cont : Continuous ↿fun τ x => (gt (t₀ + τ)).pinchingQuotientAt x)
  (hQ₂ :
    ∀ τ ∈ Set.Icc 0 T,
      ∀ (x : M),
        ContMDiffAt (closedSmoothModelWithCorners n) (modelWithCornersSelf ℝ ℝ) 2
          (fun y => (gt (t₀ + τ)).pinchingQuotientAt y) x)
  (hEvol :
    ∀ τ ∈ Set.Icc 0 T,
      ∀ (x : M),
        ClosedSmoothRiemannianMetric.SatisfiesPinchingQuotientEvolutionAt gt (t₀ + τ) x
          ((gt (t₀ + τ)).pinchingRicciNormReactionMotionTraceCubicAt x))
  (hRpos : ∀ τ ∈ Set.Icc 0 T, ∀ (x : M), 0 < (gt (t₀ + τ)).scalarAt x)
  (hInitPin :
    ∀ (x : M) (b : Module.Basis (Fin 3) ℝ (TangentSpace (closedSmoothModelWithCorners n) x)) (μ : Fin 3 → ℝ),
      (∀ (i : Fin 3), ((gt t₀).ricciEndoAt x) (b i) = μ i • b i) → ∀ (i : Fin 3), ε * (gt t₀).scalarAt x ≤ μ i)
  (τ : ℝ) :
  τ ∈ Set.Icc 0 T →
    ∀ (x : M) (b : Module.Basis (Fin 3) ℝ (TangentSpace (closedSmoothModelWithCorners n) x)) (μ : Fin 3 → ℝ),
      (∀ (i : Fin 3), ((gt (t₀ + τ)).ricciEndoAt x) (b i) = μ i • b i) →
        ∀ (i : Fin 3), (2 * ε - 1 / 3) * (gt (t₀ + τ)).scalarAt x ≤ μ i
Poincare.meanScalar_deriv_nonneg_of_normalizedFlow_Ici_of_scalarVarianceTrack_le_six_tracelessRicciEnergyTrack.{u}
  {M : Type u} [TopologicalSpace M] [T2Space M] [CompactSpace M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (ClosedSmoothModel 3) M] [IsManifold (closedSmoothModelWithCorners 3) (↑⊤) M] [Nonempty M]
  (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
  (hFlow : ∀ (t : ↑(Set.Ici 0)) (x : M), IsClosedNormalizedRicciFlowSolutionAt gt (↑t) x)
  (hDifferentiateMovingTotalScalar :
    ∀ (t : ↑(Set.Ici 0)), HasDerivAt (fun s => totalScalar (gt s)) (normalizedMeanScalarEnergyNumerator (gt ↑t)) ↑t)
  (hDifferentiateMovingVolume :
    ∀ (t : ↑(Set.Ici 0)),
      HasDerivAt (fun s => totalVolume (gt s)) (totalVolumeFirstVariation (gt ↑t) (timeDerivAt gt ↑t)) ↑t)
  (hEnergyDomination :
    ∀ (t : ↑(Set.Ici 0)), normalizedFlowScalarVarianceTrack gt ↑t ≤ 6 * normalizedFlowTracelessRicciEnergyTrack gt ↑t)
  (t : ↑(Set.Ici 0)) : 0 ≤ deriv (fun s => meanScalar (gt s)) ↑t
Poincare.normalizedTracelessRicciEvolutionReactionAt_le_neg_rate_mul_of_cubic_domination.{u} {M : Type u}
  [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [CompactSpace M] [ConnectedSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ClosedSmoothModel 3) M] [IsManifold (closedSmoothModelWithCorners 3) (↑⊤) M]
  (g : ClosedSmoothRiemannianMetric 3 M) (x : M) (rate : ℝ)
  (hCubic :
    g.pinchingTracelessRicciReactionTrace3At x (g.pinchingRicciNormReactionMotionTraceCubicAt x) ≤
      (4 / 3 * meanScalar g - rate) * g.tracelessRicciNormSqAt x) :
  normalizedTracelessRicciEvolutionReactionAt g x ≤ -rate * g.tracelessRicciNormSqAt x
Convex.mul_sub_le_image_sub_of_le_deriv {D : Set ℝ} (hD : Convex ℝ D) {f : ℝ → ℝ} (hf : ContinuousOn f D)
  (hf' : DifferentiableOn ℝ f (interior D)) {C : ℝ} (hf'_ge : ∀ x ∈ interior D, C ≤ deriv f x) (x : ℝ) :
  x ∈ D → ∀ y ∈ D, x ≤ y → C * (y - x) ≤ f y - f x
intervalIntegral.integral_hasDerivAt_right.{u_3} {E : Type u_3} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] {f : ℝ → E} {a b : ℝ} (hf : IntervalIntegrable f MeasureTheory.volume a b)
  (hmeas : StronglyMeasurableAtFilter f (nhds b) MeasureTheory.volume) (hb : ContinuousAt f b) :
  HasDerivAt (fun u => ∫ (x : ℝ) in a..u, f x) (f b) b
intervalIntegral.differentiable_integral_of_continuous.{u_3} {E : Type u_3} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] {f : ℝ → E} {a : ℝ} (hcont : Continuous f) : Differentiable ℝ fun u => ∫ (x : ℝ) in a..u, f x

EXIT_CODE=0
```

## Probe support-02

Command: `LEAN_NUM_THREADS=1 lake env lean /tmp/hamilton-mean-floor-reduction/support-02.lean`.

```lean
import Poincare.Global.HamiltonReactionCoreFinal
import Poincare.Global.NormalizedFlowScalarLowerProfile
import Poincare.Global.MetricFlowJointScalarContinuity
import Poincare.Global.ClosedRicciFlowNormalization
import Poincare.Global.NormalizedFlowForwardFiniteTimePositiveEinsteinMeanScalarEnergyDomination
import Poincare.Global.NormalizedFlowFiniteTimePositiveEinsteinMeanScalarInitialScalarProfile
import Poincare.Global.NormalizedFlowFiniteTimeHamiltonPinching
open Poincare
#check satisfiesHamiltonScalarEvolutionAt_of_ricciFlow_joint_metric_entries_three
#check normalizedMeanScalarPrimitive
#check continuous_normalizedMeanScalarPrimitive
#check hasDerivAt_normalizedMeanScalarPrimitive
#check hamilton_forward_preserved_and_improved_pinching_of_global_one_fourth_initial_floor
```

Actual output:

```text
Poincare.satisfiesHamiltonScalarEvolutionAt_of_ricciFlow_joint_metric_entries_three.{u} {n : ℕ} {M : Type u}
  [TopologicalSpace M] [T2Space M] [ChartedSpace (ClosedSmoothModel n) M]
  [IsManifold (closedSmoothModelWithCorners n) (↑⊤) M] {gt : ℝ → ClosedSmoothRiemannianMetric n M} {t₀ : ℝ} {x : M}
  [∀ (t : ℝ), (gt t).leviCivita.ContMDiffCovariantDerivative 1] (hFlow : ∀ (y : M), IsClosedRicciFlowSolutionAt gt t₀ y)
  (hJoint : ∀ (y : M), MetricEntriesJointContDiffAt gt t₀ y 3) : SatisfiesHamiltonScalarEvolutionAt gt t₀ x
Poincare.normalizedMeanScalarPrimitive.{u} {M : Type u} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] [ChartedSpace (ClosedSmoothModel 3) M]
  [IsManifold (closedSmoothModelWithCorners 3) (↑⊤) M] (gt : ℝ → ClosedSmoothRiemannianMetric 3 M) (t : ℝ) : ℝ
Poincare.continuous_normalizedMeanScalarPrimitive.{u} {M : Type u} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] [ChartedSpace (ClosedSmoothModel 3) M]
  [IsManifold (closedSmoothModelWithCorners 3) (↑⊤) M] (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
  (hMeanContinuous : Continuous fun t => meanScalar (gt t)) : Continuous (normalizedMeanScalarPrimitive gt)
Poincare.hasDerivAt_normalizedMeanScalarPrimitive.{u} {M : Type u} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] [ChartedSpace (ClosedSmoothModel 3) M]
  [IsManifold (closedSmoothModelWithCorners 3) (↑⊤) M] (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
  (hMeanContinuous : Continuous fun t => meanScalar (gt t)) (t : ℝ) :
  HasDerivAt (normalizedMeanScalarPrimitive gt) (2 / 3 * meanScalar (gt t)) t
Poincare.hamilton_forward_preserved_and_improved_pinching_of_global_one_fourth_initial_floor.{u} {M : Type u}
  [TopologicalSpace M] [T2Space M] [CompactSpace M] [ChartedSpace (ClosedSmoothModel 3) M]
  [IsManifold (closedSmoothModelWithCorners 3) (↑⊤) M] [Nonempty M] (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
  {t0 T delta : ℝ} [∀ (t : ℝ), (gt t).leviCivita.ContMDiffCovariantDerivative 1] (hT0 : 0 ≤ T)
  (hdeltaNonneg : 0 ≤ delta) (hdeltaAdm : delta ≤ PinchingAlgebra.pinchedTracelessAdmissibleDelta3 (1 / 6))
  (hInitFloor : GlobalRicciEigenvalueFloor3 (gt t0) (1 / 4))
  (hRpos : ∀ tau ∈ Set.Icc 0 T, ∀ (x : M), 0 < (gt (t0 + tau)).scalarAt x)
  (hQCont : Continuous ↿fun tau x => (gt (t0 + tau)).pinchingQuotientAt x)
  (hQTwo :
    ∀ tau ∈ Set.Icc 0 T,
      ∀ (x : M),
        ContMDiffAt (closedSmoothModelWithCorners 3) (modelWithCornersSelf ℝ ℝ) 2
          (fun y => (gt (t0 + tau)).pinchingQuotientAt y) x)
  (hQEvol :
    ∀ tau ∈ Set.Icc 0 T,
      ∀ (x : M),
        ClosedSmoothRiemannianMetric.SatisfiesPinchingQuotientEvolutionAt gt (t0 + tau) x
          ((gt (t0 + tau)).pinchingRicciNormReactionMotionTraceCubicAt x))
  (hTQCont : Continuous ↿fun tau x => (gt (t0 + tau)).tracelessPinchingAt x delta)
  (hTQTwo :
    ∀ tau ∈ Set.Icc 0 T,
      ∀ (x : M),
        ContMDiffAt (closedSmoothModelWithCorners 3) (modelWithCornersSelf ℝ ℝ) 2
          (fun y => (gt (t0 + tau)).tracelessPinchingAt y delta) x)
  (hTQEvol :
    ∀ tau ∈ Set.Icc 0 T,
      ∀ (x : M),
        ClosedSmoothRiemannianMetric.SatisfiesTracelessPinchingImprovementEvolutionAt gt (t0 + tau) x delta
          ((gt (t0 + tau)).pinchingRicciNormReactionMotionTraceCubicAt x)) :
  (∀ tau ∈ Set.Icc 0 T, pinchingMaximumTrack gt t0 tau ≤ pinchingMaximumTrack gt t0 0) ∧
    (∀ tau ∈ Set.Icc 0 T, GlobalRicciEigenvalueFloor3 (gt (t0 + tau)) (1 / 6)) ∧
      ∀ tau ∈ Set.Icc 0 T, tracelessPinchingMaximumTrack gt t0 delta tau ≤ tracelessPinchingMaximumTrack gt t0 delta 0

EXIT_CODE=0
```

## Actual output: compile-01

Command: `LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HamiltonMeanFloorReduction.lean`.

```text
Poincare/Global/HamiltonMeanFloorReduction.lean:31:0: warning: automatically included section variable(s) unused in theorem `Poincare.exists_continuous_meanScalar_extension_of_normalizedRicciFlow`:
  [SecondCountableTopology M]
  [SimplyConnectedSpace M]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [SecondCountableTopology M] [SimplyConnectedSpace M] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
Poincare/Global/HamiltonMeanFloorReduction.lean:139:0: warning: automatically included section variable(s) unused in theorem `Poincare.normalizationPrimitive_unbounded_of_meanScalar_floor`:
  [SecondCountableTopology M]
  [SimplyConnectedSpace M]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [SecondCountableTopology M] [SimplyConnectedSpace M] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`

EXIT_CODE=0
```

## Actual output: gate-01

Command: `LEAN_NUM_THREADS=1 lake env lean /tmp/hamilton-mean-floor-reduction/gate-01.lean`. This scratch file contains the complete corresponding module source followed by these exact commands:

```lean
# Initial scalar positivity and the normalization obstruction
#print axioms Poincare.exists_continuous_meanScalar_extension_of_normalizedRicciFlow
#print axioms Poincare.continuousOn_meanScalar_of_normalizedRicciFlow
#print axioms Poincare.exists_normalizationPrimitive_of_normalizedRicciFlow
#print axioms Poincare.meanScalar_lower_profile_of_initial_scalar_pos
#print axioms Poincare.meanScalar_floor_on_Icc_of_initial_scalar_pos
#print axioms Poincare.normalizationPrimitive_unbounded_of_meanScalar_floor
```

```text
/tmp/hamilton-mean-floor-reduction/gate-01.lean:31:0: warning: automatically included section variable(s) unused in theorem `Poincare.exists_continuous_meanScalar_extension_of_normalizedRicciFlow`:
  [SecondCountableTopology M]
  [SimplyConnectedSpace M]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [SecondCountableTopology M] [SimplyConnectedSpace M] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
/tmp/hamilton-mean-floor-reduction/gate-01.lean:139:0: warning: automatically included section variable(s) unused in theorem `Poincare.normalizationPrimitive_unbounded_of_meanScalar_floor`:
  [SecondCountableTopology M]
  [SimplyConnectedSpace M]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [SecondCountableTopology M] [SimplyConnectedSpace M] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
'Poincare.exists_continuous_meanScalar_extension_of_normalizedRicciFlow' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.continuousOn_meanScalar_of_normalizedRicciFlow' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.exists_normalizationPrimitive_of_normalizedRicciFlow' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.meanScalar_lower_profile_of_initial_scalar_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.meanScalar_floor_on_Icc_of_initial_scalar_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.normalizationPrimitive_unbounded_of_meanScalar_floor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]

EXIT_CODE=0
```

## Actual output: checks-01

```text
$ rg -n \b(sorry|admit|axiom|opaque)\b|native_decide Poincare/Global/HamiltonMeanFloorReduction.lean
EXIT_CODE=1
$ git diff --check
EXIT_CODE=0
```

## Actual output: compile-02

Command: `LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HamiltonMeanFloorReduction.lean`.

```text
Poincare/Global/HamiltonMeanFloorReduction.lean:31:0: warning: automatically included section variable(s) unused in theorem `Poincare.exists_continuous_meanScalar_extension_of_normalizedRicciFlow`:
  [SecondCountableTopology M]
  [SimplyConnectedSpace M]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [SecondCountableTopology M] [SimplyConnectedSpace M] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
Poincare/Global/HamiltonMeanFloorReduction.lean:139:0: warning: automatically included section variable(s) unused in theorem `Poincare.normalizationPrimitive_unbounded_of_meanScalar_floor`:
  [SecondCountableTopology M]
  [SimplyConnectedSpace M]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [SecondCountableTopology M] [SimplyConnectedSpace M] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`

EXIT_CODE=0
```

## Actual output: gate-02

Command: `LEAN_NUM_THREADS=1 lake env lean /tmp/hamilton-mean-floor-reduction/gate-02.lean`. This scratch file contains the complete corresponding module source followed by these exact commands:

```lean
# Initial scalar positivity and the normalization obstruction
#check Poincare.exists_continuous_meanScalar_extension_of_normalizedRicciFlow
#print axioms Poincare.exists_continuous_meanScalar_extension_of_normalizedRicciFlow
#check Poincare.continuousOn_meanScalar_of_normalizedRicciFlow
#print axioms Poincare.continuousOn_meanScalar_of_normalizedRicciFlow
#check Poincare.exists_normalizationPrimitive_of_normalizedRicciFlow
#print axioms Poincare.exists_normalizationPrimitive_of_normalizedRicciFlow
#check Poincare.meanScalar_lower_profile_of_initial_scalar_pos
#print axioms Poincare.meanScalar_lower_profile_of_initial_scalar_pos
#check Poincare.meanScalar_floor_on_Icc_of_initial_scalar_pos
#print axioms Poincare.meanScalar_floor_on_Icc_of_initial_scalar_pos
#check Poincare.normalizationPrimitive_unbounded_of_meanScalar_floor
#print axioms Poincare.normalizationPrimitive_unbounded_of_meanScalar_floor
#check Poincare.not_exists_bounded_normalizationPrimitive_of_initial_scalar_pos
#print axioms Poincare.not_exists_bounded_normalizationPrimitive_of_initial_scalar_pos
```

```text
/tmp/hamilton-mean-floor-reduction/gate-02.lean:31:0: warning: automatically included section variable(s) unused in theorem `Poincare.exists_continuous_meanScalar_extension_of_normalizedRicciFlow`:
  [SecondCountableTopology M]
  [SimplyConnectedSpace M]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [SecondCountableTopology M] [SimplyConnectedSpace M] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
/tmp/hamilton-mean-floor-reduction/gate-02.lean:139:0: warning: automatically included section variable(s) unused in theorem `Poincare.normalizationPrimitive_unbounded_of_meanScalar_floor`:
  [SecondCountableTopology M]
  [SimplyConnectedSpace M]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [SecondCountableTopology M] [SimplyConnectedSpace M] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
Poincare.exists_continuous_meanScalar_extension_of_normalizedRicciFlow.{u} {M : Type u} [TopologicalSpace M] [T2Space M]
  [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] [ChartedSpace (Poincare.ClosedSmoothModel 3) M]
  [IsManifold (Poincare.closedSmoothModelWithCorners 3) ∞ M] [CompactSpace M] [ConnectedSpace M]
  [SimplyConnectedSpace M] (gt : ℝ → Poincare.ClosedSmoothRiemannianMetric 3 M)
  (hflow : ∀ t ∈ Ici 0, ∀ (x : M), Poincare.IsClosedNormalizedRicciFlowSolutionAt gt t x)
  (hjoint : ∀ (t : ℝ) (x : M), Poincare.MetricEntriesJointContDiffAt gt t x 3) :
  ∃ r, Continuous r ∧ ∀ t ∈ Ici 0, r t = Poincare.meanScalar (gt t)
'Poincare.exists_continuous_meanScalar_extension_of_normalizedRicciFlow' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
Poincare.continuousOn_meanScalar_of_normalizedRicciFlow.{u} {M : Type u} [TopologicalSpace M] [T2Space M]
  [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] [ChartedSpace (Poincare.ClosedSmoothModel 3) M]
  [IsManifold (Poincare.closedSmoothModelWithCorners 3) ∞ M] [CompactSpace M] [ConnectedSpace M]
  [SimplyConnectedSpace M] (gt : ℝ → Poincare.ClosedSmoothRiemannianMetric 3 M)
  (hflow : ∀ t ∈ Ici 0, ∀ (x : M), Poincare.IsClosedNormalizedRicciFlowSolutionAt gt t x)
  (hjoint : ∀ (t : ℝ) (x : M), Poincare.MetricEntriesJointContDiffAt gt t x 3) :
  ContinuousOn (fun t => Poincare.meanScalar (gt t)) (Ici 0)
'Poincare.continuousOn_meanScalar_of_normalizedRicciFlow' depends on axioms: [propext, Classical.choice, Quot.sound]
Poincare.exists_normalizationPrimitive_of_normalizedRicciFlow.{u} {M : Type u} [TopologicalSpace M] [T2Space M]
  [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] [ChartedSpace (Poincare.ClosedSmoothModel 3) M]
  [IsManifold (Poincare.closedSmoothModelWithCorners 3) ∞ M] [CompactSpace M] [ConnectedSpace M]
  [SimplyConnectedSpace M] (gt : ℝ → Poincare.ClosedSmoothRiemannianMetric 3 M)
  (hflow : ∀ t ∈ Ici 0, ∀ (x : M), Poincare.IsClosedNormalizedRicciFlowSolutionAt gt t x)
  (hjoint : ∀ (t : ℝ) (x : M), Poincare.MetricEntriesJointContDiffAt gt t x 3) :
  ∃ P, Continuous P ∧ P 0 = 0 ∧ ∀ t ∈ Ici 0, HasDerivAt P (2 / 3 * Poincare.meanScalar (gt t)) t
'Poincare.exists_normalizationPrimitive_of_normalizedRicciFlow' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
Poincare.meanScalar_lower_profile_of_initial_scalar_pos.{u} {M : Type u} [TopologicalSpace M] [T2Space M]
  [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] [ChartedSpace (Poincare.ClosedSmoothModel 3) M]
  [IsManifold (Poincare.closedSmoothModelWithCorners 3) ∞ M] [CompactSpace M] [ConnectedSpace M]
  [SimplyConnectedSpace M] (gt : ℝ → Poincare.ClosedSmoothRiemannianMetric 3 M)
  (hflow : ∀ t ∈ Ici 0, ∀ (x : M), Poincare.IsClosedNormalizedRicciFlowSolutionAt gt t x)
  (hjoint : ∀ (t : ℝ) (x : M), Poincare.MetricEntriesJointContDiffAt gt t x 3)
  (hinit : ∀ (x : M), 0 < (gt 0).scalarAt x) :
  ∃ rho P,
    0 < rho ∧
      Continuous P ∧
        P 0 = 0 ∧
          (∀ t ∈ Ici 0, HasDerivAt P (2 / 3 * Poincare.meanScalar (gt t)) t) ∧
            ∀ t ∈ Ici 0, rho / 2 * Real.exp (-P t) ≤ Poincare.meanScalar (gt t)
'Poincare.meanScalar_lower_profile_of_initial_scalar_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
Poincare.meanScalar_floor_on_Icc_of_initial_scalar_pos.{u} {M : Type u} [TopologicalSpace M] [T2Space M]
  [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] [ChartedSpace (Poincare.ClosedSmoothModel 3) M]
  [IsManifold (Poincare.closedSmoothModelWithCorners 3) ∞ M] [CompactSpace M] [ConnectedSpace M]
  [SimplyConnectedSpace M] (gt : ℝ → Poincare.ClosedSmoothRiemannianMetric 3 M)
  (hflow : ∀ t ∈ Ici 0, ∀ (x : M), Poincare.IsClosedNormalizedRicciFlowSolutionAt gt t x)
  (hjoint : ∀ (t : ℝ) (x : M), Poincare.MetricEntriesJointContDiffAt gt t x 3)
  (hinit : ∀ (x : M), 0 < (gt 0).scalarAt x) (T : ℝ) (hT : 0 ≤ T) :
  ∃ c, 0 < c ∧ ∀ t ∈ Icc 0 T, c ≤ Poincare.meanScalar (gt t)
'Poincare.meanScalar_floor_on_Icc_of_initial_scalar_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
Poincare.normalizationPrimitive_unbounded_of_meanScalar_floor.{u} {M : Type u} [TopologicalSpace M] [T2Space M]
  [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] [ChartedSpace (Poincare.ClosedSmoothModel 3) M]
  [IsManifold (Poincare.closedSmoothModelWithCorners 3) ∞ M] [CompactSpace M] [ConnectedSpace M]
  [SimplyConnectedSpace M] (gt : ℝ → Poincare.ClosedSmoothRiemannianMetric 3 M) (P : ℝ → ℝ)
  (hd : ∀ t ∈ Ici 0, HasDerivAt P (2 / 3 * Poincare.meanScalar (gt t)) t) {c : ℝ} (hc : 0 < c)
  (hfloor : ∀ (t : ↑(Ici 0)), c ≤ Poincare.meanScalar (gt ↑t)) (C : ℝ) : ∃ t ∈ Ici 0, C < P t - P 0
'Poincare.normalizationPrimitive_unbounded_of_meanScalar_floor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
Poincare.not_exists_bounded_normalizationPrimitive_of_initial_scalar_pos.{u} {M : Type u} [TopologicalSpace M]
  [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (Poincare.ClosedSmoothModel 3) M] [IsManifold (Poincare.closedSmoothModelWithCorners 3) ∞ M]
  [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M] (gt : ℝ → Poincare.ClosedSmoothRiemannianMetric 3 M)
  (hflow : ∀ t ∈ Ici 0, ∀ (x : M), Poincare.IsClosedNormalizedRicciFlowSolutionAt gt t x)
  (hjoint : ∀ (t : ℝ) (x : M), Poincare.MetricEntriesJointContDiffAt gt t x 3)
  (hinit : ∀ (x : M), 0 < (gt 0).scalarAt x) :
  ¬∃ P C, Continuous P ∧ (∀ t ∈ Ici 0, HasDerivAt P (2 / 3 * Poincare.meanScalar (gt t)) t) ∧ ∀ t ∈ Ici 0, P t - P 0 ≤ C
'Poincare.not_exists_bounded_normalizationPrimitive_of_initial_scalar_pos' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]

EXIT_CODE=0
```

## Actual output: checks-02

```text
$ rg -n \b(sorry|admit|axiom|opaque)\b|native_decide Poincare/Global/HamiltonMeanFloorReduction.lean
EXIT_CODE=1
$ git diff --check
EXIT_CODE=0
$ git diff --stat
 Poincare/Global/HamiltonMeanFloorReduction.lean | 34 +++++++++++++++++++++++++
 1 file changed, 34 insertions(+)
EXIT_CODE=0
```

## Recorded source locations

Source searches below show up to three actual matching lines per symbol and the full match count. All source lookup commands exited zero.

```text
$ rg -n -F satisfiesHamiltonScalarEvolutionAt_of_ricciFlow_joint_metric_entries_three Poincare .lake/packages/mathlib/Mathlib
Poincare/Global/MetricFlowJointPinchingEvolution.lean:718:    satisfiesHamiltonScalarEvolutionAt_of_ricciFlow_joint_metric_entries_three
Poincare/Global/MetricFlowJointPinchingEvolution.lean:870:    satisfiesHamiltonScalarEvolutionAt_of_ricciFlow_joint_metric_entries_three
Poincare/Global/CoordinateRicciFlowHamiltonScalarBridge.lean:73:    satisfiesHamiltonScalarEvolutionAt_of_ricciFlow_joint_metric_entries_three
[5 matches; first three displayed]
EXIT_CODE=0

$ rg -n -F normalizedMeanScalarPrimitive Poincare .lake/packages/mathlib/Mathlib
Poincare/Global/NormalizedFlowFiniteTimePositiveEinsteinMeanScalarInitialScalarProfile.lean:65:noncomputable def normalizedMeanScalarPrimitive
Poincare/Global/NormalizedFlowFiniteTimePositiveEinsteinMeanScalarInitialScalarProfile.lean:72:theorem continuous_normalizedMeanScalarPrimitive
Poincare/Global/NormalizedFlowFiniteTimePositiveEinsteinMeanScalarInitialScalarProfile.lean:75:    Continuous (normalizedMeanScalarPrimitive gt) := by
[8 matches; first three displayed]
EXIT_CODE=0

$ rg -n -F continuous_normalizedMeanScalarPrimitive Poincare .lake/packages/mathlib/Mathlib
Poincare/Global/NormalizedFlowFiniteTimePositiveEinsteinMeanScalarInitialScalarProfile.lean:72:theorem continuous_normalizedMeanScalarPrimitive
Poincare/Global/NormalizedFlowFiniteTimePositiveEinsteinMeanScalarInitialScalarProfile.lean:177:      (continuous_normalizedMeanScalarPrimitive gt hMeanContinuous)
EXIT_CODE=0

$ rg -n -F hasDerivAt_normalizedMeanScalarPrimitive Poincare .lake/packages/mathlib/Mathlib
Poincare/Global/NormalizedFlowFiniteTimePositiveEinsteinMeanScalarInitialScalarProfile.lean:83:theorem hasDerivAt_normalizedMeanScalarPrimitive
Poincare/Global/NormalizedFlowFiniteTimePositiveEinsteinMeanScalarInitialScalarProfile.lean:179:        hasDerivAt_normalizedMeanScalarPrimitive gt hMeanContinuous t)
EXIT_CODE=0

$ rg -n -F hamilton_forward_preserved_and_improved_pinching_of_global_one_fourth_initial_floor Poincare .lake/packages/mathlib/Mathlib
Poincare/Global/NormalizedFlowFiniteTimeHamiltonPinching.lean:251:theorem hamilton_forward_preserved_and_improved_pinching_of_global_one_fourth_initial_floor
Poincare/Global/NormalizedFlowFiniteTimeHamiltonPinching.lean:411:    hamilton_forward_preserved_and_improved_pinching_of_global_one_fourth_initial_floor
EXIT_CODE=0

$ rg -n -F exists_uniform_normalizedFlow_scalar_lower_of_initial_scalar_pos_of_normalizationPrimitive_bddAbove Poincare .lake/packages/mathlib/Mathlib
Poincare/Global/NormalizedFlowScalarLowerProfile.lean:337:theorem exists_uniform_normalizedFlow_scalar_lower_of_initial_scalar_pos_of_normalizationPrimitive_bddAbove
Poincare/Global/NormalizedFlowScalarLowerProfile.lean:395:    exists_uniform_normalizedFlow_scalar_lower_of_initial_scalar_pos_of_normalizationPrimitive_bddAbove
Poincare/Global/HamiltonMeanFloorReduction.lean:182:    exists_uniform_normalizedFlow_scalar_lower_of_initial_scalar_pos_of_normalizationPrimitive_bddAbove
EXIT_CODE=0

$ rg -n -F normalizedFlow_scalarAt_gt_exponential_normalizationPrimitive_Ici Poincare .lake/packages/mathlib/Mathlib
Poincare/Global/NormalizedFlowFiniteTimePositiveEinsteinMeanScalarInitialScalarProfile.lean:125:    apply normalizedFlow_scalarAt_gt_exponential_normalizationPrimitive_Ici
Poincare/Global/NormalizedFlowScalarLowerProfile.lean:257:theorem normalizedFlow_scalarAt_gt_exponential_normalizationPrimitive_Ici
Poincare/Global/NormalizedFlowScalarLowerProfile.lean:323:    normalizedFlow_scalarAt_gt_exponential_normalizationPrimitive_Ici
[4 matches; first three displayed]
EXIT_CODE=0

$ rg -n -F le_meanScalar_of_forall_le_scalarAt Poincare .lake/packages/mathlib/Mathlib
Poincare/Global/NormalizedFlowAbsoluteDissipation.lean:472:  exact le_meanScalar_of_forall_le_scalarAt (gt t) c (hScalarLower t)
Poincare/Global/NormalizedFlowInvariantRangeClosure.lean:129:      le_meanScalar_of_forall_le_scalarAt (gt t) c (hScalarLower t)
Poincare/Global/NormalizedFlowMeanScalarLimit.lean:275:    exact le_meanScalar_of_forall_le_scalarAt
[16 matches; first three displayed]
EXIT_CODE=0

$ rg -n -F meanScalar_pos_of_forall_scalarAt_ge Poincare .lake/packages/mathlib/Mathlib
Poincare/Global/ScalarMeanLowerBound.lean:94:theorem meanScalar_pos_of_forall_scalarAt_ge
EXIT_CODE=0

$ rg -n -F satisfiesNormalizedHamiltonScalarEvolutionAt_of_normalizedFlow_of_globalLichnerowicz Poincare .lake/packages/mathlib/Mathlib
Poincare/Global/NormalizedFlowFiniteTimePositiveEinsteinMeanScalarInitialScalarProfile.lean:130:        satisfiesNormalizedHamiltonScalarEvolutionAt_of_normalizedFlow_of_globalLichnerowicz
Poincare/Global/NormalizedFlowScalarLowerProfile.lean:52:theorem satisfiesNormalizedHamiltonScalarEvolutionAt_of_normalizedFlow_of_globalLichnerowicz
Poincare/Global/NormalizedFlowScalarLowerProfile.lean:400:      satisfiesNormalizedHamiltonScalarEvolutionAt_of_normalizedFlow_of_globalLichnerowicz
[6 matches; first three displayed]
EXIT_CODE=0

$ rg -n -F globalLichnerowiczAssemblyRegularity_of_jointMetricEntriesThree Poincare .lake/packages/mathlib/Mathlib
Poincare/Global/NormalizedFlowFullyAssembledEnergyEndpoint.lean:63:    globalLichnerowiczAssemblyRegularity_of_jointMetricEntriesThree hJoint
Poincare/Global/NormalizedFlowFullyAssembledEnergyEndpoint.lean:114:    globalLichnerowiczAssemblyRegularity_of_jointMetricEntriesThree hJoint
Poincare/Global/NormalizedFlowFullyAssembledEnergyEndpoint.lean:158:    globalLichnerowiczAssemblyRegularity_of_jointMetricEntriesThree hJoint
[28 matches; first three displayed]
EXIT_CODE=0

$ rg -n -F scalarAt_contMDiffAt_two_of_normalizedRicciFlow Poincare .lake/packages/mathlib/Mathlib
Poincare/Global/NormalizedFlowFiniteTimePositiveEinsteinMeanScalarInitialScalarProfile.lean:133:      exact scalarAt_contMDiffAt_two_of_normalizedRicciFlow
Poincare/Global/NormalizedFlowJointPinchingRegularity.lean:44:  exact scalarAt_contMDiffAt_two_of_normalizedRicciFlow
Poincare/Global/NormalizedFlowJointPinchingRegularity.lean:76:    scalarAt_contMDiffAt_two_of_normalizedRicciFlow hFlow hEntries x
[21 matches; first three displayed]
EXIT_CODE=0

$ rg -n -F timeVariationExtContMDiffAt_two_of_metricEntriesJointContDiffAt_three Poincare .lake/packages/mathlib/Mathlib
Poincare/Global/NormalizedFlowRicciTensorEvolution.lean:173:    timeVariationExtContMDiffAt_two_of_metricEntriesJointContDiffAt_three
Poincare/Global/FiniteExtinctionRicciFlowJointMetricEntries.lean:84:    exact timeVariationExtContMDiffAt_two_of_metricEntriesJointContDiffAt_three
Poincare/Global/HamiltonReactionEndpoint.lean:53:    (fun y ↦ timeVariationExtContMDiffAt_two_of_metricEntriesJointContDiffAt_three
[19 matches; first three displayed]
EXIT_CODE=0

$ rg -n -F continuousAt_scalarAt_joint_of_metricEntriesJointContDiffAt_three Poincare .lake/packages/mathlib/Mathlib
Poincare/Global/NormalizedFlowInvariantPairJointContinuity.lean:52:      continuousAt_scalarAt_joint_of_metricEntriesJointContDiffAt_three
Poincare/Global/NormalizedFlowInvariantPairJointContinuity.lean:60:      continuousAt_scalarAt_joint_of_metricEntriesJointContDiffAt_three
Poincare/Global/MetricFlowJointScalarContinuity.lean:33:  exact (continuousAt_scalarAt_joint_of_metricEntriesJointContDiffAt_three
[12 matches; first three displayed]
EXIT_CODE=0

$ rg -n -F continuous_trace_timeDeriv Poincare .lake/packages/mathlib/Mathlib
Poincare/Global/HamiltonChartDensityLocalDomination.lean:28:theorem continuous_trace_timeDeriv
Poincare/Global/HamiltonChartDensityLocalDomination.lean:162:  have hcont := (continuous_trace_timeDeriv gt hjoint).const_mul (1 / 2 : ℝ)
Poincare/Global/HamiltonMeanFloorReduction.lean:45:      (((HamiltonChartDensityLocalDomination.continuous_trace_timeDeriv gt hjoint).comp
EXIT_CODE=0

$ rg -n -F traceMetricVariationAt_timeDeriv_of_isClosedNormalizedRicciFlowSolutionAt Poincare .lake/packages/mathlib/Mathlib
Poincare/Global/NormalizedFlowScalarIntegralVariation.lean:318:    traceMetricVariationAt_timeDeriv_of_isClosedNormalizedRicciFlowSolutionAt
Poincare/Global/HamiltonMeanFloorReduction.lean:49:    rw [traceMetricVariationAt_timeDeriv_of_isClosedNormalizedRicciFlowSolutionAt
Poincare/Global/NormalizedFlowVolumeVariation.lean:129:theorem traceMetricVariationAt_timeDeriv_of_isClosedNormalizedRicciFlowSolutionAt
[7 matches; first three displayed]
EXIT_CODE=0

$ rg -n -F satisfiesHamiltonScalarEvolutionAt_of_ricciFlow Poincare .lake/packages/mathlib/Mathlib
Poincare/Global/FiniteExtinctionRicciFlowScalarEvolutionInteriorContinuousOn.lean:100:    exact satisfiesHamiltonScalarEvolutionAt_of_ricciFlow_no_raise_hypothesis
Poincare/Global/MetricFlowJointPinchingEvolution.lean:718:    satisfiesHamiltonScalarEvolutionAt_of_ricciFlow_joint_metric_entries_three
Poincare/Global/MetricFlowJointPinchingEvolution.lean:870:    satisfiesHamiltonScalarEvolutionAt_of_ricciFlow_joint_metric_entries_three
[31 matches; first three displayed]
EXIT_CODE=0

$ rg -n -F satisfiesRicciEvolutionAt_of_ricciFlow_traceSecondRegularity Poincare .lake/packages/mathlib/Mathlib
Poincare/Global/ScalarVariation.lean:25438:theorem satisfiesRicciEvolutionAt_of_ricciFlow_traceSecondRegularity
EXIT_CODE=0

$ rg -n -F continuousOn_meanScalar_of_ricciFlow Poincare .lake/packages/mathlib/Mathlib
Poincare/Global/ClosedRicciFlowNormalization.lean:310:theorem continuousOn_meanScalar_of_ricciFlow
Poincare/Global/ClosedRicciFlowNormalization.lean:343:    ((continuousOn_meanScalar_of_ricciFlow gt hhalf.le hflow' hjoint').mono
EXIT_CODE=0

$ rg -n -F hamilton_pinching_preserved Poincare .lake/packages/mathlib/Mathlib
Poincare/Global/MetricFlowJointPinchingEvolution.lean:1552:theorem hamilton_pinching_preserved_continuousOn
Poincare/Global/MetricFlowJointPinchingEvolution.lean:1806:theorem hamilton_pinching_preserved_of_ricciFlow_joint_metric_entries_three
Poincare/Global/MetricFlowJointPinchingEvolution.lean:1840:  exact hamilton_pinching_preserved_continuousOn
[8 matches; first three displayed]
EXIT_CODE=0

$ rg -n -F hamilton_eigenvalue_pinching_floor_preserved Poincare .lake/packages/mathlib/Mathlib
Poincare/Global/ScalarEvolution.lean:5053:theorem hamilton_eigenvalue_pinching_floor_preserved
Poincare/Global/NormalizedFlowFiniteTimePositiveEinstein.lean:71:    hamilton_eigenvalue_pinching_floor_preserved
Poincare/Global/NormalizedFlowFiniteTimeHamiltonPinching.lean:298:    hamilton_eigenvalue_pinching_floor_preserved
EXIT_CODE=0

$ rg -n -F meanScalar_deriv_nonneg_of_normalizedFlow_Ici_of_scalarVarianceTrack_le_six_tracelessRicciEnergyTrack Poincare .lake/packages/mathlib/Mathlib
Poincare/Global/NormalizedFlowFiniteDissipationCoerciveGap.lean:319:    meanScalar_deriv_nonneg_of_normalizedFlow_Ici_of_scalarVarianceTrack_le_six_tracelessRicciEnergyTrack
Poincare/Global/NormalizedFlowForwardFiniteTimePositiveEinsteinMeanScalarEnergyDomination.lean:43:theorem meanScalar_deriv_nonneg_of_normalizedFlow_Ici_of_scalarVarianceTrack_le_six_tracelessRicciEnergyTrack
Poincare/Global/NormalizedFlowForwardFiniteTimePositiveEinsteinMeanScalarEnergyDomination.lean:120:    meanScalar_deriv_nonneg_of_normalizedFlow_Ici_of_scalarVarianceTrack_le_six_tracelessRicciEnergyTrack
EXIT_CODE=0

$ rg -n -F normalizedTracelessRicciEvolutionReactionAt_le_neg_rate_mul_of_cubic_domination Poincare .lake/packages/mathlib/Mathlib
Poincare/Global/NormalizedFlowForwardPointwiseTracelessEnergyActualReactionDecay.lean:271:theorem normalizedTracelessRicciEvolutionReactionAt_le_neg_rate_mul_of_cubic_domination
Poincare/Global/NormalizedFlowForwardPointwiseTracelessEnergyActualReactionDecay.lean:296:    normalizedTracelessRicciEvolutionReactionAt_le_neg_rate_mul_of_cubic_domination
Poincare/Global/NormalizedFlowForwardPointwiseTracelessEnergyPinchingDomination.lean:127:    normalizedTracelessRicciEvolutionReactionAt_le_neg_rate_mul_of_cubic_domination
EXIT_CODE=0

$ rg -n -F mul_sub_le_image_sub_of_le_deriv Poincare .lake/packages/mathlib/Mathlib
Poincare/Global/HamiltonMeanFloorReduction.lean:147:    have h := (convex_Ici (0 : ℝ)).mul_sub_le_image_sub_of_le_deriv
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/MeanValue.lean:52:  `Convex.image_sub_le_mul_sub_of_deriv_le`, `Convex.mul_sub_le_image_sub_of_le_deriv`,
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/MeanValue.lean:307:theorem Convex.mul_sub_le_image_sub_of_le_deriv {D : Set ℝ} (hD : Convex ℝ D) {f : ℝ → ℝ}
[7 matches; first three displayed]
EXIT_CODE=0

$ rg -n -F integral_hasDerivAt_right Poincare .lake/packages/mathlib/Mathlib
Poincare/Global/HamiltonMeanFloorReduction.lean:80:  have hd := intervalIntegral.integral_hasDerivAt_right
Poincare/Global/NormalizedFlowFiniteTimePositiveEinsteinMeanScalarInitialScalarProfile.lean:91:  exact intervalIntegral.integral_hasDerivAt_right
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean:727:theorem integral_hasDerivAt_right (hf : IntervalIntegrable f volume a b)
[7 matches; first three displayed]
EXIT_CODE=0

$ rg -n -F differentiable_integral_of_continuous Poincare .lake/packages/mathlib/Mathlib
Poincare/Global/NormalizedFlowFiniteTimePositiveEinsteinMeanScalarInitialScalarProfile.lean:78:  exact (intervalIntegral.differentiable_integral_of_continuous
Poincare/Global/HamiltonMeanFloorReduction.lean:77:    (intervalIntegral.differentiable_integral_of_continuous (a := 0) hf).continuous,
.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean:933:theorem differentiable_integral_of_continuous (hcont : Continuous f) :
[4 matches; first three displayed]
EXIT_CODE=0

$ rg -n -F exists_pos_scalar_floor_of_forall_scalarAt_pos Poincare .lake/packages/mathlib/Mathlib
Poincare/Global/HamiltonMeanFloorReduction.lean:97:  obtain ⟨rho, hrho, hlow⟩ := exists_pos_scalar_floor_of_forall_scalarAt_pos (gt 0) hinit
Poincare/Global/NormalizedFlowScalarLowerProfile.lean:75:theorem exists_pos_scalar_floor_of_forall_scalarAt_pos
Poincare/Global/NormalizedFlowScalarLowerProfile.lean:362:    exists_pos_scalar_floor_of_forall_scalarAt_pos (gt t0) hInitialPos
EXIT_CODE=0

$ rg -n -F mul_div_cancel₀ Poincare .lake/packages/mathlib/Mathlib
.lake/packages/mathlib/Mathlib/Algebra/Algebra/Epi.lean:71:     _ = (b • (f a / f b)) ⊗ₜ[R] (1 / f b) := by rw [smul_def, mul_div_cancel₀ _ hb]
.lake/packages/mathlib/Mathlib/Algebra/Algebra/Epi.lean:73:     _ = (f a / f b) ⊗ₜ[R] 1 := by rw [smul_def, mul_div_cancel₀ _ hb]
.lake/packages/mathlib/Mathlib/Algebra/QuadraticDiscriminant.lean:138:      rw [mul_div_cancel₀ _ hb] at this
[123 matches; first three displayed]
EXIT_CODE=0

$ rg -n -F exists_isMaxOn Poincare .lake/packages/mathlib/Mathlib
.lake/packages/mathlib/Mathlib/Geometry/Manifold/Complex.lean:135:  rcases hc.exists_isMaxOn ⟨a, ha⟩ hd.continuousOn.norm with ⟨c, hcU, hc⟩
Poincare/Global/HamiltonMeanFloorReduction.lean:128:  obtain ⟨tmax, _, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hT)
.lake/packages/mathlib/Mathlib/NumberTheory/Transcendental/Liouville/Basic.lean:146:    IsCompact.exists_isMaxOn isCompact_Icc
[47 matches; first three displayed]
EXIT_CODE=0

$ rg -n -F convex_Ici Poincare .lake/packages/mathlib/Mathlib
Poincare/Global/HamiltonMeanFloorReduction.lean:147:    have h := (convex_Ici (0 : ℝ)).mul_sub_le_image_sub_of_le_deriv
Poincare/Global/NormalizedFlowFiniteDissipationCoerciveGap.lean:96:    monotoneOn_of_deriv_nonneg (convex_Ici T) hContinuous
Poincare/Global/MetricRescaleFiniteAtlasForwardFlow.lean:113:    apply strictMonoOn_of_hasDerivWithinAt_pos (convex_Ici (0 : ℝ))
[39 matches; first three displayed]
EXIT_CODE=0

```

## Final proof diff

```diff
diff --git a/Poincare/Global/HamiltonMeanFloorReduction.lean b/Poincare/Global/HamiltonMeanFloorReduction.lean
new file mode 100644
index 00000000..c8c7d9fd
--- /dev/null
+++ b/Poincare/Global/HamiltonMeanFloorReduction.lean
@@ -0,0 +1,200 @@
+import Poincare.Global.HamiltonReactionCoreFinal
+import Poincare.Global.NormalizedFlowScalarLowerProfile
+import Poincare.Global.MetricFlowJointScalarContinuity
+
+/-!
+# Initial scalar positivity and the normalization obstruction
+
+Joint metric regularity supplies a continuous extension of the forward mean
+scalar track, hence a normalization antiderivative. The scalar comparison
+then supplies positive floors on compact time intervals. A bounded
+antiderivative on the entire forward ray is incompatible with a positive
+uniform mean floor; it cannot be used as a viable replacement core.
+-/
+
+set_option autoImplicit false
+noncomputable section
+open Set Filter MeasureTheory
+open scoped Manifold ContDiff Topology
+universe u
+namespace Poincare
+
+variable {M : Type u}
+variable [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
+variable [MeasurableSpace M] [BorelSpace M]
+variable [ChartedSpace (ClosedSmoothModel 3) M]
+variable [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
+variable [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M]
+
+/-- The normalized equation expresses the mean using scalar curvature and
+metric speed at a single point, providing a continuous extension to real time. -/
+theorem exists_continuous_meanScalar_extension_of_normalizedRicciFlow
+    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
+    (hflow : ∀ t ∈ Ici (0 : ℝ), ∀ x, IsClosedNormalizedRicciFlowSolutionAt gt t x)
+    (hjoint : ∀ t x, MetricEntriesJointContDiffAt gt t x 3) :
+    ∃ r : ℝ → ℝ, Continuous r ∧ ∀ t ∈ Ici (0 : ℝ), r t = meanScalar (gt t) := by
+  classical
+  let x : M := Classical.arbitrary M
+  have hs : Continuous (fun p : ℝ × M ↦ (gt p.1).scalarAt p.2) :=
+    continuous_iff_continuousAt.mpr fun p ↦
+      continuousAt_scalarAt_joint_of_metricEntriesJointContDiffAt_three (hjoint p.1 p.2)
+  let r : ℝ → ℝ := fun t ↦ (gt t).scalarAt x +
+    traceMetricVariationAt (gt t) (timeDerivAt gt t) x / 2
+  refine ⟨r, ?_, ?_⟩
+  · exact (hs.comp (continuous_id.prodMk continuous_const)).add
+      (((HamiltonChartDensityLocalDomination.continuous_trace_timeDeriv gt hjoint).comp
+        (continuous_id.prodMk continuous_const)).div_const 2)
+  · intro t ht
+    dsimp [r]
+    rw [traceMetricVariationAt_timeDeriv_of_isClosedNormalizedRicciFlowSolutionAt
+      (hflow t ht x) (by norm_num)]
+    ring
+
+/-- Mean scalar continuity on the forward ray requires no moving-integral
+hypothesis for a jointly regular normalized flow. -/
+theorem continuousOn_meanScalar_of_normalizedRicciFlow
+    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
+    (hflow : ∀ t ∈ Ici (0 : ℝ), ∀ x, IsClosedNormalizedRicciFlowSolutionAt gt t x)
+    (hjoint : ∀ t x, MetricEntriesJointContDiffAt gt t x 3) :
+    ContinuousOn (fun t ↦ meanScalar (gt t)) (Ici (0 : ℝ)) := by
+  obtain ⟨r, hr, heq⟩ :=
+    exists_continuous_meanScalar_extension_of_normalizedRicciFlow gt hflow hjoint
+  exact hr.continuousOn.congr (fun t ht ↦ (heq t ht).symm)
+
+/-- Integrating a continuous extension constructs an ordinary derivative even
+at time zero. Its increments on the forward ray integrate `(2/3) meanScalar`. -/
+theorem exists_normalizationPrimitive_of_normalizedRicciFlow
+    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
+    (hflow : ∀ t ∈ Ici (0 : ℝ), ∀ x, IsClosedNormalizedRicciFlowSolutionAt gt t x)
+    (hjoint : ∀ t x, MetricEntriesJointContDiffAt gt t x 3) :
+    ∃ P : ℝ → ℝ, Continuous P ∧ P 0 = 0 ∧
+      ∀ t ∈ Ici (0 : ℝ), HasDerivAt P ((2 / 3 : ℝ) * meanScalar (gt t)) t := by
+  obtain ⟨r, hr, heq⟩ :=
+    exists_continuous_meanScalar_extension_of_normalizedRicciFlow gt hflow hjoint
+  let f : ℝ → ℝ := fun t ↦ (2 / 3 : ℝ) * r t
+  have hf : Continuous f := continuous_const.mul hr
+  refine ⟨fun t ↦ ∫ s in (0 : ℝ)..t, f s,
+    (intervalIntegral.differentiable_integral_of_continuous (a := 0) hf).continuous,
+    by simp, ?_⟩
+  intro t ht
+  have hd := intervalIntegral.integral_hasDerivAt_right
+    (hf.intervalIntegrable 0 t)
+    hf.aestronglyMeasurable.stronglyMeasurableAtFilter hf.continuousAt
+  simpa only [f, heq t ht] using hd
+
+/-- Positive initial scalar curvature gives an explicit positive mean profile.
+The profile is allowed to decrease with time. -/
+theorem meanScalar_lower_profile_of_initial_scalar_pos
+    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
+    (hflow : ∀ t ∈ Ici (0 : ℝ), ∀ x, IsClosedNormalizedRicciFlowSolutionAt gt t x)
+    (hjoint : ∀ t x, MetricEntriesJointContDiffAt gt t x 3)
+    (hinit : ∀ x, 0 < (gt 0).scalarAt x) :
+    ∃ (rho : ℝ) (P : ℝ → ℝ), 0 < rho ∧ Continuous P ∧ P 0 = 0 ∧
+      (∀ t ∈ Ici (0 : ℝ), HasDerivAt P ((2 / 3 : ℝ) * meanScalar (gt t)) t) ∧
+      ∀ t ∈ Ici (0 : ℝ),
+        (rho / 2) * Real.exp (-P t) ≤ meanScalar (gt t) := by
+  obtain ⟨P, hP, hP0, hd⟩ := exists_normalizationPrimitive_of_normalizedRicciFlow gt hflow hjoint
+  obtain ⟨rho, hrho, hlow⟩ := exists_pos_scalar_floor_of_forall_scalarAt_pos (gt 0) hinit
+  have hs : Continuous (fun p : ℝ × M ↦ (gt p.1).scalarAt p.2) :=
+    continuous_iff_continuousAt.mpr fun p ↦
+      continuousAt_scalarAt_joint_of_metricEntriesJointContDiffAt_three (hjoint p.1 p.2)
+  have hL := globalLichnerowiczAssemblyRegularity_of_jointMetricEntriesThree hjoint
+  have hp := normalizedFlow_scalarAt_gt_exponential_normalizationPrimitive_Ici
+    (gt := gt) (t0 := 0) hrho (by simpa only [zero_add] using hs)
+    (fun t ht x ↦ by
+      simpa only [zero_add] using
+        satisfiesNormalizedHamiltonScalarEvolutionAt_of_normalizedFlow_of_globalLichnerowicz
+          (x := x) (hflow t ht) hL)
+    (fun t ht x ↦ by
+      simpa only [zero_add] using scalarAt_contMDiffAt_two_of_normalizedRicciFlow
+        (hflow t ht) (hL.timeVariationEntries t) x)
+    P hP (by simpa only [zero_add] using hd) hlow
+  refine ⟨rho, P, hrho, hP, hP0, hd, ?_⟩
+  intro t ht
+  apply le_meanScalar_of_forall_le_scalarAt
+  intro x
+  simpa only [zero_add, hP0, sub_zero] using (hp t ht x).le
+
+/-- A positive floor follows on each fixed compact forward time interval.
+The witness may depend on the endpoint. -/
+theorem meanScalar_floor_on_Icc_of_initial_scalar_pos
+    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
+    (hflow : ∀ t ∈ Ici (0 : ℝ), ∀ x, IsClosedNormalizedRicciFlowSolutionAt gt t x)
+    (hjoint : ∀ t x, MetricEntriesJointContDiffAt gt t x 3)
+    (hinit : ∀ x, 0 < (gt 0).scalarAt x) (T : ℝ) (hT : 0 ≤ T) :
+    ∃ c : ℝ, 0 < c ∧ ∀ t ∈ Icc (0 : ℝ) T, c ≤ meanScalar (gt t) := by
+  obtain ⟨rho, P, hrho, hP, _, _, hlow⟩ :=
+    meanScalar_lower_profile_of_initial_scalar_pos gt hflow hjoint hinit
+  obtain ⟨tmax, _, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hT)
+    hP.continuousOn
+  refine ⟨(rho / 2) * Real.exp (-P tmax),
+    mul_pos (div_pos hrho (by norm_num)) (Real.exp_pos _), ?_⟩
+  intro t ht
+  exact (mul_le_mul_of_nonneg_left
+    (Real.exp_le_exp.mpr (neg_le_neg (hmax ht)))
+    (div_nonneg hrho.le (by norm_num))).trans (hlow t ht.1)
+
+/-- A positive uniform mean floor forces every normalization antiderivative
+to exceed every proposed upper bound on its forward increments. -/
+theorem normalizationPrimitive_unbounded_of_meanScalar_floor
+    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
+    (P : ℝ → ℝ)
+    (hd : ∀ t ∈ Ici (0 : ℝ), HasDerivAt P ((2 / 3 : ℝ) * meanScalar (gt t)) t)
+    {c : ℝ} (hc : 0 < c)
+    (hfloor : ∀ t : Ici (0 : ℝ), c ≤ meanScalar (gt t.1)) :
+    ∀ C : ℝ, ∃ t ∈ Ici (0 : ℝ), C < P t - P 0 := by
+  have hg (t : ℝ) (ht : 0 ≤ t) : (2 / 3 : ℝ) * c * t ≤ P t - P 0 := by
+    have h := (convex_Ici (0 : ℝ)).mul_sub_le_image_sub_of_le_deriv
+      (fun s hs ↦ (hd s hs).continuousAt.continuousWithinAt)
+      (fun s hs ↦ (hd s (interior_subset hs)).differentiableAt.differentiableWithinAt)
+      (C := (2 / 3 : ℝ) * c)
+      (fun s hs ↦ by
+        rw [(hd s (interior_subset hs)).deriv]
+        exact mul_le_mul_of_nonneg_left (hfloor ⟨s, interior_subset hs⟩) (by norm_num))
+      0 (by simp) t ht ht
+    simpa only [sub_zero] using h
+  intro C
+  let t : ℝ := (|C| + 1) / ((2 / 3 : ℝ) * c)
+  have hden : 0 < (2 / 3 : ℝ) * c := mul_pos (by norm_num) hc
+  have ht : 0 ≤ t := (div_pos (by positivity) hden).le
+  refine ⟨t, ht, ?_⟩
+  have heq : (2 / 3 : ℝ) * c * t = |C| + 1 := mul_div_cancel₀ _ hden.ne'
+  have hbound := hg t ht
+  rw [heq] at hbound
+  linarith [le_abs_self C]
+
+/-- The proposed bounded normalization residual is inconsistent with positive
+initial scalar curvature on an infinite jointly regular normalized flow. -/
+theorem not_exists_bounded_normalizationPrimitive_of_initial_scalar_pos
+    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
+    (hflow : ∀ t ∈ Ici (0 : ℝ), ∀ x, IsClosedNormalizedRicciFlowSolutionAt gt t x)
+    (hjoint : ∀ t x, MetricEntriesJointContDiffAt gt t x 3)
+    (hinit : ∀ x, 0 < (gt 0).scalarAt x) :
+    ¬ ∃ (P : ℝ → ℝ) (C : ℝ), Continuous P ∧
+      (∀ t ∈ Ici (0 : ℝ), HasDerivAt P ((2 / 3 : ℝ) * meanScalar (gt t)) t) ∧
+      ∀ t ∈ Ici (0 : ℝ), P t - P 0 ≤ C := by
+  rintro ⟨P, C, hP, hd, hupper⟩
+  have hs : Continuous (fun p : ℝ × M ↦ (gt p.1).scalarAt p.2) :=
+    continuous_iff_continuousAt.mpr fun p ↦
+      continuousAt_scalarAt_joint_of_metricEntriesJointContDiffAt_three (hjoint p.1 p.2)
+  have hL := globalLichnerowiczAssemblyRegularity_of_jointMetricEntriesThree hjoint
+  obtain ⟨c, hc, hlow⟩ :=
+    exists_uniform_normalizedFlow_scalar_lower_of_initial_scalar_pos_of_normalizationPrimitive_bddAbove
+      (gt := gt) (t0 := 0) (C := C) (by simpa only [zero_add] using hs)
+      (fun t ht x ↦ by
+        simpa only [zero_add] using
+          satisfiesNormalizedHamiltonScalarEvolutionAt_of_normalizedFlow_of_globalLichnerowicz
+            (x := x) (hflow t ht) hL)
+      (fun t ht x ↦ by
+        simpa only [zero_add] using scalarAt_contMDiffAt_two_of_normalizedRicciFlow
+          (hflow t ht) (hL.timeVariationEntries t) x)
+      P hP (by simpa only [zero_add] using hd) hupper hinit
+  have hmean : ∀ t : Ici (0 : ℝ), c ≤ meanScalar (gt t.1) := by
+    intro t
+    exact le_meanScalar_of_forall_le_scalarAt (gt t.1) c
+      (by simpa only [zero_add] using hlow t.1 t.2)
+  obtain ⟨t, ht, hlt⟩ :=
+    normalizationPrimitive_unbounded_of_meanScalar_floor gt P hd hc hmean C
+  exact (not_lt_of_ge (hupper t ht)) hlt
+
+end Poincare
```
