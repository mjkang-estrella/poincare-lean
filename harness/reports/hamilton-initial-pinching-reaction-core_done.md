# Hamilton initial pinching reaction core reduction

Date: 2026-09-10. Worker result: done, pending independent acceptance.

Base: `0bafde8403d953b99c8e5e51eefffc8ae89d057f`. Proof head: `fde6a5d496a8d22a89400214a6b794a09263eb7a`.
Branch: `worker/hamilton-initial-pinching-reaction-core`.
Worktree: `/private/tmp/poincare-workers/hamilton-initial-pinching-reaction-core`.
Toolchain: `leanprover/lean4:v4.30.0-rc2`.

## Result

The new module `Poincare/Global/HamiltonInitialPinchingReactionCoreReduction.lean` proves both sufficient core adapters,
the Hamilton pinched-limit endpoint, and the universal reduction. All seven
new declarations have exactly `[propext, Classical.choice, Quot.sound]`.
Every source compilation and dependency probe exited 0 with no warnings.
The forbidden-token scans have empty output and the expected exit 1.
Whitespace checks exit 0. The survey's displayed final target was extracted
verbatim and proved by applying the new adapter with precisely its witnesses
and hypotheses. No extra analytic input was introduced.

For the main adapter, the witnesses are
`c = meanScalar (gt 0)`, `epsilon_later = 2 * epsilon - 1/3`,
`kappa = 1 - 4 * epsilon + 6 * epsilon^2`,
`gamma = 4/3 - 2 * (2 - delta) * kappa * C`, and `rate = gamma * c`.
`meanFloorFromEnergy` proves positivity and the forward mean floor.
`initial_pinching_preserved` retains the initial quotient coefficient and
supplies the degraded eigenfloor. The global pinching domination theorem
supplies the reaction inequality using `gamma * c ≤ gamma * meanScalar (gt t)`.
That landed theorem uses the cubic-domination bridge.

The Eta variant replaces only the comparison/gap pair by the explicit
positive-existential normalization gap from section 4.5. It uses `rate = eta`
and the landed direct normalization-gap theorem. Both definitions retain the
compact realization, parameter continuity, realization equality, all-time
joint C³ entries, continuous third-jet profiles, forward normalized flow,
initial pointwise scalar positivity, the initial eigenfloor, the strict
`1/6` lower bound and `1/3` upper bound, and the original delta bounds and
admissibility for the degraded floor.

The comparison/gap, `V ≤ 6E`, and scalar Stokes premises remain displayed in
the definitions. No theorem here produces these residual estimates or proves
the universal existence input. This is a conditional reduction, not an
unconditional proof of the Poincare conjecture.

## Scope and commits

The task-specific branch and one-new-Lean-module scope were followed.
The only other delivery is this required report. Existing Lean sources,
`Poincare.lean`, frozen contracts, audits, missions, ledgers, and `HANDOFF.md`
were not edited. This report carries the handoff because the task limits
edits to the new module and its report. No merge or task acceptance was done.
No full build or root integration audit was launched.

The initial `git status --short --branch` output was:

```text
## worker/hamilton-initial-pinching-reaction-core
```

`git rev-parse HEAD` returned the base above. The porcelain worktree inventory
showed this worktree on the named worker branch and main at that same base,
as well as other worktrees that were left untouched. README, HANDOFF top,
PROJECT_MAP, AGENTS, the task, survey sections 2.2, 3.4, 4.5 and Appendix C,
and the landed prerequisite sources and imports were read before editing.

Each theorem was compiled, dependency-checked, token-scanned, and committed
before adding the next theorem:

```text
fde6a5d4 Derive universal Hamilton convergence from initial pinching cores
0b3cd651 Derive Hamilton pinched limit from initial pinching reaction core
a4a8a5ac Prove initial pinching reaction core adapter with direct eta gap
84ff8ca8 Prove reaction core reduction from initial pinching and residual estimates
```

Probe source revisions: `main-*` uses `84ff8ca8`, `eta-*` uses `a4a8a5ac`,
`endpoint-*` uses `0b3cd651`, and `final-*` plus `survey-target` use `fde6a5d4`.
The dependency probes copy the corresponding source and append `#print axioms`
for each declaration then present. They use source copies so they cannot
accidentally test an old cached build of the new module.

## Exact survey-target application

The following suffix was appended to the final source. Its proposition comes
from the final `#check` in Appendix C's `targets.lean`, with only the `#check`
wrapper changed to an `example` declaration. The compiler accepted the full
application. Actual command and output appear in the complete probe log below.

```lean
open Poincare Poincare.HamiltonInitialPinchingReactionCoreReduction
variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (ClosedSmoothModel 3) M]
  [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
  [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M]

example : ∀ (K : Type v) [TopologicalSpace K] [CompactSpace K]
    (metric : K → ClosedSmoothRiemannianMetric 3 M)
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    (parameter : Ici (0 : ℝ) → K) (epsilon delta C : ℝ),
  Continuous parameter →
  (∀ t : Ici (0 : ℝ), metric (parameter t) = gt t.1) →
  (∀ slot : MetricEntryThirdJetSlot 3 M,
    Continuous (fun p : K × ClosedSmoothModel 3 ↦ metricEntryThirdJetProfile (metric p.1) slot p.2)) →
  (∀ t x, MetricEntriesJointContDiffAt gt t x 3) →
  (∀ t ∈ Ici (0 : ℝ), ∀ x, IsClosedNormalizedRicciFlowSolutionAt gt t x) →
  (∀ x, 0 < (gt 0).scalarAt x) →
  1/6 < epsilon → epsilon ≤ 1/3 →
  GlobalRicciEigenvalueFloor3 (gt 0) epsilon →
  0 < delta → delta ≤ 1 →
  delta ≤ PinchingAlgebra.pinchedTracelessAdmissibleDelta3 (2 * epsilon - 1/3) →
  (∀ t ∈ Ici (0 : ℝ), ClosedLaplacianStokes (gt t) (fun x ↦ (gt t).scalarAt x)) →
  (∀ t : Ici (0 : ℝ), normalizedFlowScalarVarianceTrack gt t.1 ≤
    6 * normalizedFlowTracelessRicciEnergyTrack gt t.1) →
  (∀ t ∈ Ici (0 : ℝ), ∀ x, (gt t).scalarAt x ≤ C * meanScalar (gt t)) →
  0 < (4/3 : ℝ) - 2 * (2 - delta) * (1 - 4 * epsilon + 6 * epsilon^2) * C →
  HamiltonReactionCore3Final.{u,v} M := by
  intro K topK compactK metric gt parameter epsilon delta C
    hparam hreal hjet hjoint hflow hinit hepos hele hpin hdpos hdle hadm
    hstokes henergy hcompare hgap
  exact hamiltonReactionCore3Final_of_initialPinching
    ⟨K, topK, compactK, metric, gt, parameter, epsilon, delta, C,
      hparam, hreal, hjet, hjoint, hflow, hinit, hepos, hele, hpin,
      hdpos, hdle, hadm, hstokes, henergy, hcompare, hgap⟩
```

## Complete probe log

All commands below ran with `LEAN_NUM_THREADS=1`. Empty output is shown as an
empty fenced block. There were no failed Lean probes. The raw source snapshots,
outputs, command JSONL, and final diff also remain in
`/tmp/hamilton-initial-pinching-reaction-core-evidence`.

### main-01

Command: `lake env lean Poincare/Global/HamiltonInitialPinchingReactionCoreReduction.lean`. Exit: 0.

```text
```

### main-tokens

Command: `rg -n '\b(sorry|admit|axiom|opaque)\b|native_decide' Poincare/Global/HamiltonInitialPinchingReactionCoreReduction.lean`. Exit: 1.

```text
```

### main-whitespace

Command: `git diff --check`. Exit: 0.

```text
```

### main-dependencies

Command: `lake env lean /tmp/hamilton-initial-pinching-reaction-core-evidence/main-dependencies.lean`. Exit: 0.

```text
'Poincare.HamiltonInitialPinchingReactionCoreReduction.HamiltonReactionCore3InitialPinching' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HamiltonInitialPinchingReactionCoreReduction.hamiltonReactionCore3Final_of_initialPinching' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### eta-01

Command: `lake env lean Poincare/Global/HamiltonInitialPinchingReactionCoreReduction.lean`. Exit: 0.

```text
```

### eta-dependencies

Command: `lake env lean /tmp/hamilton-initial-pinching-reaction-core-evidence/eta-dependencies.lean`. Exit: 0.

```text
'Poincare.HamiltonInitialPinchingReactionCoreReduction.HamiltonReactionCore3InitialPinching' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HamiltonInitialPinchingReactionCoreReduction.hamiltonReactionCore3Final_of_initialPinching' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HamiltonInitialPinchingReactionCoreReduction.HamiltonReactionCore3InitialPinchingEta' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HamiltonInitialPinchingReactionCoreReduction.hamiltonReactionCore3Final_of_initialPinchingEta' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### eta-tokens

Command: `rg -n '\b(sorry|admit|axiom|opaque)\b|native_decide' Poincare/Global/HamiltonInitialPinchingReactionCoreReduction.lean`. Exit: 1.

```text
```

### eta-whitespace

Command: `git diff --check`. Exit: 0.

```text
```

### endpoint-01

Command: `lake env lean Poincare/Global/HamiltonInitialPinchingReactionCoreReduction.lean`. Exit: 0.

```text
```

### endpoint-dependencies

Command: `lake env lean /tmp/hamilton-initial-pinching-reaction-core-evidence/endpoint-dependencies.lean`. Exit: 0.

```text
'Poincare.HamiltonInitialPinchingReactionCoreReduction.HamiltonReactionCore3InitialPinching' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HamiltonInitialPinchingReactionCoreReduction.hamiltonReactionCore3Final_of_initialPinching' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HamiltonInitialPinchingReactionCoreReduction.HamiltonReactionCore3InitialPinchingEta' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HamiltonInitialPinchingReactionCoreReduction.hamiltonReactionCore3Final_of_initialPinchingEta' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HamiltonInitialPinchingReactionCoreReduction.hamiltonConvergencePinchedLimit3_of_hamiltonReactionCore3InitialPinching' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### endpoint-tokens

Command: `rg -n '\b(sorry|admit|axiom|opaque)\b|native_decide' Poincare/Global/HamiltonInitialPinchingReactionCoreReduction.lean`. Exit: 1.

```text
```

### endpoint-whitespace

Command: `git diff --check`. Exit: 0.

```text
```

### final-01

Command: `lake env lean Poincare/Global/HamiltonInitialPinchingReactionCoreReduction.lean`. Exit: 0.

```text
```

### final-dependencies

Command: `lake env lean /tmp/hamilton-initial-pinching-reaction-core-evidence/final-dependencies.lean`. Exit: 0.

```text
'Poincare.HamiltonInitialPinchingReactionCoreReduction.HamiltonReactionCore3InitialPinching' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HamiltonInitialPinchingReactionCoreReduction.hamiltonReactionCore3Final_of_initialPinching' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HamiltonInitialPinchingReactionCoreReduction.HamiltonReactionCore3InitialPinchingEta' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HamiltonInitialPinchingReactionCoreReduction.hamiltonReactionCore3Final_of_initialPinchingEta' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HamiltonInitialPinchingReactionCoreReduction.hamiltonConvergencePinchedLimit3_of_hamiltonReactionCore3InitialPinching' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HamiltonInitialPinchingReactionCoreReduction.UniversalHamiltonReactionCoreInitialPinchingStatement' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HamiltonInitialPinchingReactionCoreReduction.universalHamiltonConvergence_of_universalHamiltonReactionCoreInitialPinching' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### final-names

Command: `rg -n '^(noncomputable )?(def|theorem|structure) (HamiltonReactionCore3InitialPinching|hamiltonReactionCore3Final_of_initialPinching|hamiltonConvergencePinchedLimit3_of_hamiltonReactionCore3InitialPinching|UniversalHamiltonReactionCoreInitialPinchingStatement|universalHamiltonConvergence_of_universalHamiltonReactionCoreInitialPinching|HamiltonReactionCore3Final|hamiltonConvergencePinchedLimit3_of_hamiltonReactionCore3Final|UniversalHamiltonConvergenceStatement|scalarAt_pos_of_initial_scalar_pos|initial_pinching_preserved|meanFloorFromEnergy|pinchingQuotientCoefficient_pos|normalizedTracelessRicciEvolutionReactionAt_global_domination_of_pinching|normalizedTracelessRicciEvolutionReactionAt_le_neg_rate_mul_of_eigenvalue_pinching_of_normalization_gap|ClosedSmoothRiemannianMetric|MetricEntryThirdJetSlot|metricEntryThirdJetProfile|MetricEntriesJointContDiffAt|IsClosedNormalizedRicciFlowSolutionAt|GlobalRicciEigenvalueFloor3|GlobalPinchingQuotientBound3|pinchedTracelessAdmissibleDelta3|ClosedLaplacianStokes|normalizedFlowScalarVarianceTrack|normalizedFlowTracelessRicciEnergyTrack|meanScalar|normalizedTracelessRicciEvolutionReactionAt|HamiltonConvergencePinchedLimit3)' Poincare`. Exit: 0.

```text
Poincare/Global/MetricEntryThirdJetProfileLimitAlgebra.lean:81:theorem metricEntryThirdJetProfile_anchor_add_left_of_mem_closure
Poincare/Global/MetricEntryThirdJetProfileLimitAlgebra.lean:110:theorem metricEntryThirdJetProfile_anchor_smul_left_of_mem_closure
Poincare/Global/MetricEntryThirdJetProfileLimitAlgebra.lean:135:theorem metricEntryThirdJetProfile_anchor_add_right_of_mem_closure
Poincare/Global/MetricEntryThirdJetProfileLimitAlgebra.lean:160:theorem metricEntryThirdJetProfile_anchor_smul_right_of_mem_closure
Poincare/Global/MetricEntryThirdJetProfileLimitAlgebra.lean:180:theorem metricEntryThirdJetProfile_anchor_symm_of_mem_closure
Poincare/Global/MetricEntryThirdJetProfileLimitAlgebra.lean:196:theorem metricEntryThirdJetProfile_anchor_lower_of_mem_closure
Poincare/Global/MetricEntryThirdJetProfileLimitAlgebra.lean:228:noncomputable def metricEntryThirdJetProfileAnchorBilin
Poincare/Global/MetricEntryThirdJetProfileLimitAlgebra.lean:247:theorem metricEntryThirdJetProfileAnchorBilin_symm
Poincare/Global/MetricEntryThirdJetProfileLimitAlgebra.lean:258:theorem metricEntryThirdJetProfileAnchorBilin_pos
Poincare/Global/SphereTheorem.lean:118:def HamiltonConvergencePinchedLimit3 (M : Type u)
Poincare/Global/NormalizedFlowInitialPinchingPreservation.lean:30:theorem scalarAt_pos_of_initial_scalar_pos
Poincare/Global/NormalizedFlowInitialPinchingPreservation.lean:76:theorem initial_pinching_preserved
Poincare/Global/MetricFlowJointRegularity.lean:198:def MetricEntriesJointContDiffAt
Poincare/Global/MetricFlowJointRegularity.lean:204:theorem MetricEntriesJointContDiffAt.of_le
Poincare/Global/NormalizedFlowForwardTracelessEnergyDifferentialDecay.lean:36:theorem normalizedFlowTracelessRicciEnergyTrack_le_initial_mul_exp_neg_of_differential_decay
Poincare/Global/NormalizedFlowForwardTracelessEnergyDifferentialDecay.lean:54:theorem normalizedFlowTracelessRicciEnergyTrack_integrableOn_of_differential_decay
Poincare/Global/PinchedLimitInterface.lean:31:def HamiltonConvergencePinchedLimit3Core (M : Type u)
Poincare/Global/NormalizedFlowPinchingLimit.lean:151:theorem ClosedSmoothRiemannianMetric.relativeTracelessRicciAt_eq_tracelessPinchingAt_zero
Poincare/Global/NormalizedFlowCompactMeanEnergyMeasureEventualHamiltonPinchingDecay.lean:165:theorem pinchingQuotientCoefficient_pos
Poincare/Global/NormalizedFlowCompactScalarVarianceContinuity.lean:105:theorem normalizedFlowScalarVarianceTrack_aestronglyMeasurable_of_compact_parameterization
Poincare/Global/NormalizedFlowForwardFiniteTimePositiveEinsteinMeanScalarPointwiseDomination.lean:49:theorem normalizedFlowScalarVarianceTrack_le_six_tracelessRicciEnergyTrack_Ici_of_pointwise_centeredScalarSq_le_six_tracelessRicciNormSq
Poincare/Global/ScalarEvolution.lean:192:theorem ClosedSmoothRiemannianMetric.hasDerivAt_tracelessPinchingAt_of_scalar_and_tracelessNorm
Poincare/Global/ScalarEvolution.lean:208:theorem ClosedSmoothRiemannianMetric.hasDerivAt_tracelessRicciNormSqAt_of_ricciNormSq_and_scalar_sq
Poincare/Global/NormalizedFlowForwardPointwiseTracelessEnergyActualReactionDecay.lean:260:noncomputable def normalizedTracelessRicciEvolutionReactionAt
Poincare/Global/NormalizedFlowForwardPointwiseTracelessEnergyActualReactionDecay.lean:271:theorem normalizedTracelessRicciEvolutionReactionAt_le_neg_rate_mul_of_cubic_domination
Poincare/Global/NormalizedFlowForwardPointwiseTracelessEnergyActualReactionDecay.lean:287:theorem normalizedTracelessRicciEvolutionReactionAt_le_neg_rate_mul_of_cubic_nonpos
Poincare/Global/NormalizedFlowFiniteDissipationCoerciveGap.lean:121:theorem normalizedFlowScalarVarianceTrack_le_coerciveGapFactor_mul_meanScalar_deriv_at
Poincare/Global/NormalizedFlowFiniteDissipationCoerciveGap.lean:188:theorem normalizedFlowScalarVarianceTrack_le_coerciveGapFactor_mul_meanScalar_deriv
Poincare/Global/NormalizedFlowHausdorffPartitionStokes.lean:734:theorem ClosedSmoothRiemannianMetric.laplacianAt_finsetSum
Poincare/Global/NormalizedFlowForwardTracelessEnergyDecay.lean:36:theorem normalizedFlowTracelessRicciEnergyTrack_nonneg
Poincare/Global/NormalizedFlowForwardTracelessEnergyDecay.lean:45:theorem normalizedFlowTracelessRicciEnergyTrack_integrableOn_of_exponential_bound
Poincare/Global/NormalizedFlowForwardTracelessEnergyDecay.lean:73:theorem normalizedFlowTracelessRicciEnergyTrack_aestronglyMeasurable_of_continuousOn
Poincare/Global/NormalizedFlowForwardTracelessEnergyDecay.lean:85:theorem normalizedFlowTracelessRicciEnergyTrack_integrableOn_of_continuousOn_of_exponential_bound
Poincare/Global/NormalizedFlowFiniteTimePositiveRicci.lean:107:theorem ClosedSmoothRiemannianMetric.ricciEigenvalue_lower_bounds_of_scalar_lower_of_traceless_lt
Poincare/Global/NormalizedFlowFiniteTimePositiveRicci.lean:141:theorem ClosedSmoothRiemannianMetric.pinchingQuotientAt_le_one_half_of_scalar_lower_of_traceless_lt
Poincare/Global/NormalizedFlowFiniteTimePositiveRicci.lean:168:theorem ClosedSmoothRiemannianMetric.hasPosRicciAt_of_scalar_lower_of_traceless_lt
Poincare/Global/NormalizedFlowFiniteTimeHamiltonPinching.lean:97:def GlobalRicciEigenvalueFloor3
Poincare/Global/NormalizedFlowFiniteTimeHamiltonPinching.lean:111:def GlobalPinchingQuotientBound3
Poincare/Global/NormalizedFlowFiniteTimeHamiltonPinching.lean:117:theorem ClosedSmoothRiemannianMetric.globalRicciEigenvalueFloor_one_fourth_of_scalar_lower_of_traceless_lt
Poincare/Global/NormalizedFlowFiniteTimeHamiltonPinching.lean:149:theorem ClosedSmoothRiemannianMetric.globalPinchingQuotientBound_three_eighths_of_globalRicciEigenvalueFloor_one_fourth
Poincare/Global/MetricRescaleFiniteAtlasForwardFlow.lean:149:theorem meanScalar_forwardTimeReparameterizedConstRescaling_eq_base
Poincare/Global/MetricRescaleFiniteAtlasForwardFlow.lean:271:theorem meanScalar_forwardTimeReparameterizedConstRescaling_eq_base_of_baseDensityIntegrable
Poincare/Global/RicciNorm.lean:1546:noncomputable def pinchedTracelessAdmissibleDelta3 (ε : ℝ) : ℝ :=
Poincare/Global/RicciNorm.lean:1550:theorem pinchedTracelessAdmissibleDelta3_one_tenth :
Poincare/Global/RicciNorm.lean:1677:theorem pinchedTracelessAdmissibleDelta3_le_actual_min_bound
Poincare/Global/NormalizedFlowStokesBoundaryReduction.lean:45:def ClosedLaplacianStokes
Poincare/Global/HamiltonMeanFloorFromEnergyDomination.lean:51:theorem meanFloorFromEnergy
Poincare/Global/HamiltonMeanFloorFromEnergyDomination.lean:75:theorem meanFloorFromEnergy_of_initialMeanPos
Poincare/Global/NormalizedFlowPointwiseConvergence.lean:156:theorem meanScalar_limit_pos_of_tendsto_of_eventually_lower
Poincare/Global/NormalizedFlowForwardPointwiseTracelessEnergyDecay.lean:37:theorem normalizedFlowTracelessRicciEnergyTrack_le_mul_totalVolume_of_pointwise
Poincare/Global/NormalizedFlowForwardPointwiseTracelessEnergyDecay.lean:62:theorem normalizedFlowTracelessRicciEnergyTrack_le_initialVolume_mul_exp_of_pointwise_of_normalizedFlow_Ici
Poincare/Global/NormalizedFlowForwardPointwiseTracelessEnergyDecay.lean:93:theorem normalizedFlowTracelessRicciEnergyTrack_integrableOn_of_pointwise_exponential_decay_of_normalizedFlow_Ici
Poincare/Global/NormalizedFlowForwardPointwiseTracelessEnergyPinchingDomination.lean:105:theorem normalizedTracelessRicciEvolutionReactionAt_le_neg_rate_mul_of_eigenvalue_pinching_of_normalization_gap
Poincare/Global/NormalizedFlowForwardPointwiseTracelessEnergyPinchingDomination.lean:140:theorem normalizedTracelessRicciEvolutionReactionAt_le_neg_rate_mul_of_eigenvalue_pinching_of_quotient_scalar_mean
Poincare/Global/NormalizedFlowForwardPointwiseTracelessEnergyPinchingDomination.lean:203:theorem normalizedTracelessRicciEvolutionReactionAt_global_domination_of_pinching
Poincare/Global/NormalizedFlow.lean:91:structure IsClosedNormalizedRicciFlowSolutionAt
Poincare/Global/NormalizedFlowForwardFiniteDissipationReduction.lean:41:noncomputable def normalizedFlowScalarVarianceTrack
Poincare/Global/NormalizedFlowForwardFiniteDissipationReduction.lean:47:noncomputable def normalizedFlowTracelessRicciEnergyTrack
Poincare/Global/NormalizedFlowForwardFiniteDissipationReduction.lean:160:theorem normalizedFlowScalarVarianceTrack_integrableOn_iff_tracelessRicciEnergyTrack_integrableOn_of_normalizedFlow_Ici_of_deriv_nonneg_of_meanUpper
Poincare/Global/ScalarMeanLowerBound.lean:55:theorem meanScalar_le_of_forall_scalarAt_le
Poincare/Global/ScalarMeanLowerBound.lean:94:theorem meanScalar_pos_of_forall_scalarAt_ge
Poincare/Global/NormalizedFlowHamiltonPinchingQuotientFromEigenFloor.lean:32:theorem pinchingQuotientCoefficient_pos (epsilon : ℝ) :
Poincare/Global/MetricEntryThirdJetProfileCompactness.lean:40:theorem metricEntryThirdJetProfile_differentiable
Poincare/Global/ClosedMetricThirdJetTopology.lean:115:noncomputable def metricEntryThirdJetProfile (g : G) :
Poincare/Global/ClosedMetricThirdJetTopology.lean:124:theorem metricEntryThirdJetProfile_value_anchor
Poincare/Global/ClosedMetricThirdJetTopology.lean:146:theorem metricEntryThirdJetProfile_injective :
Poincare/Global/ClosedMetricThirdJetTopology.lean:197:theorem metricEntryThirdJetProfile_isEmbedding :
Poincare/Global/HamiltonFrontStatements.lean:83:def UniversalHamiltonConvergenceStatement : Prop :=
Poincare/Global/HamiltonReactionCoreFinal.lean:27:def HamiltonReactionCore3Final (M : Type u)
Poincare/Global/HamiltonReactionCoreFinal.lean:82:theorem hamiltonConvergencePinchedLimit3_of_hamiltonReactionCore3Final
Poincare/Global/HamiltonInitialPinchingReactionCoreReduction.lean:29:def HamiltonReactionCore3InitialPinching (M : Type u)
Poincare/Global/HamiltonInitialPinchingReactionCoreReduction.lean:59:theorem hamiltonReactionCore3Final_of_initialPinching
Poincare/Global/HamiltonInitialPinchingReactionCoreReduction.lean:86:def HamiltonReactionCore3InitialPinchingEta (M : Type u)
Poincare/Global/HamiltonInitialPinchingReactionCoreReduction.lean:116:theorem hamiltonReactionCore3Final_of_initialPinchingEta
Poincare/Global/HamiltonInitialPinchingReactionCoreReduction.lean:138:theorem hamiltonConvergencePinchedLimit3_of_hamiltonReactionCore3InitialPinching
Poincare/Global/HamiltonInitialPinchingReactionCoreReduction.lean:145:def UniversalHamiltonReactionCoreInitialPinchingStatement : Prop :=
Poincare/Global/HamiltonInitialPinchingReactionCoreReduction.lean:154:theorem universalHamiltonConvergence_of_universalHamiltonReactionCoreInitialPinching
Poincare/Global/MetricRescaleFiniteAtlasIntegrals.lean:258:theorem meanScalar_constSMul
Poincare/Global/MetricRescaleFiniteAtlasIntegrals.lean:300:theorem meanScalar_constSMul_of_baseDensityIntegrable
Poincare/Global/MetricRescaleFiniteAtlasIntegrals.lean:316:theorem meanScalar_timeReparameterizedConstRescaling_eq_base
Poincare/Global/MetricRescaleFiniteAtlasIntegrals.lean:406:theorem meanScalar_timeReparameterizedConstRescaling_eq_base_of_baseDensityIntegrable
Poincare/Global/ScalarIntegral.lean:65:noncomputable def meanScalar (g : ClosedSmoothRiemannianMetric n M) : ℝ :=
Poincare/Global/ScalarIntegral.lean:86:theorem meanScalar_of_forall_isEinsteinAt
Poincare/Global/ScalarIntegral.lean:99:theorem meanScalar_of_forall_isEinsteinAt_of_volume_ne_zero
Poincare/Global/NormalizedFlowForwardFiniteTimePositiveEinsteinMeanScalarEnergyDomination.lean:43:theorem meanScalar_deriv_nonneg_of_normalizedFlow_Ici_of_scalarVarianceTrack_le_six_tracelessRicciEnergyTrack
Poincare/Global/NormalizedFlowScalarIntegralVariation.lean:208:theorem meanScalar_mul_totalVolume_eq_totalScalar [Nonempty M]
Poincare/Global/NormalizedFlowCompactFiniteDissipationBoundedVariation.lean:46:theorem normalizedFlowScalarVarianceTrack_integrableOn_of_tracelessRicciEnergyTrack_integrableOn_of_normalizedFlow_Ici_of_meanLower_of_continuousTracks
Poincare/Global/HamiltonMeanFloorReduction.lean:87:theorem meanScalar_lower_profile_of_initial_scalar_pos
Poincare/Global/HamiltonMeanFloorReduction.lean:120:theorem meanScalar_floor_on_Icc_of_initial_scalar_pos
```

### final-tokens

Command: `rg -n '\b(sorry|admit|axiom|opaque)\b|native_decide' Poincare/Global/HamiltonInitialPinchingReactionCoreReduction.lean`. Exit: 1.

```text
```

### final-whitespace

Command: `git diff --check`. Exit: 0.

```text
```

### survey-target

Command: `lake env lean /tmp/hamilton-initial-pinching-reaction-core-evidence/survey-target.lean`. Exit: 0.

```text
```

The final dependency output was also parsed and checked for seven entries,
with each ordered list exactly equal to the required list. Actual output:

```text
All 7 declaration dependency lists equal [propext, Classical.choice, Quot.sound].
```

## Final proof diff

Command: `git diff 0bafde8403d953b99c8e5e51eefffc8ae89d057f fde6a5d496a8d22a89400214a6b794a09263eb7a -- Poincare/Global/HamiltonInitialPinchingReactionCoreReduction.lean`. Exit: 0.

```diff
diff --git a/Poincare/Global/HamiltonInitialPinchingReactionCoreReduction.lean b/Poincare/Global/HamiltonInitialPinchingReactionCoreReduction.lean
new file mode 100644
index 00000000..c3939adf
--- /dev/null
+++ b/Poincare/Global/HamiltonInitialPinchingReactionCoreReduction.lean
@@ -0,0 +1,162 @@
+import Poincare.Global.NormalizedFlowInitialPinchingPreservation
+import Poincare.Global.HamiltonMeanFloorFromEnergyDomination
+import Poincare.Global.HamiltonReactionCoreFinal
+import Poincare.Global.NormalizedFlowForwardPointwiseTracelessEnergyPinchingDomination
+
+/-!
+# Reaction core from initial pinching and explicit residual estimates
+
+Initial pinching supplies the forward eigenvalue floor and Ricci quotient
+bound. Energy domination and scalar Stokes supply the positive mean floor.
+The scalar-to-mean comparison and strict coefficient gap supply a uniform
+reaction rate. Existence of these data remains an input.
+-/
+
+set_option autoImplicit false
+noncomputable section
+open Set Filter MeasureTheory
+open scoped Manifold ContDiff Topology
+universe u v
+namespace Poincare.HamiltonInitialPinchingReactionCoreReduction
+
+variable {M : Type u} [TopologicalSpace M] [T2Space M]
+  [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]
+  [ChartedSpace (ClosedSmoothModel 3) M]
+  [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
+  [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M]
+
+/-- The survey's initial-data core, with all residual estimates displayed. -/
+def HamiltonReactionCore3InitialPinching (M : Type u)
+    [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
+    [MeasurableSpace M] [BorelSpace M]
+    [ChartedSpace (ClosedSmoothModel 3) M]
+    [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
+    [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M] : Prop :=
+  ∃ (K : Type v) (topK : TopologicalSpace K) (_ : @CompactSpace K topK)
+    (metric : K → ClosedSmoothRiemannianMetric 3 M)
+    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
+    (parameter : Ici (0 : ℝ) → K) (epsilon delta C : ℝ),
+      Continuous parameter ∧
+      (∀ t : Ici (0 : ℝ), metric (parameter t) = gt t.1) ∧
+      (∀ slot : MetricEntryThirdJetSlot 3 M,
+        Continuous (fun p : K × ClosedSmoothModel 3 ↦
+          metricEntryThirdJetProfile (metric p.1) slot p.2)) ∧
+      (∀ t x, MetricEntriesJointContDiffAt gt t x 3) ∧
+      (∀ t ∈ Ici (0 : ℝ), ∀ x, IsClosedNormalizedRicciFlowSolutionAt gt t x) ∧
+      (∀ x, 0 < (gt 0).scalarAt x) ∧
+      1/6 < epsilon ∧ epsilon ≤ 1/3 ∧
+      GlobalRicciEigenvalueFloor3 (gt 0) epsilon ∧
+      0 < delta ∧ delta ≤ 1 ∧
+      delta ≤ PinchingAlgebra.pinchedTracelessAdmissibleDelta3 (2 * epsilon - 1/3) ∧
+      (∀ t ∈ Ici (0 : ℝ), ClosedLaplacianStokes (gt t) (fun x ↦ (gt t).scalarAt x)) ∧
+      (∀ t : Ici (0 : ℝ), normalizedFlowScalarVarianceTrack gt t.1 ≤
+        6 * normalizedFlowTracelessRicciEnergyTrack gt t.1) ∧
+      (∀ t ∈ Ici (0 : ℝ), ∀ x, (gt t).scalarAt x ≤ C * meanScalar (gt t)) ∧
+      0 < (4/3 : ℝ) - 2 * (2 - delta) * (1 - 4 * epsilon + 6 * epsilon^2) * C
+
+/-- Initial pinching and the residual estimates reconstruct the final core,
+with rate equal to the coefficient gap times the initial mean scalar. -/
+theorem hamiltonReactionCore3Final_of_initialPinching
+    (h : HamiltonReactionCore3InitialPinching.{u, v} M) :
+    HamiltonReactionCore3Final.{u, v} M := by
+  rcases h with ⟨K, topK, compactK, metric, gt, parameter, epsilon, delta, C,
+    hparam, hreal, hjet, hjoint, hflow, hinit, hepos, hele, hpin,
+    hdpos, hdle, hadm, hstokes, henergy, hcompare, hgap⟩
+  letI : TopologicalSpace K := topK
+  haveI : CompactSpace K := compactK
+  let c : ℝ := meanScalar (gt 0)
+  let gamma : ℝ := (4/3 : ℝ) - 2 * (2 - delta) * (1 - 4 * epsilon + 6 * epsilon^2) * C
+  have hfloor := HamiltonMeanFloorFromEnergyDomination.meanFloorFromEnergy
+    gt hjoint hflow hstokes hinit henergy
+  have hpos := NormalizedFlowInitialPinchingPreservation.scalarAt_pos_of_initial_scalar_pos
+    gt hjoint hflow hinit
+  have hpres := NormalizedFlowInitialPinchingPreservation.initial_pinching_preserved
+    gt epsilon hjoint hflow hinit hele hpin
+  refine ⟨K, topK, compactK, gt, metric, parameter, c, gamma * c,
+    hparam, hreal, hfloor.1, hfloor.2, hflow, hjoint,
+    mul_pos hgap hfloor.1, ?_, hjet⟩
+  intro t ht
+  exact normalizedTracelessRicciEvolutionReactionAt_global_domination_of_pinching
+    (gt t) (by linarith) (by linarith) hdpos.le (by linarith) hadm
+    (pinchingQuotientCoefficient_pos epsilon).le (hpos t ht)
+    (hpres t ht).1 (hpres t ht).2 (hcompare t ht)
+    (mul_le_mul_of_nonneg_left (hfloor.2 ⟨t, ht⟩) hgap.le)
+
+/-- Initial pinching with a direct uniform positive normalization gap. -/
+def HamiltonReactionCore3InitialPinchingEta (M : Type u)
+    [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
+    [MeasurableSpace M] [BorelSpace M]
+    [ChartedSpace (ClosedSmoothModel 3) M]
+    [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
+    [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M] : Prop :=
+  ∃ (K : Type v) (topK : TopologicalSpace K) (_ : @CompactSpace K topK)
+    (metric : K → ClosedSmoothRiemannianMetric 3 M)
+    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
+    (parameter : Ici (0 : ℝ) → K) (epsilon delta : ℝ),
+      Continuous parameter ∧
+      (∀ t : Ici (0 : ℝ), metric (parameter t) = gt t.1) ∧
+      (∀ slot : MetricEntryThirdJetSlot 3 M,
+        Continuous (fun p : K × ClosedSmoothModel 3 ↦
+          metricEntryThirdJetProfile (metric p.1) slot p.2)) ∧
+      (∀ t x, MetricEntriesJointContDiffAt gt t x 3) ∧
+      (∀ t ∈ Ici (0 : ℝ), ∀ x, IsClosedNormalizedRicciFlowSolutionAt gt t x) ∧
+      (∀ x, 0 < (gt 0).scalarAt x) ∧
+      1/6 < epsilon ∧ epsilon ≤ 1/3 ∧
+      GlobalRicciEigenvalueFloor3 (gt 0) epsilon ∧
+      0 < delta ∧ delta ≤ 1 ∧
+      delta ≤ PinchingAlgebra.pinchedTracelessAdmissibleDelta3 (2 * epsilon - 1/3) ∧
+      (∀ t ∈ Ici (0 : ℝ), ClosedLaplacianStokes (gt t) (fun x ↦ (gt t).scalarAt x)) ∧
+      (∀ t : Ici (0 : ℝ), normalizedFlowScalarVarianceTrack gt t.1 ≤
+        6 * normalizedFlowTracelessRicciEnergyTrack gt t.1) ∧
+      (∃ eta : ℝ, 0 < eta ∧ ∀ t ∈ Ici (0 : ℝ), ∀ x,
+        2 * (2-delta) * (gt t).ricciNormSqAt x / (gt t).scalarAt x + eta ≤
+          (4/3 : ℝ) * meanScalar (gt t))
+
+/-- The direct normalization gap supplies the final core with rate `eta`. -/
+theorem hamiltonReactionCore3Final_of_initialPinchingEta
+    (h : HamiltonReactionCore3InitialPinchingEta.{u, v} M) :
+    HamiltonReactionCore3Final.{u, v} M := by
+  rcases h with ⟨K, topK, compactK, metric, gt, parameter, epsilon, delta,
+    hparam, hreal, hjet, hjoint, hflow, hinit, hepos, hele, hpin,
+    hdpos, hdle, hadm, hstokes, henergy, eta, heta, hgap⟩
+  letI : TopologicalSpace K := topK
+  haveI : CompactSpace K := compactK
+  have hfloor := HamiltonMeanFloorFromEnergyDomination.meanFloorFromEnergy
+    gt hjoint hflow hstokes hinit henergy
+  have hpos := NormalizedFlowInitialPinchingPreservation.scalarAt_pos_of_initial_scalar_pos
+    gt hjoint hflow hinit
+  have hpres := NormalizedFlowInitialPinchingPreservation.initial_pinching_preserved
+    gt epsilon hjoint hflow hinit hele hpin
+  refine ⟨K, topK, compactK, gt, metric, parameter, meanScalar (gt 0), eta,
+    hparam, hreal, hfloor.1, hfloor.2, hflow, hjoint, heta, ?_, hjet⟩
+  intro t ht x
+  exact normalizedTracelessRicciEvolutionReactionAt_le_neg_rate_mul_of_eigenvalue_pinching_of_normalization_gap
+    (gt t) x (by linarith) (by linarith) hdpos.le hadm (hpos t ht x)
+    ((hpres t ht).1 x) (hgap t ht x)
+
+/-- The sufficient initial-pinching core reaches the Hamilton endpoint. -/
+theorem hamiltonConvergencePinchedLimit3_of_hamiltonReactionCore3InitialPinching
+    (h : HamiltonReactionCore3InitialPinching.{u, v} M) : HamiltonConvergencePinchedLimit3 M :=
+  hamiltonConvergencePinchedLimit3_of_hamiltonReactionCore3Final
+    (hamiltonReactionCore3Final_of_initialPinching h)
+
+/-- Open existence obligation for initial-pinching cores on every compatible
+Borel structure of a closed simply connected smooth three-manifold. -/
+def UniversalHamiltonReactionCoreInitialPinchingStatement : Prop :=
+  ∀ (N : Type u) [TopologicalSpace N] [T2Space N] [SecondCountableTopology N]
+    [MeasurableSpace N] [BorelSpace N]
+    [ChartedSpace (ClosedSmoothModel 3) N]
+    [IsManifold (closedSmoothModelWithCorners 3) ∞ N]
+    [CompactSpace N] [ConnectedSpace N] [SimplyConnectedSpace N],
+      HamiltonReactionCore3InitialPinching.{u, v} N
+
+/-- Universal initial-pinching cores imply universal Hamilton convergence. -/
+theorem universalHamiltonConvergence_of_universalHamiltonReactionCoreInitialPinching
+    (h : UniversalHamiltonReactionCoreInitialPinchingStatement.{u, v}) :
+    UniversalHamiltonConvergenceStatement.{u} := by
+  intro N _ _ _ _ _ _ _ _
+  letI : MeasurableSpace N := borel N
+  letI : BorelSpace N := ⟨rfl⟩
+  exact hamiltonConvergencePinchedLimit3_of_hamiltonReactionCore3InitialPinching (h N)
+
+end Poincare.HamiltonInitialPinchingReactionCoreReduction
```

## Handoff

First action for the orchestrator:

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HamiltonInitialPinchingReactionCoreReduction.lean
```

Independently review the diff against the recorded base and rerun the focused
contract gate before acceptance. Root import wiring and integration audits
remain the orchestrator's work.

## Delivery whitespace checks

Command: `git diff --check`. Exit: 0. Actual output:

```text
```

Command: `git diff --cached --check`, including the new report. Exit: 0.
Actual output:

```text
```
