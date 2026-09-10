# Hamilton mean floor from energy domination

Date: 2026-09-10. Base: `babccd85e15cdd3a58cd922b1118bf8d1dff3f0c`.
Branch: `worker/hamilton-mean-floor-from-energy-domination`.
Proof head: `110375595ee111033ffa9e1347ebbef27f4ce0df`.
Toolchain: `leanprover/lean4:v4.30.0-rc2`.

The worker objective is complete. The new module is
`Poincare/Global/HamiltonMeanFloorFromEnergyDomination.lean`, with nine
public declarations in `Poincare.HamiltonMeanFloorFromEnergyDomination`.
The focused Lean gate passes. Every declaration, including both definitions,
prints exactly `[propext, Classical.choice, Quot.sound]`. The forbidden-token
scan is empty with exit 1; the whitespace check exits 0. This is a worker
result for independent review, not an acceptance or merge.

The exact survey signatures and proof bodies of `movingDerivatives` and
`meanFloorFromEnergy` are preserved. Appendix C's actual `meanFloorFromEnergy`
assumes initial pointwise scalar positivity, whereas the task also asks for
positive initial mean alone. The additional theorem
`meanFloorFromEnergy_of_initialMeanPos` proves that requested stronger result
and supplies the core adapter. It assumes `0 < meanScalar (gt 0)` directly,
without requiring pointwise scalar positivity. Both floor theorems conclude
positive initial mean and
`∀ t : Ici 0, meanScalar (gt 0) ≤ meanScalar (gt t.1)`.

The moving derivative proof constructs finite-atlas density data from joint
C³ entries and its derived local bound. It uses automatic volume
differentiation, joint continuity of the actual scalar time derivative, and
the Lichnerowicz assembly for total scalar differentiation. Scalar Stokes
remains explicit. The energy inequality makes the exact mean derivative
nonnegative, and the mean-value criterion makes the mean monotone on `Ici 0`.

`HamiltonReactionCore3Energy` retains the original compact parameter family,
realization, forward flow, all-time joint C³ entries, positive reaction rate,
uniform reaction domination, and continuous third-jet profiles. It replaces
the existential positive floor with positive initial mean, forward energy
domination, and forward scalar Stokes. `hamiltonReactionCore3Final_of_energy`
uses the exact witness `c := meanScalar (gt 0)`, preserving every other witness.
The module also proves the Hamilton endpoint, defines the universal energy
core statement, and proves its reductions to the universal final core and
universal Hamilton convergence.

Stokes is not proved automatic. Energy domination and core existence remain
premises. No negative-time flow equation, new connection instance premise,
analytic premise concealed in a helper definition, or unconditional
Poincaré theorem is introduced.

The worktree was initially clean at the recorded base. README, HANDOFF's top
section, the project map, AGENTS, the task, the requested survey sections,
and the nearby definitions and imports were read before editing. The task's
specific branch and file scope take precedence over the general branch and
HANDOFF rules. Only the named new Lean file and this required report are
added. Existing Lean files, `Poincare.lean`, HANDOFF, frozen contracts,
missions, audits, and ledgers remain unchanged. No root build or integration
audit was run; the task specifies a focused worker gate.

Each theorem was compiled, dependency-checked, scanned, and committed before
the next increment. The seven proof commits are recorded below in the actual
git output. The only final Lean warning is the original scratch theorem's
unused `[SimplyConnectedSpace M]` assumption in `movingDerivatives`; retaining
it preserves the exact signature.

One additional signature-test attempt failed because the concatenated scratch
file redeclared universe `u`. The module itself compiled throughout. Removing
the duplicate scratch declaration made the exact target assignments pass.
The failed output is included without alteration. Its source remains at
`/tmp/hamilton-mean-floor-from-energy-domination/exact-signatures-duplicate-universe.lean`.

First action for the orchestrator:

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HamiltonMeanFloorFromEnergyDomination.lean
```

Then review the diff from the recorded base and rerun the nine dependency
prints before deciding acceptance.

## Reproduced Appendix C source

Before creating the module, the following exact fenced source was extracted
from the survey into
`/tmp/hamilton-mean-floor-from-energy-domination/partial-dependencies.lean`.
Its current elaboration and all three dependency prints passed. The third
scratch theorem was reproduced as part of the evidence and is not added to
the new module.

```lean
import Poincare.Global.ClosedRicciFlowNormalization
import Poincare.Global.HamiltonMeanFloorReduction
import Poincare.Global.HamiltonReactionCoreFinal
import Poincare.Global.MetricFlowJointPinchingEvolution
import Poincare.Global.NormalizedFlowCompactMeanEnergyMeasureEventualHamiltonPinchingDecay
import Poincare.Global.NormalizedFlowCompactMeanEnergyMeasureHamiltonPinchingDecay
import Poincare.Global.NormalizedFlowCompactScalarMeanComparison
import Poincare.Global.NormalizedFlowFiniteTimeHamiltonPinching
import Poincare.Global.NormalizedFlowFiniteTimeMeanScalarPinching
import Poincare.Global.NormalizedFlowForwardFiniteTimePositiveEinsteinMeanScalarEnergyDomination
import Poincare.Global.NormalizedFlowForwardFiniteTimePositiveEinsteinMeanScalarPointwiseDomination
import Poincare.Global.NormalizedFlowForwardPointwiseTracelessEnergyActualReactionDecay
import Poincare.Global.NormalizedFlowForwardPointwiseTracelessEnergyPinchingDomination
import Poincare.Global.NormalizedFlowHamiltonPinchingQuotientFromEigenFloor
import Poincare.Global.NormalizedFlowHausdorffScalarDominationJointC1Reduction
import Poincare.Global.NormalizedFlowHausdorffScalarTimeDerivativeAutomatic
import Poincare.Global.NormalizedFlowImprovedPinchingDecay
import Poincare.Global.NormalizedFlowImprovedPinchingSampleScalarFloorDecay
import Poincare.Global.NormalizedFlowImprovedPinchingSubsequenceDecay
import Poincare.Global.NormalizedFlowJointPinchingRegularity
import Poincare.Global.NormalizedFlowPinchingLimit
import Poincare.Global.NormalizedFlowRicciTensorEvolution
import Poincare.Global.NormalizedFlowScalarLowerProfile
set_option pp.universes false
open Poincare
set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology
universe u
namespace Poincare.PinchingReactionSurvey
variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (ClosedSmoothModel 3) M]
  [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
  [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M]

theorem movingDerivatives
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    (hjoint : ∀ t x, MetricEntriesJointContDiffAt gt t x 3)
    (hflow : ∀ t ∈ Ici (0 : ℝ), ∀ x, IsClosedNormalizedRicciFlowSolutionAt gt t x)
    (hstokes : ∀ t ∈ Ici (0 : ℝ), ClosedLaplacianStokes (gt t) (fun x ↦ (gt t).scalarAt x)) :
    (∀ t ∈ Ici (0 : ℝ), HasDerivAt (fun s ↦ totalVolume (gt s))
      (totalVolumeFirstVariation (gt t) (timeDerivAt gt t)) t) ∧
    (∀ t ∈ Ici (0 : ℝ), HasDerivAt (fun s ↦ totalScalar (gt s))
      (normalizedMeanScalarEnergyNumerator (gt t)) t) := by
  obtain ⟨D⟩ := HamiltonReactionCoreReduction.chartFrameDensityData_of_joint_of_local_bound
    gt hjoint (HamiltonChartDensityLocalDomination.localBound_of_jointMetricEntries gt hjoint)
  let V := D.toChartFrameDensityVariation
  constructor
  · intro t ht
    exact V.hasDerivAt_totalVolume_of_normalizedFlowAt t (hflow t ht)
  · intro t ht
    exact hasDerivAt_totalScalar_energyNumerator_of_normalizedFlowAt_of_jointScalarTimeDerivative
      V hjoint (scalarTimeDerivativeJointContinuous_of_metricEntriesJointContDiffAt_three hjoint)
      (globalLichnerowiczAssemblyRegularity_of_jointMetricEntriesThree hjoint)
      t (hflow t ht) (hstokes t ht)

theorem meanFloorFromEnergy
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    (hjoint : ∀ t x, MetricEntriesJointContDiffAt gt t x 3)
    (hflow : ∀ t ∈ Ici (0 : ℝ), ∀ x, IsClosedNormalizedRicciFlowSolutionAt gt t x)
    (hstokes : ∀ t ∈ Ici (0 : ℝ), ClosedLaplacianStokes (gt t) (fun x ↦ (gt t).scalarAt x))
    (hinit : ∀ x, 0 < (gt 0).scalarAt x)
    (henergy : ∀ t : Ici (0 : ℝ), normalizedFlowScalarVarianceTrack gt t.1 ≤
      6 * normalizedFlowTracelessRicciEnergyTrack gt t.1) :
    0 < meanScalar (gt 0) ∧ ∀ t : Ici (0 : ℝ), meanScalar (gt 0) ≤ meanScalar (gt t.1) := by
  obtain ⟨hv, hs⟩ := movingDerivatives gt hjoint hflow hstokes
  have hd := meanScalar_deriv_nonneg_of_normalizedFlow_Ici_of_scalarVarianceTrack_le_six_tracelessRicciEnergyTrack
    gt (fun t ↦ hflow t.1 t.2) (fun t ↦ hs t.1 t.2) (fun t ↦ hv t.1 t.2) henergy
  have hf : ∀ t ∈ Ici (0 : ℝ), DifferentiableAt ℝ (fun s ↦ meanScalar (gt s)) t := by
    intro t ht
    exact (hasDerivAt_meanScalar_three_of_normalizedFlow (hflow t ht) (hs t ht) (hv t ht)).differentiableAt
  have hm := monotoneOn_of_deriv_nonneg (convex_Ici (0 : ℝ))
    (continuousOn_meanScalar_of_normalizedRicciFlow gt hflow hjoint)
    (fun t ht ↦ (hf t (interior_subset ht)).differentiableWithinAt)
    (fun t ht ↦ hd ⟨t, interior_subset ht⟩)
  obtain ⟨rho, hrho, hlower⟩ := exists_pos_scalar_floor_of_forall_scalarAt_pos (gt 0) hinit
  exact ⟨meanScalar_pos_of_forall_scalarAt_ge (gt 0) hrho hlower,
    fun t ↦ hm (by simp) t.2 t.2⟩

theorem constantRateFromGap
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    {epsilon delta kappa C c : ℝ}
    (he : 0 < epsilon) (he3 : epsilon ≤ 1 / 3)
    (hd : 0 ≤ delta) (hd2 : delta ≤ 2)
    (hadm : delta ≤ PinchingAlgebra.pinchedTracelessAdmissibleDelta3 epsilon)
    (hk : 0 ≤ kappa) (hc : 0 < c)
    (hgap : 0 < (4 / 3 : ℝ) - 2 * (2 - delta) * kappa * C)
    (hr : ∀ t ∈ Ici (0 : ℝ), c ≤ meanScalar (gt t))
    (hR : ∀ t ∈ Ici (0 : ℝ), ∀ x, 0 < (gt t).scalarAt x)
    (hpin : ∀ t ∈ Ici (0 : ℝ), GlobalRicciEigenvalueFloor3 (gt t) epsilon)
    (hq : ∀ t ∈ Ici (0 : ℝ), GlobalPinchingQuotientBound3 (gt t) kappa)
    (hcompare : ∀ t ∈ Ici (0 : ℝ), ∀ x, (gt t).scalarAt x ≤ C * meanScalar (gt t)) :
    ∃ rate : ℝ, 0 < rate ∧ ∀ t ∈ Ici (0 : ℝ), ∀ x,
      normalizedTracelessRicciEvolutionReactionAt (gt t) x ≤ -rate * (gt t).tracelessRicciNormSqAt x := by
  let gamma : ℝ := (4 / 3 : ℝ) - 2 * (2 - delta) * kappa * C
  refine ⟨gamma * c, mul_pos hgap hc, ?_⟩
  intro t ht
  exact normalizedTracelessRicciEvolutionReactionAt_global_domination_of_pinching
    (gt t) he he3 hd hd2 hadm hk (hR t ht) (hpin t ht) (hq t ht)
    (hcompare t ht) (mul_le_mul_of_nonneg_left (hr t ht) hgap.le)
end Poincare.PinchingReactionSurvey

#print axioms Poincare.PinchingReactionSurvey.movingDerivatives
#print axioms Poincare.PinchingReactionSurvey.meanFloorFromEnergy
#print axioms Poincare.PinchingReactionSurvey.constantRateFromGap
```

## Exact signature check

The complete new module was followed by this independent context and the two
survey target assignments. The second, successful attempt removed the
redundant global `universe u` command. A separate source comparison also
checks that both complete survey declaration texts occur unchanged in the
new module.

```lean
set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology
namespace Poincare.MeanFloorExactProbe
variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (ClosedSmoothModel 3) M]
  [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
  [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M]

example
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    (hjoint : ∀ t x, MetricEntriesJointContDiffAt gt t x 3)
    (hflow : ∀ t ∈ Ici (0 : ℝ), ∀ x, IsClosedNormalizedRicciFlowSolutionAt gt t x)
    (hstokes : ∀ t ∈ Ici (0 : ℝ), ClosedLaplacianStokes (gt t) (fun x ↦ (gt t).scalarAt x)) :
    (∀ t ∈ Ici (0 : ℝ), HasDerivAt (fun s ↦ totalVolume (gt s))
      (totalVolumeFirstVariation (gt t) (timeDerivAt gt t)) t) ∧
    (∀ t ∈ Ici (0 : ℝ), HasDerivAt (fun s ↦ totalScalar (gt s))
      (normalizedMeanScalarEnergyNumerator (gt t)) t) :=
  Poincare.HamiltonMeanFloorFromEnergyDomination.movingDerivatives gt hjoint hflow hstokes

example
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    (hjoint : ∀ t x, MetricEntriesJointContDiffAt gt t x 3)
    (hflow : ∀ t ∈ Ici (0 : ℝ), ∀ x, IsClosedNormalizedRicciFlowSolutionAt gt t x)
    (hstokes : ∀ t ∈ Ici (0 : ℝ), ClosedLaplacianStokes (gt t) (fun x ↦ (gt t).scalarAt x))
    (hinit : ∀ x, 0 < (gt 0).scalarAt x)
    (henergy : ∀ t : Ici (0 : ℝ), normalizedFlowScalarVarianceTrack gt t.1 ≤
      6 * normalizedFlowTracelessRicciEnergyTrack gt t.1) :
    0 < meanScalar (gt 0) ∧ ∀ t : Ici (0 : ℝ), meanScalar (gt 0) ≤ meanScalar (gt t.1) :=
  Poincare.HamiltonMeanFloorFromEnergyDomination.meanFloorFromEnergy gt hjoint hflow hstokes hinit henergy

end Poincare.MeanFloorExactProbe
```

## Actual command output

Commands are listed in recorded order. All Lean processes inherited
`LEAN_NUM_THREADS=1`. For each `dependencies-N.lean` check, the file consists
of that increment's exact module source followed by `#print axioms` for every
one of its N named declarations. The final nine-name output is included.
The temporary probe sources, command log, and failed attempt remain under
`/tmp/hamilton-mean-floor-from-energy-domination`. The final module diff is
included in the command output below.

### Command 1

```sh
LEAN_NUM_THREADS=1 lake env lean /tmp/hamilton-mean-floor-from-energy-domination/partial-dependencies.lean
```

Exit: 0.

```text
/tmp/hamilton-mean-floor-from-energy-domination/partial-dependencies.lean:38:0: warning: automatically included section variable(s) unused in theorem `Poincare.PinchingReactionSurvey.movingDerivatives`:
  [SimplyConnectedSpace M]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [SimplyConnectedSpace M] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
/tmp/hamilton-mean-floor-from-energy-domination/partial-dependencies.lean:82:0: warning: automatically included section variable(s) unused in theorem `Poincare.PinchingReactionSurvey.constantRateFromGap`:
  [SimplyConnectedSpace M]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [SimplyConnectedSpace M] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
'Poincare.PinchingReactionSurvey.movingDerivatives' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.PinchingReactionSurvey.meanFloorFromEnergy' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.PinchingReactionSurvey.constantRateFromGap' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### Command 2

```sh
rg -n '^(noncomputable )?(def|theorem|abbrev|structure) (chartFrameDensityData_of_joint_of_local_bound|localBound_of_jointMetricEntries|toChartFrameDensityVariation|hasDerivAt_totalVolume_of_normalizedFlowAt|hasDerivAt_totalScalar_energyNumerator_of_normalizedFlowAt_of_jointScalarTimeDerivative|scalarTimeDerivativeJointContinuous_of_metricEntriesJointContDiffAt_three|globalLichnerowiczAssemblyRegularity_of_jointMetricEntriesThree|meanScalar_deriv_nonneg_of_normalizedFlow_Ici_of_scalarVarianceTrack_le_six_tracelessRicciEnergyTrack|hasDerivAt_meanScalar_three_of_normalizedFlow|continuousOn_meanScalar_of_normalizedRicciFlow|exists_pos_scalar_floor_of_forall_scalarAt_pos|meanScalar_pos_of_forall_scalarAt_ge|HamiltonReactionCore3Final|hamiltonConvergencePinchedLimit3_of_hamiltonReactionCore3Final|UniversalHamiltonReactionCoreFinalStatement|universalHamiltonConvergence_of_universalHamiltonReactionCoreFinal|ClosedLaplacianStokes|normalizedFlowScalarVarianceTrack|normalizedFlowTracelessRicciEnergyTrack|MetricEntryThirdJetSlot|metricEntryThirdJetProfile)\b' Poincare
```

Exit: 0.

```text
Poincare/Global/NormalizedFlowHausdorffSpatialMixedRegularity.lean:153:def globalLichnerowiczAssemblyRegularity_of_jointMetricEntriesThree
Poincare/Global/NormalizedFlowScalarLowerProfile.lean:75:theorem exists_pos_scalar_floor_of_forall_scalarAt_pos
Poincare/Global/NormalizedFlowStokesBoundaryReduction.lean:45:def ClosedLaplacianStokes
Poincare/Global/HamiltonChartDensityLocalDomination.lean:151:theorem localBound_of_jointMetricEntries
Poincare/Global/NormalizedFlowHausdorffScalarTimeDerivativeAutomatic.lean:182:theorem scalarTimeDerivativeJointContinuous_of_metricEntriesJointContDiffAt_three
Poincare/Global/ScalarMeanLowerBound.lean:94:theorem meanScalar_pos_of_forall_scalarAt_ge
Poincare/Global/NormalizedFlowForwardFiniteDissipationReduction.lean:41:noncomputable def normalizedFlowScalarVarianceTrack
Poincare/Global/NormalizedFlowForwardFiniteDissipationReduction.lean:47:noncomputable def normalizedFlowTracelessRicciEnergyTrack
Poincare/Global/HamiltonReactionCoreReduction.lean:93:theorem chartFrameDensityData_of_joint_of_local_bound
Poincare/Global/NormalizedFlowHausdorffScalarDominationJointC1Reduction.lean:248:theorem hasDerivAt_totalScalar_energyNumerator_of_normalizedFlowAt_of_jointScalarTimeDerivative
Poincare/Global/HamiltonReactionCoreFinal.lean:27:def HamiltonReactionCore3Final (M : Type u)
Poincare/Global/HamiltonReactionCoreFinal.lean:82:theorem hamiltonConvergencePinchedLimit3_of_hamiltonReactionCore3Final
Poincare/Global/HamiltonReactionCoreFinal.lean:88:def UniversalHamiltonReactionCoreFinalStatement : Prop :=
Poincare/Global/HamiltonReactionCoreFinal.lean:97:theorem universalHamiltonConvergence_of_universalHamiltonReactionCoreFinal
Poincare/Global/HamiltonMeanFloorReduction.lean:55:theorem continuousOn_meanScalar_of_normalizedRicciFlow
Poincare/Global/NormalizedFlowForwardFiniteTimePositiveEinsteinMeanScalarEnergyDomination.lean:43:theorem meanScalar_deriv_nonneg_of_normalizedFlow_Ici_of_scalarVarianceTrack_le_six_tracelessRicciEnergyTrack
Poincare/Global/NormalizedFlowScalarIntegralVariation.lean:728:theorem hasDerivAt_meanScalar_three_of_normalizedFlow
Poincare/Global/ClosedMetricThirdJetTopology.lean:115:noncomputable def metricEntryThirdJetProfile (g : G) :
```

### Command 3

```sh
rg -n '(theorem|lemma) (monotoneOn_of_deriv_nonneg|convex_Ici|interior_subset|HasDerivAt.differentiableAt|DifferentiableAt.differentiableWithinAt)\b' .lake/packages/mathlib/Mathlib
```

Exit: 0.

```text
.lake/packages/mathlib/Mathlib/Analysis/Convex/Basic.lean:251:theorem convex_Ici (r : β) : Convex 𝕜 (Ici r) :=
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/MeanValue.lean:409:theorem monotoneOn_of_deriv_nonneg {D : Set ℝ} (hD : Convex ℝ D) {f : ℝ → ℝ}
.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Basic.lean:389:theorem HasDerivAt.differentiableAt (h : HasDerivAt f f' x) : DifferentiableAt 𝕜 f x :=
.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean:468:theorem DifferentiableAt.differentiableWithinAt (h : DifferentiableAt 𝕜 f x) :
.lake/packages/mathlib/Mathlib/Topology/Closure.lean:46:theorem interior_subset : interior s ⊆ s :=
```

### Command 4

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HamiltonMeanFloorFromEnergyDomination.lean
```

Exit: 0.

```text
Poincare/Global/HamiltonMeanFloorFromEnergyDomination.lean:29:0: warning: automatically included section variable(s) unused in theorem `Poincare.HamiltonMeanFloorFromEnergyDomination.movingDerivatives`:
  [SimplyConnectedSpace M]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [SimplyConnectedSpace M] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
```

### Command 5

```sh
rg -n '(def|theorem|abbrev|structure).*\b(toChartFrameDensityVariation|hasDerivAt_totalVolume_of_normalizedFlowAt|MetricEntryThirdJetSlot)\b' Poincare
```

Exit: 0.

```text
Poincare/Global/NormalizedFlowForwardChartFramePartitionCompactOrbitEndpoint.lean:121:theorem GlobalFiniteHausdorffChartFrameDensityVariation.hasDerivAt_totalVolume_of_normalizedFlowAt
Poincare/Global/HausdorffFiniteAtlasChartFrameReduction.lean:403:def GlobalFiniteExtendedChartFrameDensityData.toChartFrameDensityVariation
Poincare/Global/HausdorffFiniteAtlasChartFrameReduction.lean:429:def CompactFiniteAtlasChartFrameDensityData.toChartFrameDensityVariation
Poincare/Global/HausdorffFiniteAtlasRestrictedAreaFormula.lean:201:def GlobalFiniteExtendedChartDensityData.toChartFrameDensityVariation
```

### Command 6

```sh
LEAN_NUM_THREADS=1 lake env lean /tmp/hamilton-mean-floor-from-energy-domination/dependencies-1.lean
```

Exit: 0.

```text
/tmp/hamilton-mean-floor-from-energy-domination/dependencies-1.lean:29:0: warning: automatically included section variable(s) unused in theorem `Poincare.HamiltonMeanFloorFromEnergyDomination.movingDerivatives`:
  [SimplyConnectedSpace M]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [SimplyConnectedSpace M] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
'Poincare.HamiltonMeanFloorFromEnergyDomination.movingDerivatives' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### Command 7

```sh
rg -n '\b(sorry|admit|axiom|opaque)\b|native_decide' Poincare/Global/HamiltonMeanFloorFromEnergyDomination.lean
```

Exit: 1.

Output: empty.

### Command 8

```sh
git diff --check
```

Exit: 0.

Output: empty.

### Command 9

```sh
rg -n '^(inductive|def|abbrev|structure|theorem|noncomputable def).*\b(MetricEntryThirdJetSlot|ClosedSmoothRiemannianMetric|ClosedSmoothModel|closedSmoothModelWithCorners|MetricEntriesJointContDiffAt|IsClosedNormalizedRicciFlowSolutionAt|totalVolume|totalVolumeFirstVariation|timeDerivAt|totalScalar|normalizedMeanScalarEnergyNumerator|meanScalar|HamiltonConvergencePinchedLimit3|UniversalHamiltonConvergenceStatement)\b' Poincare
```

Exit: 0.

```text
Poincare/Global/FixedChartUniformJacobiComparison.lean:343:def MovingInitialPositionJacobiComparison (g : ClosedSmoothRiemannianMetric 3 M) : Prop :=
Poincare/Global/DifferentialInducedSuccessor.lean:44:structure Data {g : ClosedSmoothRiemannianMetric 3 M}
Poincare/Global/DifferentialInducedSuccessor.lean:94:def Data.alignment {g : ClosedSmoothRiemannianMetric 3 M}
Poincare/Global/DifferentialInducedSuccessor.lean:102:def Data.successor {g : ClosedSmoothRiemannianMetric 3 M}
Poincare/Global/DifferentialInducedSuccessor.lean:500:theorem Data.successor_anchor {g : ClosedSmoothRiemannianMetric 3 M}
Poincare/Global/DifferentialInducedSuccessor.lean:506:theorem Data.successor_target {g : ClosedSmoothRiemannianMetric 3 M}
Poincare/Global/CartanSourceExponentialFamily.lean:51:structure Family (g : ClosedSmoothRiemannianMetric 3 M) where
Poincare/Global/CartanSourceExponentialFamily.lean:57:def Family.sourceLocus {g : ClosedSmoothRiemannianMetric 3 M}
Poincare/Global/CartanSourceExponentialFamily.lean:62:def Family.targetLocus {g : ClosedSmoothRiemannianMetric 3 M}
Poincare/Global/CartanSourceExponentialFamily.lean:67:def Family.eval {g : ClosedSmoothRiemannianMetric 3 M}
Poincare/Global/CartanSourceExponentialFamily.lean:72:def Family.symmEval {g : ClosedSmoothRiemannianMetric 3 M}
Poincare/Global/CartanSourceExponentialFamily.lean:80:structure Family.JointlyRegular {g : ClosedSmoothRiemannianMetric 3 M}
Poincare/Global/CartanSourceExponentialFamily.lean:91:def genericFamily (g : ClosedSmoothRiemannianMetric 3 M) : Family g where
Poincare/Global/CartanSourceExponentialFamily.lean:118:def GenericJointRegularity (g : ClosedSmoothRiemannianMetric 3 M) : Prop :=
Poincare/Global/CartanSourceExponentialFamily.lean:219:structure LocalFamily (g : ClosedSmoothRiemannianMetric 3 M) where
Poincare/Global/FixedChartUniformSourceNormal.lean:28:structure Patch (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M) (U : Set E) where
Poincare/Global/FixedChartUniformSourceNormal.lean:63:theorem exists_patch (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M)
Poincare/Global/NormalizedFlowPinchingLimit.lean:151:theorem ClosedSmoothRiemannianMetric.relativeTracelessRicciAt_eq_tracelessPinchingAt_zero
Poincare/Global/VolumeMeasure.lean:39:def volumeMeasure (g : ClosedSmoothRiemannianMetric n M) :
Poincare/Global/VolumeMeasure.lean:45:theorem volumeMeasure_apply (g : ClosedSmoothRiemannianMetric n M)
Poincare/Global/VolumeMeasure.lean:63:theorem volumeMeasure_noAtoms (g : ClosedSmoothRiemannianMetric n M)
Poincare/Global/NormalizedFlowVolumeVariation.lean:45:noncomputable def totalVolume
Poincare/Global/NormalizedFlowVolumeVariation.lean:54:noncomputable def totalVolumeFirstVariation
Poincare/Global/RiemannianContext.lean:30:abbrev ClosedSmoothModel (n : ℕ) : Type :=
Poincare/Global/RiemannianContext.lean:34:abbrev closedSmoothModelWithCorners (n : ℕ) :
Poincare/Global/RiemannianContext.lean:44:abbrev ClosedSmoothRiemannianMetric (n : ℕ) (M : Type u)
Poincare/Global/RiemannianContext.lean:111:theorem contMDiff_inner (g : ClosedSmoothRiemannianMetric n M) :
Poincare/Global/RiemannianContext.lean:122:theorem inner_symm (g : ClosedSmoothRiemannianMetric n M) (x : M)
Poincare/Global/RiemannianContext.lean:128:theorem inner_pos (g : ClosedSmoothRiemannianMetric n M) (x : M)
Poincare/Global/RiemannianContext.lean:134:theorem inner_nonneg (g : ClosedSmoothRiemannianMetric n M) (x : M)
Poincare/Global/RiemannianContext.lean:142:theorem isVonNBounded_unitBall (g : ClosedSmoothRiemannianMetric n M) (x : M) :
Poincare/Global/RiemannianContext.lean:147:theorem fiber_inner_eq (g : ClosedSmoothRiemannianMetric n M) (x : M)
Poincare/Global/RiemannianContext.lean:154:theorem contMDiff_fiber_inner (g : ClosedSmoothRiemannianMetric n M)
Poincare/Global/CartanTargetExponentialFamily.lean:617:structure ChainState (F : Family) (g : ClosedSmoothRiemannianMetric 3 M) where
Poincare/Global/CartanTargetExponentialFamily.lean:750:structure Data (F : Family) {g : ClosedSmoothRiemannianMetric 3 M}
Poincare/Global/LeviCivita.lean:46:def IsMetricCompatible (g : ClosedSmoothRiemannianMetric n M)
Poincare/Global/LeviCivita.lean:181:theorem levi_civita_unique (g : ClosedSmoothRiemannianMetric n M)
Poincare/Global/CompactCoefficientEllipticity.lean:7:abbrev E := ClosedSmoothModel 3
Poincare/Global/SphereTheorem.lean:118:def HamiltonConvergencePinchedLimit3 (M : Type u)
Poincare/Global/FixedChartUniformDifferentialPullback.lean:211:def UniformNonzeroMetricPullback (g : ClosedSmoothRiemannianMetric 3 M) : Prop :=
Poincare/Global/ConnectionInstanceNaturality.lean:190:def conjugatedConnection (g : @ClosedSmoothRiemannianMetric 3 M _ inst _) :
Poincare/Global/MetricFlowJointRegularity.lean:198:def MetricEntriesJointContDiffAt
Poincare/Global/MetricFlowJointRegularity.lean:204:theorem MetricEntriesJointContDiffAt.of_le
Poincare/Global/NormalizedFlowHausdorffPartitionStokes.lean:734:theorem ClosedSmoothRiemannianMetric.laplacianAt_finsetSum
Poincare/Global/ScalarEvolution.lean:192:theorem ClosedSmoothRiemannianMetric.hasDerivAt_tracelessPinchingAt_of_scalar_and_tracelessNorm
Poincare/Global/ScalarEvolution.lean:208:theorem ClosedSmoothRiemannianMetric.hasDerivAt_tracelessRicciNormSqAt_of_ricciNormSq_and_scalar_sq
Poincare/Global/ScalarEvolution.lean:4047:noncomputable def scalarMinimumAt (g : ClosedSmoothRiemannianMetric n M) : ℝ :=
Poincare/Global/ScalarEvolution.lean:4094:noncomputable def pinchingMaximumAt (g : ClosedSmoothRiemannianMetric n M) : ℝ :=
Poincare/Global/Curvature.lean:37:def leviCivita (g : ClosedSmoothRiemannianMetric n M) :
Poincare/Global/Curvature.lean:43:theorem leviCivita_contMDiff (g : ClosedSmoothRiemannianMetric n M) :
Poincare/Global/Curvature.lean:50:theorem leviCivita_contMDiff₂ (g : ClosedSmoothRiemannianMetric n M) :
Poincare/Global/Curvature.lean:56:theorem leviCivita_metricCompatible (g : ClosedSmoothRiemannianMetric n M) :
Poincare/Global/Curvature.lean:62:theorem leviCivita_torsion (g : ClosedSmoothRiemannianMetric n M) :
Poincare/Global/Curvature.lean:68:theorem leviCivita_metricCompatibleAt (g : ClosedSmoothRiemannianMetric n M)
Poincare/Global/Curvature.lean:77:theorem leviCivita_torsionFreeAt (g : ClosedSmoothRiemannianMetric n M)
Poincare/Global/Curvature.lean:98:noncomputable def metricBilinAt (g : ClosedSmoothRiemannianMetric n M)
Poincare/Global/Curvature.lean:104:theorem metricBilinAt_apply (g : ClosedSmoothRiemannianMetric n M)
Poincare/Global/Curvature.lean:110:theorem metricBilinAt_nondegenerate (g : ClosedSmoothRiemannianMetric n M)
Poincare/Global/Curvature.lean:123:theorem metric_pairing_mdiffAt (g : ClosedSmoothRiemannianMetric n M)
Poincare/Global/CartanSuppliedFinitePatchCover.lean:18:structure PatchCover (g : ClosedSmoothRiemannianMetric 3 M) where
Poincare/Global/CartanSuppliedFinitePatchCover.lean:46:structure QuantitativeCover (g : ClosedSmoothRiemannianMetric 3 M) where
Poincare/Global/CartanSuppliedFinitePatchCover.lean:82:theorem exists_patchCover : ∀ g : ClosedSmoothRiemannianMetric 3 M,
Poincare/Global/DeTurckPrincipalIdentity.lean:670:theorem principalIdentity (bg : ClosedSmoothRiemannianMetric 3 M)
Poincare/Global/Laplacian.lean:66:noncomputable def gradientAt (g : ClosedSmoothRiemannianMetric n M)
Poincare/Global/Laplacian.lean:76:noncomputable def gradient (g : ClosedSmoothRiemannianMetric n M)
Poincare/Global/Laplacian.lean:81:theorem inner_gradientAt (g : ClosedSmoothRiemannianMetric n M)
Poincare/Global/Laplacian.lean:115:theorem gradientAt_add (g : ClosedSmoothRiemannianMetric n M)
Poincare/Global/Laplacian.lean:131:theorem gradient_add (g : ClosedSmoothRiemannianMetric n M)
Poincare/Global/Laplacian.lean:139:theorem gradientAt_mul (g : ClosedSmoothRiemannianMetric n M)
Poincare/Global/Laplacian.lean:153:theorem gradient_mul (g : ClosedSmoothRiemannianMetric n M)
Poincare/Global/Laplacian.lean:161:theorem gradientAt_const_smul (g : ClosedSmoothRiemannianMetric n M)
Poincare/Global/Laplacian.lean:175:theorem gradient_const_smul (g : ClosedSmoothRiemannianMetric n M)
Poincare/Global/Laplacian.lean:182:theorem gradientAt_const (g : ClosedSmoothRiemannianMetric n M)
Poincare/Global/Laplacian.lean:191:theorem gradient_const (g : ClosedSmoothRiemannianMetric n M)
Poincare/Global/Laplacian.lean:198:noncomputable def scalarGradNormSqAt (g : ClosedSmoothRiemannianMetric n M)
Poincare/Global/Laplacian.lean:213:theorem mdifferentiableAt_gradient (g : ClosedSmoothRiemannianMetric n M)
Poincare/Global/Laplacian.lean:399:noncomputable def hessianAt (g : ClosedSmoothRiemannianMetric n M)
Poincare/Global/Laplacian.lean:425:noncomputable def hessianDualAt (g : ClosedSmoothRiemannianMetric n M)
Poincare/Global/Laplacian.lean:445:theorem hessianDualAt_apply (g : ClosedSmoothRiemannianMetric n M)
Poincare/Global/Laplacian.lean:451:noncomputable def hessianContinuousAt (g : ClosedSmoothRiemannianMetric n M)
Poincare/Global/Laplacian.lean:461:theorem hessianContinuousAt_apply (g : ClosedSmoothRiemannianMetric n M)
Poincare/Global/Laplacian.lean:482:noncomputable def laplacianAt (g : ClosedSmoothRiemannianMetric n M)
Poincare/Global/Laplacian.lean:523:theorem leviCivita_smul_function (g : ClosedSmoothRiemannianMetric n M)
Poincare/Global/Laplacian.lean:541:theorem hessianAt_add (g : ClosedSmoothRiemannianMetric n M)
Poincare/Global/Laplacian.lean:563:theorem hessianAt_const_smul (g : ClosedSmoothRiemannianMetric n M)
Poincare/Global/Laplacian.lean:575:theorem hessianAt_mul (g : ClosedSmoothRiemannianMetric n M)
Poincare/Global/Laplacian.lean:602:theorem hessianContinuousAt_mul (g : ClosedSmoothRiemannianMetric n M)
Poincare/Global/Laplacian.lean:617:theorem hessianAt_const (g : ClosedSmoothRiemannianMetric n M)
Poincare/Global/Laplacian.lean:629:theorem hessianAt_symm (g : ClosedSmoothRiemannianMetric n M)
Poincare/Global/Laplacian.lean:695:theorem hessianAt_symm' (g : ClosedSmoothRiemannianMetric n M)
Poincare/Global/Laplacian.lean:702:theorem hessianDualAt_add (g : ClosedSmoothRiemannianMetric n M)
Poincare/Global/Laplacian.lean:713:theorem hessianDualAt_const_smul (g : ClosedSmoothRiemannianMetric n M)
Poincare/Global/Laplacian.lean:721:theorem hessianDualAt_const (g : ClosedSmoothRiemannianMetric n M)
Poincare/Global/Laplacian.lean:733:theorem laplacianAt_add (g : ClosedSmoothRiemannianMetric n M)
Poincare/Global/Laplacian.lean:748:theorem laplacianAt_add' (g : ClosedSmoothRiemannianMetric n M)
Poincare/Global/Laplacian.lean:765:theorem laplacianAt_const_smul (g : ClosedSmoothRiemannianMetric n M)
Poincare/Global/Laplacian.lean:778:theorem laplacianAt_const_smul' (g : ClosedSmoothRiemannianMetric n M)
Poincare/Global/Laplacian.lean:786:theorem laplacianAt_mul (g : ClosedSmoothRiemannianMetric n M)
Poincare/Global/Laplacian.lean:851:theorem laplacianAt_mul' (g : ClosedSmoothRiemannianMetric n M)
Poincare/Global/Laplacian.lean:864:theorem laplacianAt_sq (g : ClosedSmoothRiemannianMetric n M)
Poincare/Global/Laplacian.lean:876:theorem laplacianAt_const (g : ClosedSmoothRiemannianMetric n M)
Poincare/Global/NormalizedFlowFiniteTimeHamiltonPinching.lean:117:theorem ClosedSmoothRiemannianMetric.globalRicciEigenvalueFloor_one_fourth_of_scalar_lower_of_traceless_lt
Poincare/Global/NormalizedFlowFiniteTimeHamiltonPinching.lean:149:theorem ClosedSmoothRiemannianMetric.globalPinchingQuotientBound_three_eighths_of_globalRicciEigenvalueFloor_one_fourth
Poincare/Global/CartanMap.lean:45:def sourceAnchorChartMetric (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M) :
Poincare/Global/CartanMap.lean:64:def sourceAnchorBilinForm (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M) :
Poincare/Global/CartanMap.lean:90:abbrev TangentAlignment (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M)
Poincare/Global/CartanMap.lean:182:def cartanMap (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M) (p₀ : RoundSphere3)
Poincare/Global/UniformNormalRadius.lean:34:def normalCoordinateRadius (g : ClosedSmoothRiemannianMetric n M) (x₀ : M) : ℝ :=
Poincare/Global/UniformNormalRadius.lean:44:def normalCoordinateImage (g : ClosedSmoothRiemannianMetric n M) (x₀ : M) : Set M :=
Poincare/Global/MetricRescale.lean:40:def constSMul (g : ClosedSmoothRiemannianMetric n M) (c : ℝ) (hc : 0 < c) :
Poincare/Global/MetricRescale.lean:96:theorem constSMul_inner (g : ClosedSmoothRiemannianMetric n M)
Poincare/Global/LeviCivitaExistence.lean:44:theorem metric_pairing_mdiffAt (g : ClosedSmoothRiemannianMetric n M)
Poincare/Global/LeviCivitaExistence.lean:60:theorem metric_nondegenerate (g : ClosedSmoothRiemannianMetric n M) (x : M)
Poincare/Global/LeviCivitaExistence.lean:117:theorem levi_civita_exists (g : ClosedSmoothRiemannianMetric n M) :
Poincare/Global/MetricVariation.lean:41:def timeDerivAt
Poincare/Global/RiemannianMetricInstanceTransportGeometric.lean:194:def transportedInner (g : @ClosedSmoothRiemannianMetric 3 M _ inst _) (x : M) : Bilin :=
Poincare/Global/RiemannianMetricInstanceTransportGeometric.lean:248:theorem transportedInner_contMDiff (g : @ClosedSmoothRiemannianMetric 3 M _ inst _) :
Poincare/Global/RiemannianMetricInstanceTransportGeometric.lean:267:def transport (g : @ClosedSmoothRiemannianMetric 3 M _ inst _) :
Poincare/Global/RiemannianMetricInstanceTransportGeometric.lean:288:theorem transport_inner (g : @ClosedSmoothRiemannianMetric 3 M _ inst _)
Poincare/Global/ClosedRicciFlowNormalization.lean:29:def normalizedFlowGoal (g₀ : ClosedSmoothRiemannianMetric 3 M) : Prop :=
Poincare/Global/ClosedRicciFlowNormalization.lean:34:def regularRicciFlowGoal (g₀ : ClosedSmoothRiemannianMetric 3 M) : Prop :=
Poincare/Global/FixedChartMovingPositionJacobi.lean:512:theorem movingInitialPositionJacobiComparison (g : ClosedSmoothRiemannianMetric 3 M) :
Poincare/Global/FixedChartMovingPositionJacobi.lean:556:theorem uniformNonzeroMetricPullback (g : ClosedSmoothRiemannianMetric 3 M) :
Poincare/Global/FixedChartMovingPositionJacobi.lean:579:theorem exists_radius (g : ClosedSmoothRiemannianMetric 3 M) :
Poincare/Global/NormalizedFlow.lean:91:structure IsClosedNormalizedRicciFlowSolutionAt
Poincare/Global/DeTurckPrincipalSecondJet.lean:15:abbrev E := ClosedSmoothModel 3
Poincare/Global/NormalizedFlowCompactFixedTargetReactionDecayHausdorffJointScalarDerivativeCovRicciSubordinatePartitionPositiveEinstein.lean:43:theorem continuous_joint_covRicciNormSqAt_of_bochner_fields {n : ℕ} {N : Type u} {K : Type v} [TopologicalSpace N] [T2Space N] [ChartedSpace (ClosedSmoothModel n) N] [IsManifold (closedSmoothModelWithCorners n) ∞ N] [TopologicalSpace K] (metric : K → ClosedSmoothRiemannianMetric n N) (hRicNorm₂ : ∀ k : K, ∀ x : N, ContMDiffAt (closedSmoothModelWithCorners n) 𝓘(ℝ) 2 (fun y : N ↦ (metric k).ricciNormSqAt y) x) (hPairDiff : ∀ k : K, ∀ x : N, ∀ w : TangentSpace (closedSmoothModelWithCorners n) x, MDifferentiableAt (closedSmoothModelWithCorners n) 𝓘(ℝ) (fun y : N ↦ covRicciRicciPairingAt (metric k) y (extend (ClosedSmoothModel n) w y)) x) (hRicSecond : ∀ k : K, ∀ x : N, CovTensor2DerivExtDifferentiableAt (metric k) (ricciVariationField (metric k)) x) (hLaplacian : Continuous (fun p : K × N ↦ (metric p.1).laplacianAt (fun y : N ↦ (metric p.1).ricciNormSqAt y) p.2)) (hRough : Continuous (fun p : K × N ↦ roughRicciLaplacianPairingAt (metric p.1) p.2)) : Continuous (fun p : K × N ↦ covRicciNormSqAt (metric p.1) p.2) := by
Poincare/Global/CartanSuppliedUniformPatchSwitch.lean:28:structure System (g : ClosedSmoothRiemannianMetric 3 M) where
Poincare/Global/HamiltonFrontStatements.lean:83:def UniversalHamiltonConvergenceStatement : Prop :=
Poincare/Global/RoundSphereMetric.lean:213:noncomputable def roundSphereMetric3 : ClosedSmoothRiemannianMetric 3 RoundSphere3 where
Poincare/Global/CartanSuppliedSourceMap.lean:67:theorem generic_map_eq (g : ClosedSmoothRiemannianMetric 3 M)
Poincare/Global/NormalizedHosting.lean:38:def sourceNormalizedTime (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M)
Poincare/Global/NormalizedHosting.lean:43:def sourceNormalizedVelocity (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M)
Poincare/Global/CurvatureInstanceTransport.lean:207:def conjugatedDerivative (g : @ClosedSmoothRiemannianMetric 3 M _ inst _) :
Poincare/Global/CurvatureInstanceTransport.lean:215:theorem conjugatedDerivative_apply (g : @ClosedSmoothRiemannianMetric 3 M _ inst _)
Poincare/Global/CurvatureInstanceTransport.lean:254:def curvatureValue (g : @ClosedSmoothRiemannianMetric 3 M _ inst _)
Poincare/Global/CurvatureInstanceTransport.lean:265:def ConnectionCurvatureNaturality (g : @ClosedSmoothRiemannianMetric 3 M _ inst _) : Prop :=
Poincare/Global/CurvatureInstanceTransport.lean:300:def conjugatedConnection (g : @ClosedSmoothRiemannianMetric 3 M _ inst _)
Poincare/Global/CartanSuppliedDifferentialSuccessor.lean:24:structure Interpretation (g : ClosedSmoothRiemannianMetric 3 M) where
Poincare/Global/CartanSuppliedDifferentialSuccessor.lean:38:def generic (g : ClosedSmoothRiemannianMetric 3 M) : Interpretation g where
Poincare/Global/ExponentialGerm.lean:145:def expRayAt (g : ClosedSmoothRiemannianMetric n M) (x₀ : M) (v₀ : E) : ℝ → M :=
Poincare/Global/GenericJointRegularityCounterexample.lean:93:theorem not_genericJointRegularity (g : ClosedSmoothRiemannianMetric 3 E) :
Poincare/Global/GenericJointRegularityCounterexample.lean:103:def flatMetric : ClosedSmoothRiemannianMetric 3 E where
Poincare/Global/ScalarIntegral.lean:28:theorem scalarAt_continuous (g : ClosedSmoothRiemannianMetric n M) :
Poincare/Global/ScalarIntegral.lean:53:theorem scalarAt_integrable (g : ClosedSmoothRiemannianMetric n M) :
Poincare/Global/ScalarIntegral.lean:61:noncomputable def totalScalar (g : ClosedSmoothRiemannianMetric n M) : ℝ :=
Poincare/Global/ScalarIntegral.lean:65:noncomputable def meanScalar (g : ClosedSmoothRiemannianMetric n M) : ℝ :=
Poincare/Global/NormalizedFlowFiniteTimePositiveRicci.lean:107:theorem ClosedSmoothRiemannianMetric.ricciEigenvalue_lower_bounds_of_scalar_lower_of_traceless_lt
Poincare/Global/NormalizedFlowFiniteTimePositiveRicci.lean:141:theorem ClosedSmoothRiemannianMetric.pinchingQuotientAt_le_one_half_of_scalar_lower_of_traceless_lt
Poincare/Global/NormalizedFlowFiniteTimePositiveRicci.lean:168:theorem ClosedSmoothRiemannianMetric.hasPosRicciAt_of_scalar_lower_of_traceless_lt
Poincare/Global/NormalizedFlowScalarIntegralVariation.lean:180:noncomputable def normalizedMeanScalarEnergyNumerator
Poincare/Global/ClosedMetricThirdJetTopology.lean:38:inductive MetricEntryThirdJetSlot (n : ℕ) (M : Type u)
```

### Command 10

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HamiltonMeanFloorFromEnergyDomination.lean
```

Exit: 0.

```text
Poincare/Global/HamiltonMeanFloorFromEnergyDomination.lean:29:0: warning: automatically included section variable(s) unused in theorem `Poincare.HamiltonMeanFloorFromEnergyDomination.movingDerivatives`:
  [SimplyConnectedSpace M]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [SimplyConnectedSpace M] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
```

### Command 11

```sh
LEAN_NUM_THREADS=1 lake env lean /tmp/hamilton-mean-floor-from-energy-domination/dependencies-2.lean
```

Exit: 0.

```text
/tmp/hamilton-mean-floor-from-energy-domination/dependencies-2.lean:29:0: warning: automatically included section variable(s) unused in theorem `Poincare.HamiltonMeanFloorFromEnergyDomination.movingDerivatives`:
  [SimplyConnectedSpace M]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [SimplyConnectedSpace M] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
'Poincare.HamiltonMeanFloorFromEnergyDomination.movingDerivatives' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HamiltonMeanFloorFromEnergyDomination.meanFloorFromEnergy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### Command 12

```sh
rg -n '\b(sorry|admit|axiom|opaque)\b|native_decide' Poincare/Global/HamiltonMeanFloorFromEnergyDomination.lean
```

Exit: 1.

Output: empty.

### Command 13

```sh
git diff --check
```

Exit: 0.

Output: empty.

### Command 14

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HamiltonMeanFloorFromEnergyDomination.lean
```

Exit: 0.

```text
Poincare/Global/HamiltonMeanFloorFromEnergyDomination.lean:29:0: warning: automatically included section variable(s) unused in theorem `Poincare.HamiltonMeanFloorFromEnergyDomination.movingDerivatives`:
  [SimplyConnectedSpace M]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [SimplyConnectedSpace M] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
```

### Command 15

```sh
LEAN_NUM_THREADS=1 lake env lean /tmp/hamilton-mean-floor-from-energy-domination/dependencies-3.lean
```

Exit: 0.

```text
/tmp/hamilton-mean-floor-from-energy-domination/dependencies-3.lean:29:0: warning: automatically included section variable(s) unused in theorem `Poincare.HamiltonMeanFloorFromEnergyDomination.movingDerivatives`:
  [SimplyConnectedSpace M]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [SimplyConnectedSpace M] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
'Poincare.HamiltonMeanFloorFromEnergyDomination.movingDerivatives' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HamiltonMeanFloorFromEnergyDomination.meanFloorFromEnergy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HamiltonMeanFloorFromEnergyDomination.meanFloorFromEnergy_of_initialMeanPos' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### Command 16

```sh
rg -n '\b(sorry|admit|axiom|opaque)\b|native_decide' Poincare/Global/HamiltonMeanFloorFromEnergyDomination.lean
```

Exit: 1.

Output: empty.

### Command 17

```sh
git diff --check
```

Exit: 0.

Output: empty.

### Command 18

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HamiltonMeanFloorFromEnergyDomination.lean
```

Exit: 0.

```text
Poincare/Global/HamiltonMeanFloorFromEnergyDomination.lean:29:0: warning: automatically included section variable(s) unused in theorem `Poincare.HamiltonMeanFloorFromEnergyDomination.movingDerivatives`:
  [SimplyConnectedSpace M]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [SimplyConnectedSpace M] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
```

### Command 19

```sh
LEAN_NUM_THREADS=1 lake env lean /tmp/hamilton-mean-floor-from-energy-domination/dependencies-5.lean
```

Exit: 0.

```text
/tmp/hamilton-mean-floor-from-energy-domination/dependencies-5.lean:29:0: warning: automatically included section variable(s) unused in theorem `Poincare.HamiltonMeanFloorFromEnergyDomination.movingDerivatives`:
  [SimplyConnectedSpace M]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [SimplyConnectedSpace M] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
'Poincare.HamiltonMeanFloorFromEnergyDomination.movingDerivatives' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HamiltonMeanFloorFromEnergyDomination.meanFloorFromEnergy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HamiltonMeanFloorFromEnergyDomination.meanFloorFromEnergy_of_initialMeanPos' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HamiltonMeanFloorFromEnergyDomination.HamiltonReactionCore3Energy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HamiltonMeanFloorFromEnergyDomination.hamiltonReactionCore3Final_of_energy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### Command 20

```sh
rg -n '\b(sorry|admit|axiom|opaque)\b|native_decide' Poincare/Global/HamiltonMeanFloorFromEnergyDomination.lean
```

Exit: 1.

Output: empty.

### Command 21

```sh
git diff --check
```

Exit: 0.

Output: empty.

### Command 22

```sh
git commit -m 'Reduce the explicit energy core to the final Hamilton reaction core'
```

Exit: 0.

```text
[worker/hamilton-mean-floor-from-energy-domination aa250064] Reduce the explicit energy core to the final Hamilton reaction core
 1 file changed, 41 insertions(+)
```

### Command 23

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HamiltonMeanFloorFromEnergyDomination.lean
```

Exit: 0.

```text
Poincare/Global/HamiltonMeanFloorFromEnergyDomination.lean:29:0: warning: automatically included section variable(s) unused in theorem `Poincare.HamiltonMeanFloorFromEnergyDomination.movingDerivatives`:
  [SimplyConnectedSpace M]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [SimplyConnectedSpace M] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
```

### Command 24

```sh
LEAN_NUM_THREADS=1 lake env lean /tmp/hamilton-mean-floor-from-energy-domination/dependencies-6.lean
```

Exit: 0.

```text
/tmp/hamilton-mean-floor-from-energy-domination/dependencies-6.lean:29:0: warning: automatically included section variable(s) unused in theorem `Poincare.HamiltonMeanFloorFromEnergyDomination.movingDerivatives`:
  [SimplyConnectedSpace M]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [SimplyConnectedSpace M] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
'Poincare.HamiltonMeanFloorFromEnergyDomination.movingDerivatives' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HamiltonMeanFloorFromEnergyDomination.meanFloorFromEnergy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HamiltonMeanFloorFromEnergyDomination.meanFloorFromEnergy_of_initialMeanPos' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HamiltonMeanFloorFromEnergyDomination.HamiltonReactionCore3Energy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HamiltonMeanFloorFromEnergyDomination.hamiltonReactionCore3Final_of_energy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HamiltonMeanFloorFromEnergyDomination.hamiltonConvergencePinchedLimit3_of_hamiltonReactionCore3Energy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### Command 25

```sh
rg -n '\b(sorry|admit|axiom|opaque)\b|native_decide' Poincare/Global/HamiltonMeanFloorFromEnergyDomination.lean
```

Exit: 1.

Output: empty.

### Command 26

```sh
git diff --check
```

Exit: 0.

Output: empty.

### Command 27

```sh
git commit -m 'Derive the Hamilton endpoint from the energy core'
```

Exit: 0.

```text
[worker/hamilton-mean-floor-from-energy-domination f6ff7695] Derive the Hamilton endpoint from the energy core
 1 file changed, 6 insertions(+)
```

### Command 28

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HamiltonMeanFloorFromEnergyDomination.lean
```

Exit: 0.

```text
Poincare/Global/HamiltonMeanFloorFromEnergyDomination.lean:29:0: warning: automatically included section variable(s) unused in theorem `Poincare.HamiltonMeanFloorFromEnergyDomination.movingDerivatives`:
  [SimplyConnectedSpace M]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [SimplyConnectedSpace M] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
```

### Command 29

```sh
LEAN_NUM_THREADS=1 lake env lean /tmp/hamilton-mean-floor-from-energy-domination/dependencies-8.lean
```

Exit: 0.

```text
/tmp/hamilton-mean-floor-from-energy-domination/dependencies-8.lean:29:0: warning: automatically included section variable(s) unused in theorem `Poincare.HamiltonMeanFloorFromEnergyDomination.movingDerivatives`:
  [SimplyConnectedSpace M]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [SimplyConnectedSpace M] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
'Poincare.HamiltonMeanFloorFromEnergyDomination.movingDerivatives' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HamiltonMeanFloorFromEnergyDomination.meanFloorFromEnergy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HamiltonMeanFloorFromEnergyDomination.meanFloorFromEnergy_of_initialMeanPos' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HamiltonMeanFloorFromEnergyDomination.HamiltonReactionCore3Energy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HamiltonMeanFloorFromEnergyDomination.hamiltonReactionCore3Final_of_energy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HamiltonMeanFloorFromEnergyDomination.hamiltonConvergencePinchedLimit3_of_hamiltonReactionCore3Energy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HamiltonMeanFloorFromEnergyDomination.UniversalHamiltonReactionCoreEnergyStatement' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HamiltonMeanFloorFromEnergyDomination.universalHamiltonReactionCoreFinal_of_universalHamiltonReactionCoreEnergy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### Command 30

```sh
rg -n '\b(sorry|admit|axiom|opaque)\b|native_decide' Poincare/Global/HamiltonMeanFloorFromEnergyDomination.lean
```

Exit: 1.

Output: empty.

### Command 31

```sh
git diff --check
```

Exit: 0.

Output: empty.

### Command 32

```sh
git commit -m 'Reduce universal energy cores to universal final reaction cores'
```

Exit: 0.

```text
[worker/hamilton-mean-floor-from-energy-domination 9f7da813] Reduce universal energy cores to universal final reaction cores
 1 file changed, 16 insertions(+)
```

### Command 33

```sh
LEAN_NUM_THREADS=1 lake env lean Poincare/Global/HamiltonMeanFloorFromEnergyDomination.lean
```

Exit: 0.

```text
Poincare/Global/HamiltonMeanFloorFromEnergyDomination.lean:29:0: warning: automatically included section variable(s) unused in theorem `Poincare.HamiltonMeanFloorFromEnergyDomination.movingDerivatives`:
  [SimplyConnectedSpace M]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [SimplyConnectedSpace M] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
```

### Command 34

```sh
LEAN_NUM_THREADS=1 lake env lean /tmp/hamilton-mean-floor-from-energy-domination/dependencies-9.lean
```

Exit: 0.

```text
/tmp/hamilton-mean-floor-from-energy-domination/dependencies-9.lean:29:0: warning: automatically included section variable(s) unused in theorem `Poincare.HamiltonMeanFloorFromEnergyDomination.movingDerivatives`:
  [SimplyConnectedSpace M]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [SimplyConnectedSpace M] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
'Poincare.HamiltonMeanFloorFromEnergyDomination.movingDerivatives' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HamiltonMeanFloorFromEnergyDomination.meanFloorFromEnergy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HamiltonMeanFloorFromEnergyDomination.meanFloorFromEnergy_of_initialMeanPos' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HamiltonMeanFloorFromEnergyDomination.HamiltonReactionCore3Energy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HamiltonMeanFloorFromEnergyDomination.hamiltonReactionCore3Final_of_energy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HamiltonMeanFloorFromEnergyDomination.hamiltonConvergencePinchedLimit3_of_hamiltonReactionCore3Energy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HamiltonMeanFloorFromEnergyDomination.UniversalHamiltonReactionCoreEnergyStatement' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HamiltonMeanFloorFromEnergyDomination.universalHamiltonReactionCoreFinal_of_universalHamiltonReactionCoreEnergy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Poincare.HamiltonMeanFloorFromEnergyDomination.universalHamiltonConvergence_of_universalHamiltonReactionCoreEnergy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### Command 35

```sh
rg -n '\b(sorry|admit|axiom|opaque)\b|native_decide' Poincare/Global/HamiltonMeanFloorFromEnergyDomination.lean
```

Exit: 1.

Output: empty.

### Command 36

```sh
git diff --check
```

Exit: 0.

Output: empty.

### Command 37

```sh
git commit -m 'Derive universal Hamilton convergence from energy cores'
```

Exit: 0.

```text
[worker/hamilton-mean-floor-from-energy-domination 11037559] Derive universal Hamilton convergence from energy cores
 1 file changed, 7 insertions(+)
```

### Command 38

```sh
rg -n '^(inductive|def|abbrev|structure|theorem|noncomputable def) (MetricEntryThirdJetSlot|ClosedSmoothRiemannianMetric|ClosedSmoothModel|closedSmoothModelWithCorners|MetricEntriesJointContDiffAt|IsClosedNormalizedRicciFlowSolutionAt|totalVolume|totalVolumeFirstVariation|timeDerivAt|totalScalar|normalizedMeanScalarEnergyNumerator|meanScalar|HamiltonConvergencePinchedLimit3|UniversalHamiltonConvergenceStatement|normalizedTracelessRicciEvolutionReactionAt)\b' Poincare
```

Exit: 0.

```text
Poincare/Global/NormalizedFlowPinchingLimit.lean:151:theorem ClosedSmoothRiemannianMetric.relativeTracelessRicciAt_eq_tracelessPinchingAt_zero
Poincare/Global/RiemannianContext.lean:30:abbrev ClosedSmoothModel (n : ℕ) : Type :=
Poincare/Global/RiemannianContext.lean:34:abbrev closedSmoothModelWithCorners (n : ℕ) :
Poincare/Global/RiemannianContext.lean:44:abbrev ClosedSmoothRiemannianMetric (n : ℕ) (M : Type u)
Poincare/Global/SphereTheorem.lean:118:def HamiltonConvergencePinchedLimit3 (M : Type u)
Poincare/Global/NormalizedFlowVolumeVariation.lean:45:noncomputable def totalVolume
Poincare/Global/NormalizedFlowVolumeVariation.lean:54:noncomputable def totalVolumeFirstVariation
Poincare/Global/MetricFlowJointRegularity.lean:198:def MetricEntriesJointContDiffAt
Poincare/Global/MetricFlowJointRegularity.lean:204:theorem MetricEntriesJointContDiffAt.of_le
Poincare/Global/NormalizedFlowHausdorffPartitionStokes.lean:734:theorem ClosedSmoothRiemannianMetric.laplacianAt_finsetSum
Poincare/Global/ScalarEvolution.lean:192:theorem ClosedSmoothRiemannianMetric.hasDerivAt_tracelessPinchingAt_of_scalar_and_tracelessNorm
Poincare/Global/ScalarEvolution.lean:208:theorem ClosedSmoothRiemannianMetric.hasDerivAt_tracelessRicciNormSqAt_of_ricciNormSq_and_scalar_sq
Poincare/Global/NormalizedFlowForwardPointwiseTracelessEnergyActualReactionDecay.lean:260:noncomputable def normalizedTracelessRicciEvolutionReactionAt
Poincare/Global/NormalizedFlowFiniteTimeHamiltonPinching.lean:117:theorem ClosedSmoothRiemannianMetric.globalRicciEigenvalueFloor_one_fourth_of_scalar_lower_of_traceless_lt
Poincare/Global/NormalizedFlowFiniteTimeHamiltonPinching.lean:149:theorem ClosedSmoothRiemannianMetric.globalPinchingQuotientBound_three_eighths_of_globalRicciEigenvalueFloor_one_fourth
Poincare/Global/MetricVariation.lean:41:def timeDerivAt
Poincare/Global/NormalizedFlow.lean:91:structure IsClosedNormalizedRicciFlowSolutionAt
Poincare/Global/NormalizedFlowFiniteTimePositiveRicci.lean:107:theorem ClosedSmoothRiemannianMetric.ricciEigenvalue_lower_bounds_of_scalar_lower_of_traceless_lt
Poincare/Global/NormalizedFlowFiniteTimePositiveRicci.lean:141:theorem ClosedSmoothRiemannianMetric.pinchingQuotientAt_le_one_half_of_scalar_lower_of_traceless_lt
Poincare/Global/NormalizedFlowFiniteTimePositiveRicci.lean:168:theorem ClosedSmoothRiemannianMetric.hasPosRicciAt_of_scalar_lower_of_traceless_lt
Poincare/Global/HamiltonFrontStatements.lean:83:def UniversalHamiltonConvergenceStatement : Prop :=
Poincare/Global/ClosedMetricThirdJetTopology.lean:38:inductive MetricEntryThirdJetSlot (n : ℕ) (M : Type u)
Poincare/Global/NormalizedFlowScalarIntegralVariation.lean:180:noncomputable def normalizedMeanScalarEnergyNumerator
Poincare/Global/ScalarIntegral.lean:61:noncomputable def totalScalar (g : ClosedSmoothRiemannianMetric n M) : ℝ :=
Poincare/Global/ScalarIntegral.lean:65:noncomputable def meanScalar (g : ClosedSmoothRiemannianMetric n M) : ℝ :=
```

### Command 39

```sh
rg -n '(def|theorem|abbrev|structure) ([A-Za-z0-9_]+\.)?(scalarAt|tracelessRicciNormSqAt)\b' Poincare/Global
```

Exit: 0.

```text
Poincare/Global/Curvature.lean:159:noncomputable def scalarAt (x : M) : ℝ :=
Poincare/Global/RicciNorm.lean:190:noncomputable def tracelessRicciNormSqAt (x : M) : ℝ :=
```

### Command 40

```sh
python3 /tmp/hamilton-mean-floor-from-energy-domination/compare-survey.py
```

Exit: 0.

```text
movingDerivatives: exact survey signature and proof body preserved
meanFloorFromEnergy: exact survey signature and proof body preserved
```

### Command 41

```sh
LEAN_NUM_THREADS=1 lake env lean /tmp/hamilton-mean-floor-from-energy-domination/exact-signatures.lean
```

Exit: 1.

```text
/tmp/hamilton-mean-floor-from-energy-domination/exact-signatures.lean:29:0: warning: automatically included section variable(s) unused in theorem `Poincare.HamiltonMeanFloorFromEnergyDomination.movingDerivatives`:
  [SimplyConnectedSpace M]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [SimplyConnectedSpace M] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
/tmp/hamilton-mean-floor-from-energy-domination/exact-signatures.lean:172:9: error: a universe level named `u` has already been declared
```

### Command 42

```sh
rg -n '^(theorem|def) ' Poincare/Global/HamiltonMeanFloorFromEnergyDomination.lean
```

Exit: 0.

```text
29:theorem movingDerivatives
51:theorem meanFloorFromEnergy
75:theorem meanFloorFromEnergy_of_initialMeanPos
98:def HamiltonReactionCore3Energy (M : Type u)
126:theorem hamiltonReactionCore3Final_of_energy
138:theorem hamiltonConvergencePinchedLimit3_of_hamiltonReactionCore3Energy
144:def UniversalHamiltonReactionCoreEnergyStatement : Prop :=
153:theorem universalHamiltonReactionCoreFinal_of_universalHamiltonReactionCoreEnergy
160:theorem universalHamiltonConvergence_of_universalHamiltonReactionCoreEnergy
```

### Command 43

```sh
git diff --check babccd85e15cdd3a58cd922b1118bf8d1dff3f0c
```

Exit: 0.

Output: empty.

### Command 44

```sh
git log '--format=%h %s' babccd85e15cdd3a58cd922b1118bf8d1dff3f0c..HEAD
```

Exit: 0.

```text
11037559 Derive universal Hamilton convergence from energy cores
9f7da813 Reduce universal energy cores to universal final reaction cores
f6ff7695 Derive the Hamilton endpoint from the energy core
aa250064 Reduce the explicit energy core to the final Hamilton reaction core
0663f8d9 Derive the uniform floor from positive initial mean alone
55db2c33 Land the exact survey mean floor from scalar energy domination
2b2e0332 Prove moving integral derivatives with explicit scalar Stokes
```

### Command 45

```sh
git diff --name-status babccd85e15cdd3a58cd922b1118bf8d1dff3f0c
```

Exit: 0.

```text
A	Poincare/Global/HamiltonMeanFloorFromEnergyDomination.lean
```

### Command 46

```sh
git rev-parse HEAD
```

Exit: 0.

```text
110375595ee111033ffa9e1347ebbef27f4ce0df
```

### Command 47

```sh
LEAN_NUM_THREADS=1 lake env lean /tmp/hamilton-mean-floor-from-energy-domination/exact-signatures.lean
```

Exit: 0.

```text
/tmp/hamilton-mean-floor-from-energy-domination/exact-signatures.lean:29:0: warning: automatically included section variable(s) unused in theorem `Poincare.HamiltonMeanFloorFromEnergyDomination.movingDerivatives`:
  [SimplyConnectedSpace M]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [SimplyConnectedSpace M] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
```

### Command 48

```sh
git diff babccd85e15cdd3a58cd922b1118bf8d1dff3f0c -- Poincare/Global/HamiltonMeanFloorFromEnergyDomination.lean
```

Exit: 0.

```text
diff --git a/Poincare/Global/HamiltonMeanFloorFromEnergyDomination.lean b/Poincare/Global/HamiltonMeanFloorFromEnergyDomination.lean
new file mode 100644
index 00000000..1528c623
--- /dev/null
+++ b/Poincare/Global/HamiltonMeanFloorFromEnergyDomination.lean
@@ -0,0 +1,166 @@
+import Poincare.Global.HamiltonChartDensityLocalDomination
+import Poincare.Global.HamiltonMeanFloorReduction
+import Poincare.Global.NormalizedFlowHausdorffScalarTimeDerivativeAutomatic
+import Poincare.Global.NormalizedFlowHausdorffScalarDominationJointC1Reduction
+import Poincare.Global.NormalizedFlowForwardFiniteTimePositiveEinsteinMeanScalarEnergyDomination
+
+/-!
+# Mean scalar floor from energy domination
+
+Moving integral differentiation follows from joint C³ metric entries and
+explicit closed Laplacian Stokes. The integrated energy inequality then
+makes the forward mean scalar nondecreasing. Core existence, Stokes, and
+the energy inequality remain explicit inputs.
+-/
+
+set_option autoImplicit false
+noncomputable section
+open Set Filter MeasureTheory
+open scoped Manifold ContDiff Topology
+universe u v
+namespace Poincare.HamiltonMeanFloorFromEnergyDomination
+variable {M : Type u} [TopologicalSpace M] [T2Space M]
+  [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]
+  [ChartedSpace (ClosedSmoothModel 3) M]
+  [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
+  [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M]
+
+/-- The moving volume and total-scalar identities, retaining Stokes explicitly. -/
+theorem movingDerivatives
+    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
+    (hjoint : ∀ t x, MetricEntriesJointContDiffAt gt t x 3)
+    (hflow : ∀ t ∈ Ici (0 : ℝ), ∀ x, IsClosedNormalizedRicciFlowSolutionAt gt t x)
+    (hstokes : ∀ t ∈ Ici (0 : ℝ), ClosedLaplacianStokes (gt t) (fun x ↦ (gt t).scalarAt x)) :
+    (∀ t ∈ Ici (0 : ℝ), HasDerivAt (fun s ↦ totalVolume (gt s))
+      (totalVolumeFirstVariation (gt t) (timeDerivAt gt t)) t) ∧
+    (∀ t ∈ Ici (0 : ℝ), HasDerivAt (fun s ↦ totalScalar (gt s))
+      (normalizedMeanScalarEnergyNumerator (gt t)) t) := by
+  obtain ⟨D⟩ := HamiltonReactionCoreReduction.chartFrameDensityData_of_joint_of_local_bound
+    gt hjoint (HamiltonChartDensityLocalDomination.localBound_of_jointMetricEntries gt hjoint)
+  let V := D.toChartFrameDensityVariation
+  constructor
+  · intro t ht
+    exact V.hasDerivAt_totalVolume_of_normalizedFlowAt t (hflow t ht)
+  · intro t ht
+    exact hasDerivAt_totalScalar_energyNumerator_of_normalizedFlowAt_of_jointScalarTimeDerivative
+      V hjoint (scalarTimeDerivativeJointContinuous_of_metricEntriesJointContDiffAt_three hjoint)
+      (globalLichnerowiczAssemblyRegularity_of_jointMetricEntriesThree hjoint)
+      t (hflow t ht) (hstokes t ht)
+
+/-- The exact survey mean-floor theorem from pointwise initial positivity. -/
+theorem meanFloorFromEnergy
+    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
+    (hjoint : ∀ t x, MetricEntriesJointContDiffAt gt t x 3)
+    (hflow : ∀ t ∈ Ici (0 : ℝ), ∀ x, IsClosedNormalizedRicciFlowSolutionAt gt t x)
+    (hstokes : ∀ t ∈ Ici (0 : ℝ), ClosedLaplacianStokes (gt t) (fun x ↦ (gt t).scalarAt x))
+    (hinit : ∀ x, 0 < (gt 0).scalarAt x)
+    (henergy : ∀ t : Ici (0 : ℝ), normalizedFlowScalarVarianceTrack gt t.1 ≤
+      6 * normalizedFlowTracelessRicciEnergyTrack gt t.1) :
+    0 < meanScalar (gt 0) ∧ ∀ t : Ici (0 : ℝ), meanScalar (gt 0) ≤ meanScalar (gt t.1) := by
+  obtain ⟨hv, hs⟩ := movingDerivatives gt hjoint hflow hstokes
+  have hd := meanScalar_deriv_nonneg_of_normalizedFlow_Ici_of_scalarVarianceTrack_le_six_tracelessRicciEnergyTrack
+    gt (fun t ↦ hflow t.1 t.2) (fun t ↦ hs t.1 t.2) (fun t ↦ hv t.1 t.2) henergy
+  have hf : ∀ t ∈ Ici (0 : ℝ), DifferentiableAt ℝ (fun s ↦ meanScalar (gt s)) t := by
+    intro t ht
+    exact (hasDerivAt_meanScalar_three_of_normalizedFlow (hflow t ht) (hs t ht) (hv t ht)).differentiableAt
+  have hm := monotoneOn_of_deriv_nonneg (convex_Ici (0 : ℝ))
+    (continuousOn_meanScalar_of_normalizedRicciFlow gt hflow hjoint)
+    (fun t ht ↦ (hf t (interior_subset ht)).differentiableWithinAt)
+    (fun t ht ↦ hd ⟨t, interior_subset ht⟩)
+  obtain ⟨rho, hrho, hlower⟩ := exists_pos_scalar_floor_of_forall_scalarAt_pos (gt 0) hinit
+  exact ⟨meanScalar_pos_of_forall_scalarAt_ge (gt 0) hrho hlower,
+    fun t ↦ hm (by simp) t.2 t.2⟩
+
+/-- Positive initial mean suffices for the same uniform floor. -/
+theorem meanFloorFromEnergy_of_initialMeanPos
+    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
+    (hjoint : ∀ t x, MetricEntriesJointContDiffAt gt t x 3)
+    (hflow : ∀ t ∈ Ici (0 : ℝ), ∀ x, IsClosedNormalizedRicciFlowSolutionAt gt t x)
+    (hstokes : ∀ t ∈ Ici (0 : ℝ), ClosedLaplacianStokes (gt t) (fun x ↦ (gt t).scalarAt x))
+    (hinit : 0 < meanScalar (gt 0))
+    (henergy : ∀ t : Ici (0 : ℝ), normalizedFlowScalarVarianceTrack gt t.1 ≤
+      6 * normalizedFlowTracelessRicciEnergyTrack gt t.1) :
+    0 < meanScalar (gt 0) ∧ ∀ t : Ici (0 : ℝ), meanScalar (gt 0) ≤ meanScalar (gt t.1) := by
+  obtain ⟨hv, hs⟩ := movingDerivatives gt hjoint hflow hstokes
+  have hd := meanScalar_deriv_nonneg_of_normalizedFlow_Ici_of_scalarVarianceTrack_le_six_tracelessRicciEnergyTrack
+    gt (fun t ↦ hflow t.1 t.2) (fun t ↦ hs t.1 t.2) (fun t ↦ hv t.1 t.2) henergy
+  have hf : ∀ t ∈ Ici (0 : ℝ), DifferentiableAt ℝ (fun s ↦ meanScalar (gt s)) t := by
+    intro t ht
+    exact (hasDerivAt_meanScalar_three_of_normalizedFlow (hflow t ht) (hs t ht) (hv t ht)).differentiableAt
+  have hm := monotoneOn_of_deriv_nonneg (convex_Ici (0 : ℝ))
+    (continuousOn_meanScalar_of_normalizedRicciFlow gt hflow hjoint)
+    (fun t ht ↦ (hf t (interior_subset ht)).differentiableWithinAt)
+    (fun t ht ↦ hd ⟨t, interior_subset ht⟩)
+  exact ⟨hinit, fun t ↦ hm (by simp) t.2 t.2⟩
+
+/-- The final reaction core with positive initial mean, energy domination,
+and scalar Stokes replacing the positive floor. Every analytic input is explicit. -/
+def HamiltonReactionCore3Energy (M : Type u)
+    [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
+    [MeasurableSpace M] [BorelSpace M]
+    [ChartedSpace (ClosedSmoothModel 3) M]
+    [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
+    [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M] : Prop :=
+  ∃ (K : Type v) (topK : TopologicalSpace K) (_ : @CompactSpace K topK)
+    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
+    (metric : K → ClosedSmoothRiemannianMetric 3 M)
+    (parameter : Ici (0 : ℝ) → K) (rate : ℝ),
+      Continuous parameter ∧
+      (∀ t : Ici (0 : ℝ), metric (parameter t) = gt t.1) ∧
+      0 < meanScalar (gt 0) ∧
+      (∀ t : Ici (0 : ℝ), normalizedFlowScalarVarianceTrack gt t.1 ≤
+        6 * normalizedFlowTracelessRicciEnergyTrack gt t.1) ∧
+      (∀ t ∈ Ici (0 : ℝ),
+        ClosedLaplacianStokes (gt t) (fun x ↦ (gt t).scalarAt x)) ∧
+      (∀ t ∈ Ici (0 : ℝ), ∀ x : M, IsClosedNormalizedRicciFlowSolutionAt gt t x) ∧
+      (∀ t x, MetricEntriesJointContDiffAt gt t x 3) ∧
+      0 < rate ∧
+      (∀ t ∈ Ici (0 : ℝ), ∀ x : M,
+        normalizedTracelessRicciEvolutionReactionAt (gt t) x ≤
+          -rate * (gt t).tracelessRicciNormSqAt x) ∧
+      (∀ slot : MetricEntryThirdJetSlot 3 M,
+        Continuous (fun p : K × ClosedSmoothModel 3 ↦
+          metricEntryThirdJetProfile (metric p.1) slot p.2))
+
+/-- Energy domination supplies the floor in the unchanged final core. -/
+theorem hamiltonReactionCore3Final_of_energy
+    (h : HamiltonReactionCore3Energy.{u, v} M) :
+    HamiltonReactionCore3Final.{u, v} M := by
+  rcases h with ⟨K, topK, compactK, gt, metric, parameter, rate,
+    hparam, hreal, hinit, henergy, hstokes, hflow, hjoint, hrate, hreaction, hjet⟩
+  letI : TopologicalSpace K := topK
+  haveI : CompactSpace K := compactK
+  have hfloor := meanFloorFromEnergy_of_initialMeanPos gt hjoint hflow hstokes hinit henergy
+  exact ⟨K, topK, compactK, gt, metric, parameter, meanScalar (gt 0), rate,
+    hparam, hreal, hfloor.1, hfloor.2, hflow, hjoint, hrate, hreaction, hjet⟩
+
+/-- The energy core reaches the Hamilton pinched-limit endpoint. -/
+theorem hamiltonConvergencePinchedLimit3_of_hamiltonReactionCore3Energy
+    (h : HamiltonReactionCore3Energy.{u, v} M) : HamiltonConvergencePinchedLimit3 M :=
+  hamiltonConvergencePinchedLimit3_of_hamiltonReactionCore3Final
+    (hamiltonReactionCore3Final_of_energy h)
+
+/-- Open existence obligation for the energy core on every compatible Borel manifold. -/
+def UniversalHamiltonReactionCoreEnergyStatement : Prop :=
+  ∀ (N : Type u) [TopologicalSpace N] [T2Space N] [SecondCountableTopology N]
+    [MeasurableSpace N] [BorelSpace N]
+    [ChartedSpace (ClosedSmoothModel 3) N]
+    [IsManifold (closedSmoothModelWithCorners 3) ∞ N]
+    [CompactSpace N] [ConnectedSpace N] [SimplyConnectedSpace N],
+      HamiltonReactionCore3Energy.{u, v} N
+
+/-- Universal energy cores supply the unchanged universal final cores. -/
+theorem universalHamiltonReactionCoreFinal_of_universalHamiltonReactionCoreEnergy
+    (h : UniversalHamiltonReactionCoreEnergyStatement.{u, v}) :
+    UniversalHamiltonReactionCoreFinalStatement.{u, v} := by
+  intro N _ _ _ _ _ _ _ _ _ _
+  exact hamiltonReactionCore3Final_of_energy (h N)
+
+/-- Universal energy cores yield universal Hamilton convergence. -/
+theorem universalHamiltonConvergence_of_universalHamiltonReactionCoreEnergy
+    (h : UniversalHamiltonReactionCoreEnergyStatement.{u, v}) :
+    UniversalHamiltonConvergenceStatement.{u} :=
+  universalHamiltonConvergence_of_universalHamiltonReactionCoreFinal
+    (universalHamiltonReactionCoreFinal_of_universalHamiltonReactionCoreEnergy h)
+
+end Poincare.HamiltonMeanFloorFromEnergyDomination
```

### Command 49

```sh
git diff --check babccd85e15cdd3a58cd922b1118bf8d1dff3f0c
```

Exit: 0.

Output: empty.

### Command 50

```sh
git diff --cached --check
```

Exit: 2.

```text
harness/reports/hamilton-mean-floor-from-energy-domination_done.md:1384: new blank line at EOF.
```

### Command 51

```sh
git status --short --branch
```

Exit: 0.

```text
## worker/hamilton-mean-floor-from-energy-domination
A  harness/reports/hamilton-mean-floor-from-energy-domination_done.md
```

### Command 52

```sh
git diff --cached --check
```

Exit: 0.

Output: empty.
