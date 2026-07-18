import Mathlib.Analysis.Calculus.Deriv.Shift
import Poincare.Global.ForwardTailIntegrability
import Poincare.Global.NormalizedFlowCompactMeanEnergyMeasureHamiltonPinchingDecay

/-!
# Compact mean-energy decay from eventual Hamilton pinching

The Hamilton coercivity used by the compact mean-energy endpoint need not hold
from time zero.  This module starts it at an arbitrary nonnegative time `T`.
The compact-family realization makes the energy track continuous, hence
integrable on `[0,T]`; the Hamilton argument is applied to the translated flow
`s ↦ g(T+s)` and translation invariance returns an integrable tail on
`Ici T`.

Metric time derivatives, the normalized-flow equation, joint metric-entry
regularity, and total-volume variation are transported through the time shift
below.  Thus no unproved time-shift regularity or volume identity is hidden in
the eventual package.
-/

noncomputable section

open Bundle FiberBundle Filter MeasureTheory Set
open scoped Manifold ContDiff MeasureTheory Topology ENNReal NNReal

universe u v

namespace Poincare

/-!
## Time-translation lemmas
-/

/-- Translating the time parameter does not change the pointwise metric time
derivative. -/
theorem timeDerivAt_const_add
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (ClosedSmoothModel n) M]
    [IsManifold (closedSmoothModelWithCorners n) ∞ M]
    (gt : ℝ → ClosedSmoothRiemannianMetric n M) (T s : ℝ) :
    timeDerivAt (fun r ↦ gt (T + r)) s = timeDerivAt gt (T + s) := by
  funext x a b
  exact deriv_comp_const_add (fun r ↦ (gt r).inner x a b) T s

/-- A normalized Ricci-flow solution remains one after translating its time
parameter. -/
theorem isClosedNormalizedRicciFlowSolutionAt_const_add
    {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
    [CompactSpace M] [ConnectedSpace M]
    [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (ClosedSmoothModel n) M]
    [IsManifold (closedSmoothModelWithCorners n) ∞ M]
    (gt : ℝ → ClosedSmoothRiemannianMetric n M) (T s : ℝ) (x : M)
    (hFlow : IsClosedNormalizedRicciFlowSolutionAt gt (T + s) x) :
    IsClosedNormalizedRicciFlowSolutionAt (fun r ↦ gt (T + r)) s x := by
  constructor
  · intro r
    exact hFlow.leviCivita (T + r)
  · intro Z hZ hreg w
    rw [deriv_comp_const_add
      (fun r ↦ (gt r).inner x (Z x) w) T s]
    exact hFlow.flow hZ hreg w

/-- Joint time-space regularity of metric entries is invariant under a
translation of the time coordinate. -/
theorem metricEntriesJointContDiffAt_const_add
    {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (ClosedSmoothModel n) M]
    [IsManifold (closedSmoothModelWithCorners n) ∞ M]
    (gt : ℝ → ClosedSmoothRiemannianMetric n M) (T s : ℝ) (x : M)
    {k : ℕ∞ω} (hJoint : MetricEntriesJointContDiffAt gt (T + s) x k) :
    MetricEntriesJointContDiffAt (fun r ↦ gt (T + r)) s x k := by
  intro a b
  have hShift : ContDiffAt ℝ k
      (fun p : ℝ × ClosedSmoothModel n ↦ (T + p.1, p.2))
      (s, extChartAt (closedSmoothModelWithCorners n) x x) :=
    (contDiffAt_const.add contDiffAt_fst).prodMk contDiffAt_snd
  have hComp := (hJoint a b).comp
    (s, extChartAt (closedSmoothModelWithCorners n) x x) hShift
  simpa only [metricEntryJointChart, Function.comp_apply] using hComp

/-!
## Eventual geometric package
-/

/-- Compact forward-flow data whose Hamilton pinching hypotheses begin only
at the nonnegative time `tailStart`.

As in the global package, neither the Ricci quotient bound nor a
scalar-to-mean comparison is stored. -/
structure
    NormalizedFlowSphereCompactMeanEnergyMeasureEventualHamiltonPinchingCoreData3
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M]
    [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (ClosedSmoothModel 3) M]
    [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
    [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M] where
  K : Type v
  topologicalSpaceK : TopologicalSpace K
  compactSpaceK : @CompactSpace K topologicalSpaceK
  gt : ℝ → ClosedSmoothRiemannianMetric 3 M
  metric : K → ClosedSmoothRiemannianMetric 3 M
  parameter : Ici (0 : ℝ) → K
  parameterContinuous :
    letI : TopologicalSpace K := topologicalSpaceK
    Continuous parameter
  realizesFlow : ∀ t : Ici (0 : ℝ),
    metric (parameter t) = gt t.1
  meanScalarFloor : ℝ
  meanScalarFloor_pos : 0 < meanScalarFloor
  meanScalarLower : ∀ t : Ici (0 : ℝ),
    meanScalarFloor ≤ meanScalar (gt t.1)
  normalizedFlow : ∀ t ∈ Ici (0 : ℝ), ∀ x : M,
    IsClosedNormalizedRicciFlowSolutionAt gt t x
  compactFiniteAtlasChartFrameDensityData :
    CompactFiniteAtlasChartFrameDensityData gt
  jointMetricEntries : ∀ t : ℝ, ∀ x : M,
    MetricEntriesJointContDiffAt gt t x 3
  tailStart : ℝ
  tailStart_nonneg : 0 ≤ tailStart
  pinchingEpsilon : ℝ
  pinchingEpsilon_pos : 0 < pinchingEpsilon
  pinchingEpsilon_le_one_third : pinchingEpsilon ≤ 1 / 3
  pinchingDelta : ℝ
  pinchingDelta_nonneg : 0 ≤ pinchingDelta
  pinchingDelta_le_two : pinchingDelta ≤ 2
  pinchingDelta_admissible :
    pinchingDelta ≤
      PinchingAlgebra.pinchedTracelessAdmissibleDelta3 pinchingEpsilon
  scalarPositiveOnTail : ∀ t ∈ Ici tailStart, ∀ x : M,
    0 < (gt t).scalarAt x
  ricciEigenvalueFloorOnTail : ∀ t ∈ Ici tailStart,
    GlobalRicciEigenvalueFloor3 (gt t) pinchingEpsilon
  finiteVolumeMeasureContinuous :
    letI : TopologicalSpace K := topologicalSpaceK
    Continuous (fun k ↦ closedMetricFiniteVolumeMeasure (metric k))
  scalarJointContinuous :
    letI : TopologicalSpace K := topologicalSpaceK
    Continuous (fun p : K × M ↦ (metric p.1).scalarAt p.2)
  tracelessRicciNormSqJointContinuous :
    letI : TopologicalSpace K := topologicalSpaceK
    Continuous
      (fun p : K × M ↦ (metric p.1).tracelessRicciNormSqAt p.2)

section EventualCore

variable {M : Type u} [TopologicalSpace M] [T2Space M]
variable [SecondCountableTopology M]
variable [MeasurableSpace M] [BorelSpace M]
variable [ChartedSpace (ClosedSmoothModel 3) M]
variable [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
variable [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M]

abbrev EventualHamiltonCore :=
  NormalizedFlowSphereCompactMeanEnergyMeasureEventualHamiltonPinchingCoreData3

namespace NormalizedFlowSphereCompactMeanEnergyMeasureEventualHamiltonPinchingCoreData3

/-- The quotient coefficient forced by the eventual eigenvalue floor. -/
def pinchingQuotientCoefficient
    (data : EventualHamiltonCore.{u, v} M) : ℝ :=
  1 - 4 * data.pinchingEpsilon + 6 * data.pinchingEpsilon ^ 2

theorem pinchingQuotientCoefficient_pos
    (data : EventualHamiltonCore.{u, v} M) :
    0 < data.pinchingQuotientCoefficient := by
  simpa only [pinchingQuotientCoefficient] using
    Poincare.pinchingQuotientCoefficient_pos data.pinchingEpsilon

/-- The quotient bound on the eventual tail is derived from positive scalar
curvature and the global eigenvalue floor. -/
theorem globalPinchingQuotientBoundOnTail
    (data : EventualHamiltonCore.{u, v} M)
    (t : ℝ) (ht : t ∈ Ici data.tailStart) :
    GlobalPinchingQuotientBound3 (data.gt t)
      data.pinchingQuotientCoefficient := by
  simpa only [pinchingQuotientCoefficient] using
    (data.gt t).globalPinchingQuotientBound_of_globalRicciEigenvalueFloor
      (data.scalarPositiveOnTail t ht)
      (data.ricciEigenvalueFloorOnTail t ht)

/-- Compactness and the global positive mean floor still provide one uniform
scalar-to-mean factor, independent of the tail start. -/
theorem existsScalarMeanFactor
    (data : EventualHamiltonCore.{u, v} M) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : Ici (0 : ℝ), ∀ x : M,
      (data.gt t.1).scalarAt x ≤ C * meanScalar (data.gt t.1) := by
  letI : TopologicalSpace data.K := data.topologicalSpaceK
  letI : CompactSpace data.K := data.compactSpaceK
  exact
    exists_pos_uniform_scalarAt_le_mul_meanScalar_of_compact_parameterization_of_meanLower
      data.gt data.metric data.parameter data.realizesFlow
      data.meanScalarFloor_pos data.meanScalarLower data.scalarJointContinuous

/-- A fixed compactness-produced scalar-to-mean factor. -/
noncomputable def scalarMeanFactor
    (data : EventualHamiltonCore.{u, v} M) : ℝ :=
  Classical.choose data.existsScalarMeanFactor

theorem scalarMeanFactor_pos
    (data : EventualHamiltonCore.{u, v} M) :
    0 < data.scalarMeanFactor :=
  (Classical.choose_spec data.existsScalarMeanFactor).1

theorem scalarAt_le_scalarMeanFactor_mul_meanScalar
    (data : EventualHamiltonCore.{u, v} M)
    (t : Ici (0 : ℝ)) (x : M) :
    (data.gt t.1).scalarAt x ≤
      data.scalarMeanFactor * meanScalar (data.gt t.1) :=
  (Classical.choose_spec data.existsScalarMeanFactor).2 t x

/-- The explicit coefficient left after the eventual quotient and
scalar-to-mean estimates. -/
noncomputable def pinchingCoefficientGap
    (data : EventualHamiltonCore.{u, v} M) : ℝ :=
  (4 / 3 : ℝ) -
    2 * (2 - data.pinchingDelta) * data.pinchingQuotientCoefficient *
      data.scalarMeanFactor

/-- The flow translated so that the eventual tail begins at relative time
zero. -/
def shiftedFlow
    (data : EventualHamiltonCore.{u, v} M) :
    ℝ → ClosedSmoothRiemannianMetric 3 M :=
  fun s ↦ data.gt (data.tailStart + s)

/-- The original forward normalized-flow equation transports to the shifted
tail. -/
theorem shiftedFlow_normalizedFlow
    (data : EventualHamiltonCore.{u, v} M) :
    ∀ s ∈ Ici (0 : ℝ), ∀ x : M,
      IsClosedNormalizedRicciFlowSolutionAt data.shiftedFlow s x := by
  intro s hs x
  apply isClosedNormalizedRicciFlowSolutionAt_const_add
  exact data.normalizedFlow (data.tailStart + s)
    (add_nonneg data.tailStart_nonneg hs) x

/-- Global joint `C³` metric-entry regularity transports to the shifted
tail. -/
theorem shiftedFlow_jointMetricEntries
    (data : EventualHamiltonCore.{u, v} M) :
    ∀ s : ℝ, ∀ x : M,
      MetricEntriesJointContDiffAt data.shiftedFlow s x 3 := by
  intro s x
  exact metricEntriesJointContDiffAt_const_add data.gt data.tailStart s x
    (data.jointMetricEntries (data.tailStart + s) x)

/-- The original chart-frame volume variation and the proved time-derivative
translation identity give the shifted volume variation. -/
theorem shiftedFlow_volumeVariation
    (data : EventualHamiltonCore.{u, v} M) :
    ∀ s ∈ Ici (0 : ℝ),
      HasDerivAt (fun r ↦ totalVolume (data.shiftedFlow r))
        (totalVolumeFirstVariation (data.shiftedFlow s)
          (timeDerivAt data.shiftedFlow s)) s := by
  intro s hs
  have hPhysicalNonneg : 0 ≤ data.tailStart + s :=
    add_nonneg data.tailStart_nonneg hs
  have hOriginal :=
    data.compactFiniteAtlasChartFrameDensityData.toChartFrameDensityVariation.hasDerivAt_totalVolume_of_normalizedFlowAt
      (data.tailStart + s)
      (data.normalizedFlow (data.tailStart + s) hPhysicalNonneg)
  have hShifted := hOriginal.comp_const_add data.tailStart s
  have hTimeDeriv :
      timeDerivAt data.shiftedFlow s =
        timeDerivAt data.gt (data.tailStart + s) := by
    simpa only [shiftedFlow] using
      timeDerivAt_const_add data.gt data.tailStart s
  rw [hTimeDeriv]
  simpa only [shiftedFlow] using hShifted

theorem shiftedFlow_scalarPositive
    (data : EventualHamiltonCore.{u, v} M) :
    ∀ s ∈ Ici (0 : ℝ), ∀ x : M,
      0 < (data.shiftedFlow s).scalarAt x := by
  intro s hs x
  exact data.scalarPositiveOnTail (data.tailStart + s)
    (by simpa only [mem_Ici, le_add_iff_nonneg_right] using hs) x

theorem shiftedFlow_ricciEigenvalueFloor
    (data : EventualHamiltonCore.{u, v} M) :
    ∀ s ∈ Ici (0 : ℝ),
      GlobalRicciEigenvalueFloor3 (data.shiftedFlow s)
        data.pinchingEpsilon := by
  intro s hs
  exact data.ricciEigenvalueFloorOnTail (data.tailStart + s)
    (by simpa only [mem_Ici, le_add_iff_nonneg_right] using hs)

theorem shiftedFlow_globalPinchingQuotientBound
    (data : EventualHamiltonCore.{u, v} M) :
    ∀ s ∈ Ici (0 : ℝ),
      GlobalPinchingQuotientBound3 (data.shiftedFlow s)
        data.pinchingQuotientCoefficient := by
  intro s hs
  exact data.globalPinchingQuotientBoundOnTail (data.tailStart + s)
    (by simpa only [mem_Ici, le_add_iff_nonneg_right] using hs)

theorem shiftedFlow_scalarMeanComparison
    (data : EventualHamiltonCore.{u, v} M) :
    ∀ s ∈ Ici (0 : ℝ), ∀ x : M,
      (data.shiftedFlow s).scalarAt x ≤
        data.scalarMeanFactor * meanScalar (data.shiftedFlow s) := by
  intro s hs x
  exact data.scalarAt_le_scalarMeanFactor_mul_meanScalar
    ⟨data.tailStart + s, add_nonneg data.tailStart_nonneg hs⟩ x

end NormalizedFlowSphereCompactMeanEnergyMeasureEventualHamiltonPinchingCoreData3

end EventualCore

/-- Eventual Hamilton pinching with an explicit scalar-to-mean comparison on
the tail and a positive coefficient gap for that comparison factor.

The compact core still exposes a convenient globally valid factor chosen from
compactness, but decay does not use that noncanonical choice.  This structure stores
the factor actually proved on `Ici tailStart`; in particular, an asymptotic
near-round estimate may take the sharp explicit value `3 / 2` without making
any claim about the compactness-produced factor on the omitted initial
interval.  There is no global-in-time reaction-domination field. -/
structure
    NormalizedFlowSphereCompactMeanEnergyMeasureEventualHamiltonPinchingDecayAnalyticData3
    (M : Type u) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M]
    [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (ClosedSmoothModel 3) M]
    [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
    [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M] where
  pinching :
    NormalizedFlowSphereCompactMeanEnergyMeasureEventualHamiltonPinchingCoreData3.{u, v}
      M
  tailScalarMeanFactor : ℝ
  tailScalarMeanFactor_pos : 0 < tailScalarMeanFactor
  scalarAt_le_tailScalarMeanFactor_mul_meanScalar :
    ∀ t ∈ Ici pinching.tailStart, ∀ x : M,
      (pinching.gt t).scalarAt x ≤
        tailScalarMeanFactor * meanScalar (pinching.gt t)
  tailPinchingCoefficientGap_pos :
    0 < (4 / 3 : ℝ) -
      2 * (2 - pinching.pinchingDelta) *
        pinching.pinchingQuotientCoefficient * tailScalarMeanFactor

section EventualDecay

variable {M : Type u} [TopologicalSpace M] [T2Space M]
variable [SecondCountableTopology M]
variable [MeasurableSpace M] [BorelSpace M]
variable [ChartedSpace (ClosedSmoothModel 3) M]
variable [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
variable [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M]

abbrev EventualHamiltonDecay :=
  NormalizedFlowSphereCompactMeanEnergyMeasureEventualHamiltonPinchingDecayAnalyticData3

namespace NormalizedFlowSphereCompactMeanEnergyMeasureEventualHamiltonPinchingDecayAnalyticData3

/-- The coefficient left after using the scalar-to-mean factor actually
available on the eventual tail. -/
noncomputable def pinchingCoefficientGap
    (data : EventualHamiltonDecay.{u, v} M) : ℝ :=
  (4 / 3 : ℝ) -
    2 * (2 - data.pinching.pinchingDelta) *
      data.pinching.pinchingQuotientCoefficient * data.tailScalarMeanFactor

theorem pinchingCoefficientGap_pos
    (data : EventualHamiltonDecay.{u, v} M) :
    0 < data.pinchingCoefficientGap := by
  simpa only [pinchingCoefficientGap] using
    data.tailPinchingCoefficientGap_pos

/-- Optional compatibility constructor using the compactness-produced global
factor.  Asymptotic applications should normally provide a sharper explicit
tail factor instead. -/
noncomputable def ofGlobalScalarMeanFactor
    (core : EventualHamiltonCore.{u, v} M)
    (hGap : 0 < core.pinchingCoefficientGap) :
    EventualHamiltonDecay.{u, v} M :=
  { pinching := core
    tailScalarMeanFactor := core.scalarMeanFactor
    tailScalarMeanFactor_pos := core.scalarMeanFactor_pos
    scalarAt_le_tailScalarMeanFactor_mul_meanScalar := by
      intro t ht x
      exact core.scalarAt_le_scalarMeanFactor_mul_meanScalar
        ⟨t, core.tailStart_nonneg.trans ht⟩ x
    tailPinchingCoefficientGap_pos := by
      simpa only
          [NormalizedFlowSphereCompactMeanEnergyMeasureEventualHamiltonPinchingCoreData3.pinchingCoefficientGap] using
        hGap }

/-- The uniform tail decay rate is the positive gap times the global
mean-scalar floor. -/
noncomputable def reactionDecayRate
    (data : EventualHamiltonDecay.{u, v} M) : ℝ :=
  data.pinchingCoefficientGap * data.pinching.meanScalarFloor

theorem reactionDecayRate_pos
    (data : EventualHamiltonDecay.{u, v} M) :
    0 < data.reactionDecayRate :=
  mul_pos data.pinchingCoefficientGap_pos data.pinching.meanScalarFloor_pos

/-- The explicit coefficient gap and mean floor give the rate inequality on
the shifted tail. -/
theorem shiftedFlow_rate
    (data : EventualHamiltonDecay.{u, v} M) :
    ∀ s ∈ Ici (0 : ℝ),
      data.reactionDecayRate ≤
        ((4 / 3 : ℝ) -
          2 * (2 - data.pinching.pinchingDelta) *
            data.pinching.pinchingQuotientCoefficient *
              data.tailScalarMeanFactor) *
          meanScalar (data.pinching.shiftedFlow s) := by
  intro s hs
  have hMeanLower := data.pinching.meanScalarLower
    ⟨data.pinching.tailStart + s,
      add_nonneg data.pinching.tailStart_nonneg hs⟩
  have hScaled := mul_le_mul_of_nonneg_left hMeanLower
    data.pinchingCoefficientGap_pos.le
  simpa only [reactionDecayRate,
    pinchingCoefficientGap,
    NormalizedFlowSphereCompactMeanEnergyMeasureEventualHamiltonPinchingCoreData3.shiftedFlow] using
    hScaled

/-- The stored physical-tail comparison transports to the shifted flow used
by the Hamilton energy estimate. -/
theorem shiftedFlow_scalarMeanComparison
    (data : EventualHamiltonDecay.{u, v} M) :
    ∀ s ∈ Ici (0 : ℝ), ∀ x : M,
      (data.pinching.shiftedFlow s).scalarAt x ≤
        data.tailScalarMeanFactor *
          meanScalar (data.pinching.shiftedFlow s) := by
  intro s hs x
  simpa only
      [NormalizedFlowSphereCompactMeanEnergyMeasureEventualHamiltonPinchingCoreData3.shiftedFlow] using
    data.scalarAt_le_tailScalarMeanFactor_mul_meanScalar
      (data.pinching.tailStart + s)
      (by simpa only [mem_Ici, le_add_iff_nonneg_right] using hs) x

/-- Eventual geometric coercivity gives finite total forward energy.

The shifted Hamilton theorem proves integrability on relative `Ici 0`.
`integrableOn_Ici_iff_integrableOn_comp_const_add_Ici_zero` translates this
to the physical tail `Ici tailStart`, and continuity handles the omitted
compact initial interval. -/
theorem finiteTracelessRicciEnergy
    (data : EventualHamiltonDecay.{u, v} M) :
    IntegrableOn
      (normalizedFlowTracelessRicciEnergyTrack data.pinching.gt) (Ici 0) := by
  let core := data.pinching
  letI : TopologicalSpace core.K := core.topologicalSpaceK
  letI : CompactSpace core.K := core.compactSpaceK
  letI : ∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative
        (core.gt t).leviCivita 1 :=
    fun _t ↦ inferInstance
  letI : ∀ s : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative
        (core.shiftedFlow s).leviCivita 1 :=
    fun _s ↦ inferInstance
  have hEnergyContinuous : ContinuousOn
      (normalizedFlowTracelessRicciEnergyTrack core.gt) (Ici 0) :=
    continuousOn_normalizedFlowTracelessRicciEnergyTrack_of_parameterization
      core.gt core.metric core.parameter core.parameterContinuous
        core.realizesFlow core.finiteVolumeMeasureContinuous
          core.tracelessRicciNormSqJointContinuous
  have hShiftMap : ContinuousOn
      (fun s : ℝ ↦ core.tailStart + s) (Ici 0) :=
    (continuous_const.add continuous_id).continuousOn
  have hShiftMapsTo : MapsTo
      (fun s : ℝ ↦ core.tailStart + s) (Ici 0) (Ici 0) := by
    intro s hs
    exact add_nonneg core.tailStart_nonneg hs
  have hShiftedEnergyContinuousOriginal : ContinuousOn
      (fun s : ℝ ↦
        normalizedFlowTracelessRicciEnergyTrack core.gt
          (core.tailStart + s)) (Ici 0) :=
    hEnergyContinuous.comp' hShiftMap hShiftMapsTo
  have hShiftedEnergyContinuous : ContinuousOn
      (normalizedFlowTracelessRicciEnergyTrack core.shiftedFlow) (Ici 0) := by
    simpa only [NormalizedFlowSphereCompactMeanEnergyMeasureEventualHamiltonPinchingCoreData3.shiftedFlow,
      normalizedFlowTracelessRicciEnergyTrack] using
      hShiftedEnergyContinuousOriginal
  have hShiftedEnergyMeasurable : AEStronglyMeasurable
      (normalizedFlowTracelessRicciEnergyTrack core.shiftedFlow)
      (MeasureTheory.volume.restrict (Ici 0)) :=
    normalizedFlowTracelessRicciEnergyTrack_aestronglyMeasurable_of_continuousOn
      core.shiftedFlow hShiftedEnergyContinuous
  have hShiftedIntegrable : IntegrableOn
      (normalizedFlowTracelessRicciEnergyTrack core.shiftedFlow) (Ici 0) :=
    normalizedFlowTracelessRicciEnergyTrack_integrableOn_of_pinching_domination_of_normalizedFlow_global_jointMetricEntries_Ici
      core.shiftedFlow core.pinchingEpsilon_pos
        core.pinchingEpsilon_le_one_third core.pinchingDelta_nonneg
        core.pinchingDelta_le_two core.pinchingDelta_admissible
        core.pinchingQuotientCoefficient_pos.le data.reactionDecayRate_pos
        core.shiftedFlow_normalizedFlow core.shiftedFlow_volumeVariation
        hShiftedEnergyMeasurable core.shiftedFlow_jointMetricEntries
        core.shiftedFlow_scalarPositive
        core.shiftedFlow_ricciEigenvalueFloor
        core.shiftedFlow_globalPinchingQuotientBound
        data.shiftedFlow_scalarMeanComparison data.shiftedFlow_rate
  have hShiftedTail : IntegrableOn
      (fun s : ℝ ↦
        normalizedFlowTracelessRicciEnergyTrack core.gt
          (core.tailStart + s)) (Ici 0) := by
    simpa only [NormalizedFlowSphereCompactMeanEnergyMeasureEventualHamiltonPinchingCoreData3.shiftedFlow,
      normalizedFlowTracelessRicciEnergyTrack] using hShiftedIntegrable
  have hTail : IntegrableOn
      (normalizedFlowTracelessRicciEnergyTrack core.gt)
      (Ici core.tailStart) :=
    (integrableOn_Ici_iff_integrableOn_comp_const_add_Ici_zero
      (normalizedFlowTracelessRicciEnergyTrack core.gt) core.tailStart).2
        hShiftedTail
  exact integrableOn_Ici_zero_of_continuousOn_of_integrableOn_tail
    core.tailStart_nonneg hEnergyContinuous hTail

/-- The eventual package reaches the same compact moving-measure analytic
endpoint as the globally coercive package. -/
noncomputable def toMeasureAnalyticData3
    (data : EventualHamiltonDecay.{u, v} M) :
    NormalizedFlowSphereCompactMeanEnergyMeasureAnalyticData3.{u, v} M :=
  { K := data.pinching.K
    topologicalSpaceK := data.pinching.topologicalSpaceK
    compactSpaceK := data.pinching.compactSpaceK
    gt := data.pinching.gt
    metric := data.pinching.metric
    parameter := data.pinching.parameter
    realizesFlow := data.pinching.realizesFlow
    meanScalarFloor := data.pinching.meanScalarFloor
    meanScalarFloor_pos := data.pinching.meanScalarFloor_pos
    meanScalarLower := data.pinching.meanScalarLower
    finiteTracelessRicciEnergy := data.finiteTracelessRicciEnergy
    finiteVolumeMeasureContinuous :=
      data.pinching.finiteVolumeMeasureContinuous
    scalarJointContinuous := data.pinching.scalarJointContinuous
    tracelessRicciNormSqJointContinuous :=
      data.pinching.tracelessRicciNormSqJointContinuous }

theorem sphereConclusion
    (data : EventualHamiltonDecay.{u, v} M)
    (unitRecognition : UnitConstantCurvatureSphereRecognition3 M) :
    Nonempty
      (M ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) (1 : ℝ)) :=
  data.toMeasureAnalyticData3.sphereConclusion unitRecognition

end NormalizedFlowSphereCompactMeanEnergyMeasureEventualHamiltonPinchingDecayAnalyticData3

end EventualDecay

end Poincare
