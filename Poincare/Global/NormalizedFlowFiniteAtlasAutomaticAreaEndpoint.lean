import Poincare.Global.HausdorffFiniteAtlasRestrictedAreaFormula
import Poincare.Global.NormalizedFlowFullyAssembledEnergyEndpoint
import Poincare.Global.NormalizedFlowInvariantRangeClosure
import Poincare.Global.NormalizedFlowChartFramePartitionCompactOrbitEndpoint

/-!
# Fully assembled normalized-flow endpoint from finite-atlas density data

The inverse-chart Hausdorff area formula is now a theorem.  This module
connects density-only finite-atlas data directly to the legacy global
Hausdorff variation package consumed by the fully assembled normalized-flow
energy endpoint.  The independent selected-basis identification remains
visible and no area-formula premise is reintroduced.
-/

noncomputable section

open Bundle FiberBundle Filter MeasureTheory Set
open scoped Manifold ContDiff MeasureTheory Topology ENNReal NNReal

universe u

namespace Poincare

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
variable [CompactSpace M] [ConnectedSpace M]
variable [MeasurableSpace M] [BorelSpace M]
variable [ChartedSpace (ClosedSmoothModel 3) M]
variable [IsManifold (closedSmoothModelWithCorners 3) ∞ M]

/-- The corrected chart-frame density variation constructed from one finite
inverse atlas, raw density integrability, and the analytic domination data.
The exact Hausdorff area formula is inserted internally. -/
def globalFiniteHausdorffChartFrameDensityVariation_of_finiteAtlasDensityIntegrable
    {gt : ℝ → ClosedSmoothRiemannianMetric 3 M}
    (C : FiniteExtendedChartCover (n := 3) (M := M))
    (timeSet : ℝ → Set ℝ)
    (hDensity : ∀ t : ℝ, ∀ τ ∈ timeSet t,
      ∀ i : Fin C.chartCount,
        Integrable (C.inverseChartDensity (gt τ) i)
          (coordinateLebesgueMeasure (C.coordinateDomain i)))
    (hDomination : ∀ t : ℝ,
      FiniteExtendedChartFrameDensityDominationAt
        C gt (timeSet t) t) :
    GlobalFiniteHausdorffChartFrameDensityVariation gt :=
  (GlobalFiniteExtendedChartFrameDensityData.ofDensityIntegrable
    C gt timeSet hDensity hDomination).toChartFrameDensityVariation

/-- Density-only finite-atlas data plus scalar domination, normalized flow,
joint metric regularity, and coordinate flux construct the full moving
Hausdorff scalar-variation package. -/
def GlobalFiniteExtendedChartDensityData.toScalarVariationOfNormalizedFlow
    [Nonempty M]
    {gt : ℝ → ClosedSmoothRiemannianMetric 3 M}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    {C : FiniteExtendedChartCover (n := 3) (M := M)}
    (H : GlobalFiniteExtendedChartDensityData C gt)
    (hFlow : ∀ t : ℝ, ∀ x : M,
      IsClosedNormalizedRicciFlowSolutionAt gt t x)
    (hScalarDomination :
      GlobalFiniteHausdorffChartScalarDomination H.toChartDensityVariation)
    (hJoint : ∀ t : ℝ, ∀ y : M,
      MetricEntriesJointContDiffAt gt t y 3)
    (hFlux : GlobalFiniteHausdorffChartLaplacianFlux
      H.toChartDensityVariation (fun t y ↦ (gt t).scalarAt y)) :
    GlobalFiniteHausdorffChartScalarVariation gt := by
  let hLichnerowicz : GlobalLichnerowiczAssemblyRegularity gt :=
    globalLichnerowiczAssemblyRegularity_of_jointMetricEntriesThree hJoint
  exact hScalarDomination.toScalarVariation hFlow (by norm_num)
    hLichnerowicz hFlux.closedLaplacianStokes

/-- Orbit-closure form of the fully assembled normalized-flow endpoint,
fed directly by density-only finite-atlas data.  In particular there is no
`RestrictedInverseChartPullbackHausdorffAreaFormula` argument anywhere in
the theorem-facing interface. -/
theorem hamiltonConvergencePinchedLimit3Core_of_finiteAtlasDensityData_of_differentialDissipationDecay_of_globalHausdorffDominationJointMetricEntriesCompactFlux_of_compact_metricOrbitClosure
    [Nonempty M] [SimplyConnectedSpace M]
    [TopologicalSpace (ClosedSmoothRiemannianMetric 3 M)]
    {gt : ℝ → ClosedSmoothRiemannianMetric 3 M}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (C : FiniteExtendedChartCover (n := 3) (M := M))
    (H : GlobalFiniteExtendedChartDensityData C gt)
    (hFlow : ∀ t : ℝ, ∀ x : M,
      IsClosedNormalizedRicciFlowSolutionAt gt t x)
    (hScalarDomination :
      GlobalFiniteHausdorffChartScalarDomination H.toChartDensityVariation)
    (hJoint : ∀ t : ℝ, ∀ y : M,
      MetricEntriesJointContDiffAt gt t y 3)
    (hFlux : GlobalFiniteHausdorffChartLaplacianFlux
      H.toChartDensityVariation (fun t y ↦ (gt t).scalarAt y))
    (D' : ℝ → ℝ) {rate : ℝ} (hrate : 0 < rate)
    (hDissipationDeriv : ∀ t ∈ Ici (0 : ℝ),
      HasDerivAt (normalizedMeanScalarAbsoluteVarianceDissipation gt) (D' t) t)
    (hDifferentialInequality : ∀ t ∈ Ici (0 : ℝ),
      D' t ≤ -rate * normalizedMeanScalarAbsoluteVarianceDissipation gt t)
    (hOrbitCompact : IsCompact (closure (Set.range gt)))
    (hInvariantContinuous : ContinuousOn closedMetricMeanTracelessEnergyPair
      (closure (Set.range gt)))
    {c : ℝ} (hc : 0 < c)
    (hScalarLower : ∀ t : ℝ, ∀ x : M, c ≤ (gt t).scalarAt x) :
    HamiltonConvergencePinchedLimit3Core M := by
  exact
    hamiltonConvergencePinchedLimit3Core_of_differentialDissipationDecay_of_globalHausdorffDominationJointMetricEntriesCompactFlux_of_compact_metricOrbitClosure
      hFlow H.toChartDensityVariation hScalarDomination hJoint hFlux
      D' hrate hDissipationDeriv hDifferentialInequality
      hOrbitCompact hInvariantContinuous hc hScalarLower

/-- The same density-only finite-atlas route with the exact invariant
realization boundary: closedness of the attained mean-energy range replaces
both an ambient topology on smooth metrics and compactness of its orbit
closure. -/
theorem hamiltonConvergencePinchedLimit3Core_of_finiteAtlasDensityData_of_differentialDissipationDecay_of_closed_meanEnergy_orbitRange
    [Nonempty M] [SimplyConnectedSpace M]
    {gt : ℝ → ClosedSmoothRiemannianMetric 3 M}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (C : FiniteExtendedChartCover (n := 3) (M := M))
    (H : GlobalFiniteExtendedChartDensityData C gt)
    (hFlow : ∀ t : ℝ, ∀ x : M,
      IsClosedNormalizedRicciFlowSolutionAt gt t x)
    (hScalarDomination :
      GlobalFiniteHausdorffChartScalarDomination H.toChartDensityVariation)
    (hJoint : ∀ t : ℝ, ∀ y : M,
      MetricEntriesJointContDiffAt gt t y 3)
    (hFlux : GlobalFiniteHausdorffChartLaplacianFlux
      H.toChartDensityVariation (fun t y ↦ (gt t).scalarAt y))
    (D' : ℝ → ℝ) {rate : ℝ} (hrate : 0 < rate)
    (hDissipationDeriv : ∀ t ∈ Ici (0 : ℝ),
      HasDerivAt (normalizedMeanScalarAbsoluteVarianceDissipation gt) (D' t) t)
    (hDifferentialInequality : ∀ t ∈ Ici (0 : ℝ),
      D' t ≤ -rate * normalizedMeanScalarAbsoluteVarianceDissipation gt t)
    (hRangeClosed : IsClosed
      (Set.range (fun t ↦ closedMetricMeanTracelessEnergyPair (gt t))))
    {c : ℝ} (hc : 0 < c)
    (hScalarLower : ∀ t : ℝ, ∀ x : M, c ≤ (gt t).scalarAt x) :
    HamiltonConvergencePinchedLimit3Core M := by
  exact
    hamiltonConvergencePinchedLimit3Core_of_finiteAbsoluteDissipation_of_globalHausdorffJointMetricEntriesThree_of_closed_meanEnergy_orbitRange
      hFlow
      (H.toScalarVariationOfNormalizedFlow hFlow hScalarDomination hJoint hFlux)
      hJoint hFlux.closedLaplacianStokes
      (normalizedMeanScalarAbsoluteVarianceDissipation_integrableOn_of_differential_decay
        gt D' hrate hDissipationDeriv hDifferentialInequality)
      hRangeClosed hc hScalarLower

/-- Fully corrected finite-atlas endpoint.  The theorem-facing data contain
neither an area-formula witness nor the generally noncanonical equality with
`coordinateGramVolumeDensityAt`; all density differentiation stays in the
actual inverse-chart frame. -/
theorem hamiltonConvergencePinchedLimit3Core_of_finiteAtlasFrameDensityIntegrable_of_differentialDissipationDecay_of_compact_metricOrbitClosure_of_meanLimitPos
    [Nonempty M] [SimplyConnectedSpace M]
    [TopologicalSpace (ClosedSmoothRiemannianMetric 3 M)]
    {gt : ℝ → ClosedSmoothRiemannianMetric 3 M}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (C : FiniteExtendedChartCover (n := 3) (M := M))
    (timeSet : ℝ → Set ℝ)
    (hDensity : ∀ t : ℝ, ∀ τ ∈ timeSet t,
      ∀ i : Fin C.chartCount,
        Integrable (C.inverseChartDensity (gt τ) i)
          (coordinateLebesgueMeasure (C.coordinateDomain i)))
    (hDomination : ∀ t : ℝ,
      FiniteExtendedChartFrameDensityDominationAt C gt (timeSet t) t)
    (hFlow : ∀ t : ℝ, ∀ x : M,
      IsClosedNormalizedRicciFlowSolutionAt gt t x)
    (hScalarDomination : GlobalFiniteHausdorffChartFrameScalarDomination
      (globalFiniteHausdorffChartFrameDensityVariation_of_finiteAtlasDensityIntegrable
        C timeSet hDensity hDomination))
    (hJoint : ∀ t : ℝ, ∀ y : M,
      MetricEntriesJointContDiffAt gt t y 3)
    (hPartitionGeometry :
      GlobalFiniteSubordinateHausdorffLaplacianGeometry
        gt (fun t y ↦ (gt t).scalarAt y))
    (D' : ℝ → ℝ) {rate : ℝ} (hrate : 0 < rate)
    (hDissipationDeriv : ∀ t ∈ Ici (0 : ℝ),
      HasDerivAt (normalizedMeanScalarAbsoluteVarianceDissipation gt) (D' t) t)
    (hDifferentialInequality : ∀ t ∈ Ici (0 : ℝ),
      D' t ≤ -rate * normalizedMeanScalarAbsoluteVarianceDissipation gt t)
    (hOrbitCompact : IsCompact (closure (Set.range gt)))
    (hInvariantContinuous : ContinuousOn closedMetricMeanTracelessEnergyPair
      (closure (Set.range gt)))
    (hMeanLimitPos : 0 < normalizedMeanScalarLimit gt) :
    HamiltonConvergencePinchedLimit3Core M := by
  exact
    hamiltonConvergencePinchedLimit3Core_of_differentialDissipationDecay_of_globalHausdorffChartFrameDominationJointMetricEntriesSubordinatePartition_of_compact_metricOrbitClosure_of_meanLimitPos
      hFlow
      (globalFiniteHausdorffChartFrameDensityVariation_of_finiteAtlasDensityIntegrable
        C timeSet hDensity hDomination)
      hScalarDomination hJoint hPartitionGeometry D' hrate
      hDissipationDeriv hDifferentialInequality hOrbitCompact
      hInvariantContinuous hMeanLimitPos

/-- Corrected finite-atlas endpoint with the exact invariant-realization
boundary.  Closedness of the attained mean-energy range replaces a topology
and compact orbit closure on the full smooth-metric type. -/
theorem hamiltonConvergencePinchedLimit3Core_of_finiteAtlasFrameDensityIntegrable_of_differentialDissipationDecay_of_closed_meanEnergy_orbitRange
    [Nonempty M] [SimplyConnectedSpace M]
    {gt : ℝ → ClosedSmoothRiemannianMetric 3 M}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (C : FiniteExtendedChartCover (n := 3) (M := M))
    (timeSet : ℝ → Set ℝ)
    (hDensity : ∀ t : ℝ, ∀ τ ∈ timeSet t,
      ∀ i : Fin C.chartCount,
        Integrable (C.inverseChartDensity (gt τ) i)
          (coordinateLebesgueMeasure (C.coordinateDomain i)))
    (hDomination : ∀ t : ℝ,
      FiniteExtendedChartFrameDensityDominationAt C gt (timeSet t) t)
    (hFlow : ∀ t : ℝ, ∀ x : M,
      IsClosedNormalizedRicciFlowSolutionAt gt t x)
    (hScalarDomination : GlobalFiniteHausdorffChartFrameScalarDomination
      (globalFiniteHausdorffChartFrameDensityVariation_of_finiteAtlasDensityIntegrable
        C timeSet hDensity hDomination))
    (hJoint : ∀ t : ℝ, ∀ y : M,
      MetricEntriesJointContDiffAt gt t y 3)
    (hPartitionGeometry :
      GlobalFiniteSubordinateHausdorffLaplacianGeometry
        gt (fun t y ↦ (gt t).scalarAt y))
    (D' : ℝ → ℝ) {rate : ℝ} (hrate : 0 < rate)
    (hDissipationDeriv : ∀ t ∈ Ici (0 : ℝ),
      HasDerivAt (normalizedMeanScalarAbsoluteVarianceDissipation gt) (D' t) t)
    (hDifferentialInequality : ∀ t ∈ Ici (0 : ℝ),
      D' t ≤ -rate * normalizedMeanScalarAbsoluteVarianceDissipation gt t)
    (hRangeClosed : IsClosed
      (Set.range (fun t ↦ closedMetricMeanTracelessEnergyPair (gt t))))
    {c : ℝ} (hc : 0 < c)
    (hScalarLower : ∀ t : ℝ, ∀ x : M, c ≤ (gt t).scalarAt x) :
    HamiltonConvergencePinchedLimit3Core M := by
  let hVolume :=
    globalFiniteHausdorffChartFrameDensityVariation_of_finiteAtlasDensityIntegrable
      C timeSet hDensity hDomination
  let hLichnerowicz : GlobalLichnerowiczAssemblyRegularity gt :=
    globalLichnerowiczAssemblyRegularity_of_jointMetricEntriesThree hJoint
  let hStokes : ∀ t : ℝ,
      ClosedLaplacianStokes (gt t) (fun y ↦ (gt t).scalarAt y) :=
    hPartitionGeometry.closedLaplacianStokes
  let hScalar : GlobalFiniteHausdorffChartFrameScalarVariation gt :=
    hScalarDomination.toScalarVariation
      hFlow (by norm_num) hLichnerowicz hStokes
  exact
    hamiltonConvergencePinchedLimit3Core_of_normalizedFlow_finiteAbsoluteDissipation_of_closed_meanEnergy_orbitRange
      gt hFlow
      (hScalar.hasDerivAt_totalScalar_energyNumerator_of_globalLichnerowiczRegularity
        hFlow hLichnerowicz hStokes)
      (hScalar.hasDerivAt_totalVolume_of_normalizedFlow hFlow)
      (normalizedMeanScalarAbsoluteVarianceDissipation_integrableOn_of_differential_decay
        gt D' hrate hDissipationDeriv hDifferentialInequality)
      hRangeClosed hc hScalarLower

end Poincare
