import Poincare.Global.NormalizedFlowHausdorffAutomaticStokes
import Poincare.Global.NormalizedFlowDissipationDifferentialDecay

/-!
# Fully assembled normalized-flow energy endpoint

This module composes the strongest concrete reductions in the normalized-flow
route.  Coordinate scalar-density domination is upgraded to actual moving
Hausdorff integrals; compactly supported coordinate fluxes prove Stokes;
joint `C³` metric entries construct Lichnerowicz regularity; a coercive
differential inequality proves finite dissipation; and a compact parameter
space continuous only in the two scalar invariants realizes the Einstein
limit.
-/

noncomputable section

open Bundle FiberBundle Filter MeasureTheory Set
open scoped Manifold ContDiff MeasureTheory Topology ENNReal NNReal

universe u v

namespace Poincare

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
variable [CompactSpace M] [ConnectedSpace M]
variable [MeasurableSpace M] [BorelSpace M]
variable [ChartedSpace (ClosedSmoothModel 3) M]
variable [IsManifold (closedSmoothModelWithCorners 3) ∞ M]

/-- Fully assembled endpoint with the sharp positivity premise: positivity of
the actual limiting mean scalar, rather than a uniform pointwise scalar floor
along the whole flow. -/
theorem hamiltonConvergencePinchedLimit3Core_of_differentialDissipationDecay_of_globalHausdorffDominationJointMetricEntriesCompactFlux_of_compact_meanEnergy_parameterization_of_meanLimitPos
    [Nonempty M] [SimplyConnectedSpace M]
    {K : Type v} [TopologicalSpace K] [CompactSpace K]
    {gt : ℝ → ClosedSmoothRiemannianMetric 3 M}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hFlow : ∀ t : ℝ, ∀ x : M,
      IsClosedNormalizedRicciFlowSolutionAt gt t x)
    (hHausdorffVolume : GlobalFiniteHausdorffChartDensityVariation gt)
    (hScalarDomination :
      GlobalFiniteHausdorffChartScalarDomination hHausdorffVolume)
    (hJoint : ∀ t : ℝ, ∀ y : M,
      MetricEntriesJointContDiffAt gt t y 3)
    (hFlux : GlobalFiniteHausdorffChartLaplacianFlux
      hHausdorffVolume (fun t y ↦ (gt t).scalarAt y))
    (D' : ℝ → ℝ) {rate : ℝ} (hrate : 0 < rate)
    (hDissipationDeriv : ∀ t ∈ Ici (0 : ℝ),
      HasDerivAt (normalizedMeanScalarAbsoluteVarianceDissipation gt) (D' t) t)
    (hDifferentialInequality : ∀ t ∈ Ici (0 : ℝ),
      D' t ≤ -rate * normalizedMeanScalarAbsoluteVarianceDissipation gt t)
    (metric : K → ClosedSmoothRiemannianMetric 3 M)
    (parameter : ℝ → K)
    (hRealize : ∀ t : ℝ, metric (parameter t) = gt t)
    (hInvariantContinuous :
      Continuous (fun k ↦ closedMetricMeanTracelessEnergyPair (metric k)))
    (hMeanLimitPos : 0 < normalizedMeanScalarLimit gt) :
    HamiltonConvergencePinchedLimit3Core M := by
  let hLichnerowicz : GlobalLichnerowiczAssemblyRegularity gt :=
    globalLichnerowiczAssemblyRegularity_of_jointMetricEntriesThree hJoint
  let hStokes : ∀ t : ℝ,
      ClosedLaplacianStokes (gt t) (fun y ↦ (gt t).scalarAt y) :=
    hFlux.closedLaplacianStokes
  let hHausdorffScalar : GlobalFiniteHausdorffChartScalarVariation gt :=
    hScalarDomination.toScalarVariation
      hFlow (by norm_num) hLichnerowicz hStokes
  exact
    hamiltonConvergencePinchedLimit3Core_of_normalizedFlow_finiteAbsoluteDissipation_of_compact_meanEnergy_parameterization_of_meanLimitPos
      gt hFlow
      (hHausdorffScalar.hasDerivAt_totalScalar_energyNumerator_of_globalLichnerowiczRegularity
        hFlow hLichnerowicz hStokes)
      (hHausdorffScalar.hasDerivAt_totalVolume_of_normalizedFlow hFlow)
      (normalizedMeanScalarAbsoluteVarianceDissipation_integrableOn_of_differential_decay
        gt D' hrate hDissipationDeriv hDifferentialInequality)
      metric parameter hRealize hInvariantContinuous hMeanLimitPos

/-- The strongest assembled positive-Einstein endpoint currently proved in
the normalized-flow route.  Every hypothesis is raw geometric, analytic, or
compact-parameter data; no moving-integral derivative, Stokes conclusion,
finite-dissipation conclusion, Lichnerowicz package, or smooth metric
subsequence is assumed. -/
theorem hamiltonConvergencePinchedLimit3Core_of_differentialDissipationDecay_of_globalHausdorffDominationJointMetricEntriesCompactFlux_of_compact_meanEnergy_parameterization
    [Nonempty M] [SimplyConnectedSpace M]
    {K : Type v} [TopologicalSpace K] [CompactSpace K]
    {gt : ℝ → ClosedSmoothRiemannianMetric 3 M}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hFlow : ∀ t : ℝ, ∀ x : M,
      IsClosedNormalizedRicciFlowSolutionAt gt t x)
    (hHausdorffVolume : GlobalFiniteHausdorffChartDensityVariation gt)
    (hScalarDomination :
      GlobalFiniteHausdorffChartScalarDomination hHausdorffVolume)
    (hJoint : ∀ t : ℝ, ∀ y : M,
      MetricEntriesJointContDiffAt gt t y 3)
    (hFlux : GlobalFiniteHausdorffChartLaplacianFlux
      hHausdorffVolume (fun t y ↦ (gt t).scalarAt y))
    (D' : ℝ → ℝ) {rate : ℝ} (hrate : 0 < rate)
    (hDissipationDeriv : ∀ t ∈ Ici (0 : ℝ),
      HasDerivAt (normalizedMeanScalarAbsoluteVarianceDissipation gt) (D' t) t)
    (hDifferentialInequality : ∀ t ∈ Ici (0 : ℝ),
      D' t ≤ -rate * normalizedMeanScalarAbsoluteVarianceDissipation gt t)
    (metric : K → ClosedSmoothRiemannianMetric 3 M)
    (parameter : ℝ → K)
    (hRealize : ∀ t : ℝ, metric (parameter t) = gt t)
    (hInvariantContinuous :
      Continuous (fun k ↦ closedMetricMeanTracelessEnergyPair (metric k)))
    {c : ℝ} (hc : 0 < c)
    (hScalarLower : ∀ t : ℝ, ∀ x : M, c ≤ (gt t).scalarAt x) :
    HamiltonConvergencePinchedLimit3Core M := by
  let hLichnerowicz : GlobalLichnerowiczAssemblyRegularity gt :=
    globalLichnerowiczAssemblyRegularity_of_jointMetricEntriesThree hJoint
  let hStokes : ∀ t : ℝ,
      ClosedLaplacianStokes (gt t) (fun y ↦ (gt t).scalarAt y) :=
    hFlux.closedLaplacianStokes
  let hHausdorffScalar : GlobalFiniteHausdorffChartScalarVariation gt :=
    hScalarDomination.toScalarVariation
      hFlow (by norm_num) hLichnerowicz hStokes
  exact
    hamiltonConvergencePinchedLimit3Core_of_differentialAbsoluteDissipationDecay_of_globalHausdorffJointMetricEntriesThree_of_compact_meanEnergy_parameterization
      hFlow hHausdorffScalar hJoint hStokes D' hrate
      hDissipationDeriv hDifferentialInequality metric parameter hRealize
      hInvariantContinuous hc hScalarLower

/-- Orbit-closure version of the fully assembled endpoint.  This is the
direct interface for a Hamilton compactness theorem: it may install any
topology on smooth metrics for which the flow-orbit closure is compact and
the two consumed scalar invariants are continuous. -/
theorem hamiltonConvergencePinchedLimit3Core_of_differentialDissipationDecay_of_globalHausdorffDominationJointMetricEntriesCompactFlux_of_compact_metricOrbitClosure
    [Nonempty M] [SimplyConnectedSpace M]
    [TopologicalSpace (ClosedSmoothRiemannianMetric 3 M)]
    {gt : ℝ → ClosedSmoothRiemannianMetric 3 M}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hFlow : ∀ t : ℝ, ∀ x : M,
      IsClosedNormalizedRicciFlowSolutionAt gt t x)
    (hHausdorffVolume : GlobalFiniteHausdorffChartDensityVariation gt)
    (hScalarDomination :
      GlobalFiniteHausdorffChartScalarDomination hHausdorffVolume)
    (hJoint : ∀ t : ℝ, ∀ y : M,
      MetricEntriesJointContDiffAt gt t y 3)
    (hFlux : GlobalFiniteHausdorffChartLaplacianFlux
      hHausdorffVolume (fun t y ↦ (gt t).scalarAt y))
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
  let hLichnerowicz : GlobalLichnerowiczAssemblyRegularity gt :=
    globalLichnerowiczAssemblyRegularity_of_jointMetricEntriesThree hJoint
  let hStokes : ∀ t : ℝ,
      ClosedLaplacianStokes (gt t) (fun y ↦ (gt t).scalarAt y) :=
    hFlux.closedLaplacianStokes
  let hHausdorffScalar : GlobalFiniteHausdorffChartScalarVariation gt :=
    hScalarDomination.toScalarVariation
      hFlow (by norm_num) hLichnerowicz hStokes
  exact
    hamiltonConvergencePinchedLimit3Core_of_normalizedFlow_finiteAbsoluteDissipation_of_compact_metricOrbitClosure
      gt hFlow
      (hHausdorffScalar.hasDerivAt_totalScalar_energyNumerator_of_globalLichnerowiczRegularity
        hFlow hLichnerowicz hStokes)
      (hHausdorffScalar.hasDerivAt_totalVolume_of_normalizedFlow hFlow)
      (normalizedMeanScalarAbsoluteVarianceDissipation_integrableOn_of_differential_decay
        gt D' hrate hDissipationDeriv hDifferentialInequality)
      hOrbitCompact hInvariantContinuous hc hScalarLower

end Poincare
