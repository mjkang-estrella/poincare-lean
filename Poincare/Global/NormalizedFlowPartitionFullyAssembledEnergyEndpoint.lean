import Poincare.Global.NormalizedFlowHausdorffPartitionStokes
import Poincare.Global.NormalizedFlowDissipationDifferentialDecay

/-!
# Fully assembled normalized-flow endpoint from subordinate coordinate Stokes

This module is the partition-of-unity counterpart of
`NormalizedFlowFullyAssembledEnergyEndpoint`.  It composes the strongest
concrete normalized-flow reductions while replacing the older
`GlobalFiniteHausdorffChartLaplacianFlux` input by
`GlobalFiniteSubordinateHausdorffLaplacianGeometry`.

The subordinate geometry proves Stokes by localizing the scalar, cancelling
the compact coordinate divergences, and only then reassembling the finite
partition sum.  No `ClosedLaplacianStokes`, Lichnerowicz package, moving
integral derivative, or finite-dissipation conclusion is assumed here.
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

/-- Fully assembled positive-mean-limit endpoint using the corrected finite
subordinate-partition coordinate proof of Stokes.

Joint `C³` metric entries construct Lichnerowicz regularity; Hausdorff scalar
domination constructs the moving scalar variation; the differential
inequality proves finite absolute dissipation; compact mean/energy
parameterization supplies invariant compactness; and positivity of the actual
limiting mean scalar selects the positive Einstein limit. -/
theorem hamiltonConvergencePinchedLimit3Core_of_differentialDissipationDecay_of_globalHausdorffDominationJointMetricEntriesSubordinatePartition_of_compact_meanEnergy_parameterization_of_meanLimitPos
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
    (hPartitionGeometry :
      GlobalFiniteSubordinateHausdorffLaplacianGeometry
        gt (fun t y ↦ (gt t).scalarAt y))
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
    hPartitionGeometry.closedLaplacianStokes
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

end Poincare
