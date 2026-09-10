import Poincare.Global.HamiltonChartDensityLocalDomination
import Poincare.Global.HamiltonMeanFloorReduction
import Poincare.Global.NormalizedFlowHausdorffScalarTimeDerivativeAutomatic
import Poincare.Global.NormalizedFlowHausdorffScalarDominationJointC1Reduction
import Poincare.Global.NormalizedFlowForwardFiniteTimePositiveEinsteinMeanScalarEnergyDomination

/-!
# Mean scalar floor from energy domination

Moving integral differentiation follows from joint C³ metric entries and
explicit closed Laplacian Stokes. The integrated energy inequality then
makes the forward mean scalar nondecreasing. Core existence, Stokes, and
the energy inequality remain explicit inputs.
-/

set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology
universe u v
namespace Poincare.HamiltonMeanFloorFromEnergyDomination
variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (ClosedSmoothModel 3) M]
  [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
  [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M]

/-- The moving volume and total-scalar identities, retaining Stokes explicitly. -/
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

end Poincare.HamiltonMeanFloorFromEnergyDomination
