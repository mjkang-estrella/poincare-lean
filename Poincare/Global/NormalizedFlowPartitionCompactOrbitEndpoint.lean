import Poincare.Global.NormalizedFlowPartitionFullyAssembledEnergyEndpoint

/-!
# Subordinate-partition normalized flow from compact metric-orbit closure

The proof-bearing subordinate-partition endpoint currently stores an
arbitrary compact parameter space `K`, a metric-valued realization map, a
parameter selecting every flow time, and equality of that realization with
the flow.  Hamilton compactness naturally supplies a more direct interface:
compactness of the closure of the actual metric orbit.

This module proves the missing positive-mean-limit orbit-closure bridge.  It
constructs the compact parameter space internally as
`closure (Set.range gt)`, then composes that bridge with the corrected
partition-of-unity Stokes endpoint.  Thus no external `K`, metric map,
parameter map, or realization equality remains in the assembled theorem.

No ambient topology on smooth metrics is constructed here.  The topology,
compactness of the orbit closure, and continuity of the two scalar invariants
are exactly the residual input expected from a normalized-flow compactness
theorem.
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

/-- Compactness of the actual metric-orbit closure is sufficient for the
positive-mean-limit normalized-flow endpoint.

The subtype of the orbit closure supplies the compact parameter space used by
the invariant compactness theorem.  Its inclusion is the metric realization,
and every `gt t` belongs to the subtype by `subset_closure`.
-/
theorem hamiltonConvergencePinchedLimit3Core_of_normalizedFlow_finiteAbsoluteDissipation_of_compact_metricOrbitClosure_of_meanLimitPos
    [Nonempty M] [SimplyConnectedSpace M]
    [TopologicalSpace (ClosedSmoothRiemannianMetric 3 M)]
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    (hFlow : ∀ t : ℝ, ∀ x : M,
      IsClosedNormalizedRicciFlowSolutionAt gt t x)
    (hDifferentiateMovingTotalScalar : ∀ t : ℝ,
      HasDerivAt (fun s ↦ totalScalar (gt s))
        (normalizedMeanScalarEnergyNumerator (gt t)) t)
    (hDifferentiateMovingVolume : ∀ t : ℝ,
      HasDerivAt (fun s ↦ totalVolume (gt s))
        (totalVolumeFirstVariation (gt t) (timeDerivAt gt t)) t)
    (hFiniteDissipation :
      IntegrableOn (normalizedMeanScalarAbsoluteVarianceDissipation gt) (Ici 0))
    (hOrbitCompact : IsCompact (closure (Set.range gt)))
    (hInvariantContinuous : ContinuousOn closedMetricMeanTracelessEnergyPair
      (closure (Set.range gt)))
    (hMeanLimitPos : 0 < normalizedMeanScalarLimit gt) :
    HamiltonConvergencePinchedLimit3Core M := by
  let K := closure (Set.range gt)
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hOrbitCompact
  let metric : K → ClosedSmoothRiemannianMetric 3 M := fun k ↦ k.1
  let parameter : ℝ → K := fun t ↦
    ⟨gt t, subset_closure ⟨t, rfl⟩⟩
  have hContinuousK : Continuous
      (fun k : K ↦ closedMetricMeanTracelessEnergyPair (metric k)) := by
    exact continuousOn_iff_continuous_restrict.mp hInvariantContinuous
  exact
    hamiltonConvergencePinchedLimit3Core_of_normalizedFlow_finiteAbsoluteDissipation_of_compact_meanEnergy_parameterization_of_meanLimitPos
      gt hFlow hDifferentiateMovingTotalScalar hDifferentiateMovingVolume
      hFiniteDissipation metric parameter (fun _t ↦ rfl) hContinuousK
      hMeanLimitPos

/-- Fully assembled subordinate-partition endpoint with the actual metric
orbit closure as its compactness input.

Compared with the compact-parameter formulation, this theorem eliminates the
external parameter type, its topology and compactness instance, the metric
realization map, the time-parameter map, and the realization equality.  The
remaining orbit-closure hypotheses are the direct normalized-flow
compactness boundary.
-/
theorem hamiltonConvergencePinchedLimit3Core_of_differentialDissipationDecay_of_globalHausdorffDominationJointMetricEntriesSubordinatePartition_of_compact_metricOrbitClosure_of_meanLimitPos
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
  let hLichnerowicz : GlobalLichnerowiczAssemblyRegularity gt :=
    globalLichnerowiczAssemblyRegularity_of_jointMetricEntriesThree hJoint
  let hStokes : ∀ t : ℝ,
      ClosedLaplacianStokes (gt t) (fun y ↦ (gt t).scalarAt y) :=
    hPartitionGeometry.closedLaplacianStokes
  let hHausdorffScalar : GlobalFiniteHausdorffChartScalarVariation gt :=
    hScalarDomination.toScalarVariation
      hFlow (by norm_num) hLichnerowicz hStokes
  exact
    hamiltonConvergencePinchedLimit3Core_of_normalizedFlow_finiteAbsoluteDissipation_of_compact_metricOrbitClosure_of_meanLimitPos
      gt hFlow
      (hHausdorffScalar.hasDerivAt_totalScalar_energyNumerator_of_globalLichnerowiczRegularity
        hFlow hLichnerowicz hStokes)
      (hHausdorffScalar.hasDerivAt_totalVolume_of_normalizedFlow hFlow)
      (normalizedMeanScalarAbsoluteVarianceDissipation_integrableOn_of_differential_decay
        gt D' hrate hDissipationDeriv hDifferentialInequality)
      hOrbitCompact hInvariantContinuous hMeanLimitPos

end Poincare
