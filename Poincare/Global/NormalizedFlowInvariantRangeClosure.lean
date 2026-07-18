import Poincare.Global.NormalizedFlowInvariantCompactness

/-!
# Closed invariant-range realization for normalized Ricci flow

The normalized-flow energy argument does not intrinsically need a topology on
the space of smooth metrics.  Once finite absolute dissipation produces a
sequence whose mean scalar and traceless-Ricci energy converge to `(R∞, 0)`,
it is enough that the *actual range* of this two-dimensional invariant along
the flow is closed.  The limiting pair is then attained by one of the flow
metrics itself.

This is the smallest realization hypothesis in the existing energy route.  A
compact invariant range is included as an immediate sufficient condition.
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

/-- Closedness of the two scalar invariants actually attained along the flow
is enough to realize the zero-traceless-Ricci-energy limit by a smooth metric.
No topology on the type of smooth metrics is used. -/
theorem hamiltonConvergencePinchedLimit3Core_of_normalizedFlow_finiteAbsoluteDissipation_of_closed_meanEnergy_orbitRange_of_meanLimitPos
    [Nonempty M] [SimplyConnectedSpace M]
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
    (hRangeClosed : IsClosed
      (Set.range (fun t ↦ closedMetricMeanTracelessEnergyPair (gt t))))
    (hMeanLimitPos : 0 < normalizedMeanScalarLimit gt) :
    HamiltonConvergencePinchedLimit3Core M := by
  obtain ⟨sample, _hsample, _hDerivative, _hVariance, hEnergy, hMean⟩ :=
    exists_normalizedFlow_energy_tendsto_zero_and_mean_tendsto_limit_of_finite_absoluteDissipation
      gt hFlow hDifferentiateMovingTotalScalar hDifferentiateMovingVolume
        hFiniteDissipation
  have hPair :
      Tendsto
        (fun i ↦ closedMetricMeanTracelessEnergyPair (gt (sample i)))
        atTop (nhds (normalizedMeanScalarLimit gt, 0)) :=
    hMean.prodMk_nhds hEnergy
  have hLimitMem :
      (normalizedMeanScalarLimit gt, 0) ∈
        Set.range (fun t ↦ closedMetricMeanTracelessEnergyPair (gt t)) := by
    apply hRangeClosed.mem_of_tendsto hPair
    exact Eventually.of_forall fun i ↦ ⟨sample i, rfl⟩
  obtain ⟨tLimit, hLimit⟩ := hLimitMem
  have hMeanLimit :
      meanScalar (gt tLimit) = normalizedMeanScalarLimit gt :=
    congrArg Prod.fst hLimit
  have hEnergyLimit :
      (∫ x, (gt tLimit).tracelessRicciNormSqAt x
        ∂(volumeMeasure (gt tLimit))) = 0 :=
    congrArg Prod.snd hLimit
  exact hamiltonConvergencePinchedLimit3Core_of_zero_tracelessRicci_energy_auto
    (gt tLimit) hEnergyLimit <| by
      rw [hMeanLimit]
      exact hMeanLimitPos

/-- A compact two-dimensional invariant range is, in particular, closed, so
it supplies the realization required by the normalized-flow energy endpoint. -/
theorem hamiltonConvergencePinchedLimit3Core_of_normalizedFlow_finiteAbsoluteDissipation_of_compact_meanEnergy_orbitRange_of_meanLimitPos
    [Nonempty M] [SimplyConnectedSpace M]
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
    (hRangeCompact : IsCompact
      (Set.range (fun t ↦ closedMetricMeanTracelessEnergyPair (gt t))))
    (hMeanLimitPos : 0 < normalizedMeanScalarLimit gt) :
    HamiltonConvergencePinchedLimit3Core M :=
  hamiltonConvergencePinchedLimit3Core_of_normalizedFlow_finiteAbsoluteDissipation_of_closed_meanEnergy_orbitRange_of_meanLimitPos
    gt hFlow hDifferentiateMovingTotalScalar hDifferentiateMovingVolume
      hFiniteDissipation hRangeCompact.isClosed hMeanLimitPos

/-- A uniform positive scalar lower bound supplies positivity of the limiting
mean in the closed invariant-range endpoint. -/
theorem hamiltonConvergencePinchedLimit3Core_of_normalizedFlow_finiteAbsoluteDissipation_of_closed_meanEnergy_orbitRange
    [Nonempty M] [SimplyConnectedSpace M]
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
    (hRangeClosed : IsClosed
      (Set.range (fun t ↦ closedMetricMeanTracelessEnergyPair (gt t))))
    {c : ℝ} (hc : 0 < c)
    (hScalarLower : ∀ t : ℝ, ∀ x : M, c ≤ (gt t).scalarAt x) :
    HamiltonConvergencePinchedLimit3Core M := by
  have hMeanTendsto :=
    tendsto_meanScalar_normalizedMeanScalarLimit_of_normalizedFlow_finiteAbsoluteDissipation
      gt hFlow hDifferentiateMovingTotalScalar hDifferentiateMovingVolume
        hFiniteDissipation
  have hMeanLimitLower : c ≤ normalizedMeanScalarLimit gt :=
    ge_of_tendsto hMeanTendsto <| Eventually.of_forall fun t ↦
      le_meanScalar_of_forall_le_scalarAt (gt t) c (hScalarLower t)
  exact
    hamiltonConvergencePinchedLimit3Core_of_normalizedFlow_finiteAbsoluteDissipation_of_closed_meanEnergy_orbitRange_of_meanLimitPos
      gt hFlow hDifferentiateMovingTotalScalar hDifferentiateMovingVolume
        hFiniteDissipation hRangeClosed (hc.trans_le hMeanLimitLower)

/-- Actual Hausdorff moving integrals and joint `C³` metric entries discharge
the differentiation hypotheses.  The only compactness-style input left is
closedness of the two-dimensional invariant range attained by the flow. -/
theorem hamiltonConvergencePinchedLimit3Core_of_finiteAbsoluteDissipation_of_globalHausdorffJointMetricEntriesThree_of_closed_meanEnergy_orbitRange
    [Nonempty M] [SimplyConnectedSpace M]
    {gt : ℝ → ClosedSmoothRiemannianMetric 3 M}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hFlow : ∀ t : ℝ, ∀ x : M,
      IsClosedNormalizedRicciFlowSolutionAt gt t x)
    (hHausdorff : GlobalFiniteHausdorffChartScalarVariation gt)
    (hJoint : ∀ t : ℝ, ∀ y : M,
      MetricEntriesJointContDiffAt gt t y 3)
    (hStokes : ∀ t : ℝ,
      ClosedLaplacianStokes (gt t) (fun y ↦ (gt t).scalarAt y))
    (hFiniteDissipation :
      IntegrableOn (normalizedMeanScalarAbsoluteVarianceDissipation gt) (Ici 0))
    (hRangeClosed : IsClosed
      (Set.range (fun t ↦ closedMetricMeanTracelessEnergyPair (gt t))))
    {c : ℝ} (hc : 0 < c)
    (hScalarLower : ∀ t : ℝ, ∀ x : M, c ≤ (gt t).scalarAt x) :
    HamiltonConvergencePinchedLimit3Core M := by
  let hLichnerowicz :=
    globalLichnerowiczAssemblyRegularity_of_jointMetricEntriesThree hJoint
  exact
    hamiltonConvergencePinchedLimit3Core_of_normalizedFlow_finiteAbsoluteDissipation_of_closed_meanEnergy_orbitRange
      gt hFlow
      (hHausdorff.hasDerivAt_totalScalar_energyNumerator_of_globalLichnerowiczRegularity
        hFlow hLichnerowicz hStokes)
      (hHausdorff.hasDerivAt_totalVolume_of_normalizedFlow hFlow)
      hFiniteDissipation hRangeClosed hc hScalarLower

/-- Exponential decay of the absolute normalized scalar variance supplies the
finite-dissipation premise in the closed-invariant-range endpoint. -/
theorem hamiltonConvergencePinchedLimit3Core_of_exponentialAbsoluteDissipation_of_globalHausdorffJointMetricEntriesThree_of_closed_meanEnergy_orbitRange
    [Nonempty M] [SimplyConnectedSpace M]
    {gt : ℝ → ClosedSmoothRiemannianMetric 3 M}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hFlow : ∀ t : ℝ, ∀ x : M,
      IsClosedNormalizedRicciFlowSolutionAt gt t x)
    (hHausdorff : GlobalFiniteHausdorffChartScalarVariation gt)
    (hJoint : ∀ t : ℝ, ∀ y : M,
      MetricEntriesJointContDiffAt gt t y 3)
    (hStokes : ∀ t : ℝ,
      ClosedLaplacianStokes (gt t) (fun y ↦ (gt t).scalarAt y))
    (hDissipationMeasurable : AEStronglyMeasurable
      (normalizedMeanScalarAbsoluteVarianceDissipation gt)
      (MeasureTheory.volume.restrict (Ici 0)))
    {C rate c : ℝ} (hrate : 0 < rate) (hc : 0 < c)
    (hDecay : ∀ t ∈ Ici (0 : ℝ),
      normalizedMeanScalarAbsoluteVarianceDissipation gt t ≤
        C * Real.exp ((-rate) * t))
    (hRangeClosed : IsClosed
      (Set.range (fun t ↦ closedMetricMeanTracelessEnergyPair (gt t))))
    (hScalarLower : ∀ t : ℝ, ∀ x : M, c ≤ (gt t).scalarAt x) :
    HamiltonConvergencePinchedLimit3Core M := by
  apply
    hamiltonConvergencePinchedLimit3Core_of_finiteAbsoluteDissipation_of_globalHausdorffJointMetricEntriesThree_of_closed_meanEnergy_orbitRange
      hFlow hHausdorff hJoint hStokes
        (normalizedMeanScalarAbsoluteVarianceDissipation_integrableOn_of_exponential_bound
          gt hDissipationMeasurable hrate hDecay)
        hRangeClosed hc hScalarLower

end Poincare
