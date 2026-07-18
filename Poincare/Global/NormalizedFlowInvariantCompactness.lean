import Poincare.Global.NormalizedFlowHausdorffSpatialMixedRegularity

/-!
# Compact scalar-invariant parameterizations of normalized flows

Hamilton compactness is much stronger than what the energy endpoint consumes.
After finite absolute dissipation, only the pair

`(mean scalar, total traceless-Ricci energy)`

must be realized by a smooth metric.  This file proves that it is enough to
place the flow metrics in any compact parameter space on which those two
invariants vary continuously.  No topology or convergence structure is put
on the type of all smooth metrics.
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

/-- The finite-dimensional invariant map used by the normalized-flow energy
endpoint. -/
def closedMetricMeanTracelessEnergyPair
    (g : ClosedSmoothRiemannianMetric 3 M) : ℝ × ℝ :=
  (meanScalar g,
    ∫ x, g.tracelessRicciNormSqAt x ∂(volumeMeasure g))

/-- A compact parameter space containing the flow, together with continuity
of the two scalar invariants, realizes the zero-energy limit.  Positivity is
required only of the actual limiting mean scalar.

Only the invariant map must be continuous.  The metric-valued map itself has
no imposed topology. -/
theorem hamiltonConvergencePinchedLimit3Core_of_normalizedFlow_finiteAbsoluteDissipation_of_compact_meanEnergy_parameterization_of_meanLimitPos
    [Nonempty M] [SimplyConnectedSpace M]
    {K : Type v} [TopologicalSpace K] [CompactSpace K]
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
    (metric : K → ClosedSmoothRiemannianMetric 3 M)
    (parameter : ℝ → K)
    (hRealize : ∀ t : ℝ, metric (parameter t) = gt t)
    (hInvariantContinuous :
      Continuous (fun k ↦ closedMetricMeanTracelessEnergyPair (metric k)))
    (hMeanLimitPos : 0 < normalizedMeanScalarLimit gt) :
    HamiltonConvergencePinchedLimit3Core M := by
  obtain ⟨sample, hsample, _hDerivative, _hVariance, hEnergy, hMean⟩ :=
    exists_normalizedFlow_energy_tendsto_zero_and_mean_tendsto_limit_of_finite_absoluteDissipation
      gt hFlow hDifferentiateMovingTotalScalar hDifferentiateMovingVolume
        hFiniteDissipation
  have hPair :
      Tendsto
        (fun i ↦ closedMetricMeanTracelessEnergyPair (gt (sample i)))
        atTop (nhds (normalizedMeanScalarLimit gt, 0)) := by
    exact hMean.prodMk_nhds hEnergy
  have hRangeClosed : IsClosed
      (Set.range fun k ↦ closedMetricMeanTracelessEnergyPair (metric k)) :=
    (isCompact_range hInvariantContinuous).isClosed
  have hLimitMem :
      (normalizedMeanScalarLimit gt, 0) ∈
        Set.range (fun k ↦ closedMetricMeanTracelessEnergyPair (metric k)) := by
    apply hRangeClosed.mem_of_tendsto hPair
    exact Eventually.of_forall fun i ↦ by
      refine ⟨parameter (sample i), ?_⟩
      change
        closedMetricMeanTracelessEnergyPair (metric (parameter (sample i))) =
          closedMetricMeanTracelessEnergyPair (gt (sample i))
      rw [hRealize]
  obtain ⟨kLimit, hLimit⟩ := hLimitMem
  have hMeanLimit :
      meanScalar (metric kLimit) = normalizedMeanScalarLimit gt :=
    congrArg Prod.fst hLimit
  have hEnergyLimit :
      (∫ x, (metric kLimit).tracelessRicciNormSqAt x
        ∂(volumeMeasure (metric kLimit))) = 0 :=
    congrArg Prod.snd hLimit
  exact hamiltonConvergencePinchedLimit3Core_of_zero_tracelessRicci_energy_auto
    (metric kLimit) hEnergyLimit <| by
      rw [hMeanLimit]
      exact hMeanLimitPos

/-- A uniform positive scalar lower bound is one concrete source of positive
limiting mean scalar for the compact-parameterization endpoint. -/
theorem hamiltonConvergencePinchedLimit3Core_of_normalizedFlow_finiteAbsoluteDissipation_of_compact_meanEnergy_parameterization
    [Nonempty M] [SimplyConnectedSpace M]
    {K : Type v} [TopologicalSpace K] [CompactSpace K]
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
    (metric : K → ClosedSmoothRiemannianMetric 3 M)
    (parameter : ℝ → K)
    (hRealize : ∀ t : ℝ, metric (parameter t) = gt t)
    (hInvariantContinuous :
      Continuous (fun k ↦ closedMetricMeanTracelessEnergyPair (metric k)))
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
    hamiltonConvergencePinchedLimit3Core_of_normalizedFlow_finiteAbsoluteDissipation_of_compact_meanEnergy_parameterization_of_meanLimitPos
      gt hFlow hDifferentiateMovingTotalScalar hDifferentiateMovingVolume
      hFiniteDissipation metric parameter hRealize hInvariantContinuous
      (hc.trans_le hMeanLimitLower)

/-- Familiar orbit-closure formulation of the preceding compactness theorem.
If some topology on smooth metrics makes the closure of the normalized-flow
orbit compact and makes the two scalar invariants continuous on that closure,
then the zero-energy limit is realized.

No claim is made here that the ambient metric topology has already been
constructed; this theorem records exactly what a Hamilton compactness theorem
must supply to the energy endpoint. -/
theorem hamiltonConvergencePinchedLimit3Core_of_normalizedFlow_finiteAbsoluteDissipation_of_compact_metricOrbitClosure
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
    {c : ℝ} (hc : 0 < c)
    (hScalarLower : ∀ t : ℝ, ∀ x : M, c ≤ (gt t).scalarAt x) :
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
    hamiltonConvergencePinchedLimit3Core_of_normalizedFlow_finiteAbsoluteDissipation_of_compact_meanEnergy_parameterization
      gt hFlow hDifferentiateMovingTotalScalar hDifferentiateMovingVolume
      hFiniteDissipation metric parameter (fun _t ↦ rfl) hContinuousK
      hc hScalarLower

/-- Actual Hausdorff moving integrals and joint `C³` metric entries compose
with the compact invariant parameterization, leaving no Lichnerowicz package
and no metric-valued sequential compactness premise. -/
theorem hamiltonConvergencePinchedLimit3Core_of_finiteAbsoluteDissipation_of_globalHausdorffJointMetricEntriesThree_of_compact_meanEnergy_parameterization
    [Nonempty M] [SimplyConnectedSpace M]
    {K : Type v} [TopologicalSpace K] [CompactSpace K]
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
    (metric : K → ClosedSmoothRiemannianMetric 3 M)
    (parameter : ℝ → K)
    (hRealize : ∀ t : ℝ, metric (parameter t) = gt t)
    (hInvariantContinuous :
      Continuous (fun k ↦ closedMetricMeanTracelessEnergyPair (metric k)))
    {c : ℝ} (hc : 0 < c)
    (hScalarLower : ∀ t : ℝ, ∀ x : M, c ≤ (gt t).scalarAt x) :
    HamiltonConvergencePinchedLimit3Core M := by
  let hLichnerowicz :=
    globalLichnerowiczAssemblyRegularity_of_jointMetricEntriesThree hJoint
  exact
    hamiltonConvergencePinchedLimit3Core_of_normalizedFlow_finiteAbsoluteDissipation_of_compact_meanEnergy_parameterization
      gt hFlow
      (hHausdorff.hasDerivAt_totalScalar_energyNumerator_of_globalLichnerowiczRegularity
        hFlow hLichnerowicz hStokes)
      (hHausdorff.hasDerivAt_totalVolume_of_normalizedFlow hFlow)
      hFiniteDissipation metric parameter hRealize hInvariantContinuous
      hc hScalarLower

/-- Exponential dissipation decay discharges the finite-dissipation premise
in the fully assembled compact-parameterization endpoint. -/
theorem hamiltonConvergencePinchedLimit3Core_of_exponentialAbsoluteDissipation_of_globalHausdorffJointMetricEntriesThree_of_compact_meanEnergy_parameterization
    [Nonempty M] [SimplyConnectedSpace M]
    {K : Type v} [TopologicalSpace K] [CompactSpace K]
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
    (metric : K → ClosedSmoothRiemannianMetric 3 M)
    (parameter : ℝ → K)
    (hRealize : ∀ t : ℝ, metric (parameter t) = gt t)
    (hInvariantContinuous :
      Continuous (fun k ↦ closedMetricMeanTracelessEnergyPair (metric k)))
    (hScalarLower : ∀ t : ℝ, ∀ x : M, c ≤ (gt t).scalarAt x) :
    HamiltonConvergencePinchedLimit3Core M := by
  apply
    hamiltonConvergencePinchedLimit3Core_of_finiteAbsoluteDissipation_of_globalHausdorffJointMetricEntriesThree_of_compact_meanEnergy_parameterization
      hFlow hHausdorff hJoint hStokes
        (normalizedMeanScalarAbsoluteVarianceDissipation_integrableOn_of_exponential_bound
          gt hDissipationMeasurable hrate hDecay)
        metric parameter hRealize hInvariantContinuous hc hScalarLower

end Poincare
