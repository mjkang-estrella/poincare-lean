import Poincare.Global.NormalizedFlowChartFramePartitionCompactOrbitEndpoint
import Poincare.Global.NormalizedFlowForwardAbsoluteDissipation
import Poincare.Global.NormalizedFlowAbsoluteDissipationDecay
import Poincare.Global.HausdorffScalarVarianceContinuity
import Mathlib.Topology.Sequences

/-!
# Forward chart-frame partition compact-orbit endpoint

This module propagates the `Ici 0` normalized-flow interface through the
strongest corrected chart-frame, subordinate-partition, compact-orbit
Hamilton endpoint.

The global chart-frame density and scalar-domination packages still describe
the all-real metric path because dominated differentiation uses a genuine
two-sided time germ.  The normalized-flow equation itself is consumed only
at the differentiated time.  We therefore reconstruct the scalar-density
differentiation and moving total-scalar/volume derivatives separately at
each nonnegative time, with no all-real `hFlow` premise.

At the compactness endpoint, finite absolute dissipation supplies a sequence
of nonnegative times with traceless-Ricci energy tending to zero.  Compactness
of the invariant-pair image supplies a convergent subsequence.  Its energy
coordinate is zero, while a scalar lower bound assumed only on `Ici 0`
makes its mean coordinate positive.  This realizes the reduced Hamilton core
without using the older all-real mean-limit route.
-/

noncomputable section

open Bundle FiberBundle Filter MeasureTheory Set
open scoped Manifold ContDiff MeasureTheory Topology ENNReal NNReal

universe u

namespace Poincare

set_option linter.unusedSectionVars false

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
variable [CompactSpace M] [ConnectedSpace M]
variable [MeasurableSpace M] [BorelSpace M]
variable [ChartedSpace (ClosedSmoothModel 3) M]
variable [IsManifold (closedSmoothModelWithCorners 3) ∞ M]

local notation "I" => closedSmoothModelWithCorners 3

/-- Localized form of the raw moving-total-scalar integrability bridge.
Only the normalized-flow equation and Stokes theorem at the selected time
are used. -/
theorem rawTotalScalarFirstVariation_integrand_integrable_of_normalizedFlowAt_of_lichnerowicz_of_stokes
    [Nonempty M]
    {gt : ℝ → ClosedSmoothRiemannianMetric 3 M}
    [∀ s : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt s).leviCivita 1]
    (L : GlobalLichnerowiczAssemblyRegularity gt) (t : ℝ)
    (hFlow : ∀ x : M, IsClosedNormalizedRicciFlowSolutionAt gt t x)
    (hStokes : ClosedLaplacianStokes (gt t)
      (fun y ↦ (gt t).scalarAt y)) :
    Integrable
      (fun x : M ↦
        deriv (fun s ↦ (gt s).scalarAt x) t +
          (1 / 2 : ℝ) * (gt t).scalarAt x *
            traceMetricVariationAt (gt t) (timeDerivAt gt t) x)
      (volumeMeasure (gt t)) := by
  have hScalar₂ : ∀ y : M,
      ContMDiffAt I 𝓘(ℝ) 2 (fun z : M ↦ (gt t).scalarAt z) y :=
    scalarAt_contMDiffAt_two_of_normalizedRicciFlow
      hFlow (L.timeVariationEntries t)
  have hClosed :=
    closedTotalScalarFirstVariation_integrand_integrable hFlow (by norm_num)
  have hSum := hStokes.1.add hClosed
  apply hSum.congr
  exact Eventually.of_forall fun x ↦ by
    change
      (gt t).laplacianAt (fun y ↦ (gt t).scalarAt y) x +
          ((1 / 2 : ℝ) * (gt t).scalarAt x *
              traceMetricVariationAt (gt t) (timeDerivAt gt t) x -
            metricVariationRicciPairingAt (gt t) (timeDerivAt gt t) x) =
        deriv (fun s ↦ (gt s).scalarAt x) t +
          (1 / 2 : ℝ) * (gt t).scalarAt x *
            traceMetricVariationAt (gt t) (timeDerivAt gt t) x
    rw [L.scalarVariation_stokes t x,
      scalarVariationStokesBoundaryAt_eq_laplacian_scalarAt_of_normalizedFlow
        hFlow (by norm_num) hScalar₂]
    ring

/-- Corrected chart-frame scalar domination gives the normalized moving
total-scalar derivative at one time, using normalized flow only at that
time. -/
theorem GlobalFiniteHausdorffChartFrameScalarDomination.hasDerivAt_totalScalar_energyNumerator_of_normalizedFlowAt
    [Nonempty M]
    {gt : ℝ → ClosedSmoothRiemannianMetric 3 M}
    [∀ s : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt s).leviCivita 1]
    {V : GlobalFiniteHausdorffChartFrameDensityVariation gt}
    (B : GlobalFiniteHausdorffChartFrameScalarDomination V)
    (L : GlobalLichnerowiczAssemblyRegularity gt) (t : ℝ)
    (hFlow : ∀ x : M, IsClosedNormalizedRicciFlowSolutionAt gt t x)
    (hStokes : ClosedLaplacianStokes (gt t)
      (fun y ↦ (gt t).scalarAt y)) :
    HasDerivAt (fun s ↦ totalScalar (gt s))
      (normalizedMeanScalarEnergyNumerator (gt t)) t := by
  let scalarDifferentiation :
      FiniteChartScalarDensityDominatedDifferentiationAt
        (V.decomposition t) (V.differentiation t) :=
    (B.scalarDomination t).toDominatedDifferentiation
      (fun _i _z s _hs ↦ L.hasDerivAt_scalar_deriv s _)
      (rawTotalScalarFirstVariation_integrand_integrable_of_normalizedFlowAt_of_lichnerowicz_of_stokes
        L t hFlow hStokes)
  exact hasDerivAt_totalScalar_energyNumerator_of_intrinsicChartDensity
    (V.decomposition t) (V.differentiation t) scalarDifferentiation
    (V.intrinsicDensityFirstVariation t) hFlow (by norm_num)
    (fun x ↦ scalarAt_contMDiffAt_two_of_normalizedRicciFlow
      hFlow (L.timeVariationEntries t) x)
    (fun x ↦ L.scalarVariation_stokes t x) hStokes

/-- Corrected chart-frame density variation gives the moving-volume
derivative at one normalized-flow time. -/
theorem GlobalFiniteHausdorffChartFrameDensityVariation.hasDerivAt_totalVolume_of_normalizedFlowAt
    [Nonempty M]
    {gt : ℝ → ClosedSmoothRiemannianMetric 3 M}
    (V : GlobalFiniteHausdorffChartFrameDensityVariation gt) (t : ℝ)
    (hFlow : ∀ x : M, IsClosedNormalizedRicciFlowSolutionAt gt t x) :
    HasDerivAt (fun s ↦ totalVolume (gt s))
      (totalVolumeFirstVariation (gt t) (timeDerivAt gt t)) t :=
  V.hasDerivAt_totalVolume t
    (integrable_traceMetricVariationAt_timeDeriv_of_closedNormalizedRicciFlow
      hFlow (by norm_num))

/-- Forward finite-dissipation Hamilton endpoint from compactness of the
actual metric-orbit closure.

The compactness assumptions are exactly the existing orbit-closure boundary.
Flow, both moving-integral derivatives, and the scalar floor are required
only on `Ici 0`. -/
theorem hamiltonConvergencePinchedLimit3Core_of_normalizedFlow_finiteAbsoluteDissipation_Ici_of_compact_metricOrbitClosure_of_scalarLower
    [Nonempty M] [SimplyConnectedSpace M]
    [TopologicalSpace (ClosedSmoothRiemannianMetric 3 M)]
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    (hFlow : ∀ t ∈ Ici (0 : ℝ), ∀ x : M,
      IsClosedNormalizedRicciFlowSolutionAt gt t x)
    (hDifferentiateMovingTotalScalar : ∀ t ∈ Ici (0 : ℝ),
      HasDerivAt (fun s ↦ totalScalar (gt s))
        (normalizedMeanScalarEnergyNumerator (gt t)) t)
    (hDifferentiateMovingVolume : ∀ t ∈ Ici (0 : ℝ),
      HasDerivAt (fun s ↦ totalVolume (gt s))
        (totalVolumeFirstVariation (gt t) (timeDerivAt gt t)) t)
    (hFiniteDissipation :
      IntegrableOn (normalizedMeanScalarAbsoluteVarianceDissipation gt) (Ici 0))
    (hOrbitCompact : IsCompact (closure (Set.range gt)))
    (hInvariantContinuous : ContinuousOn closedMetricMeanTracelessEnergyPair
      (closure (Set.range gt)))
    {c : ℝ} (hc : 0 < c)
    (hScalarLower : ∀ t ∈ Ici (0 : ℝ), ∀ x : M,
      c ≤ (gt t).scalarAt x) :
    HamiltonConvergencePinchedLimit3Core M := by
  obtain ⟨sample, hsampleNonneg, hsampleAtTop, _hDerivativeZero,
      _hVarianceZero, hEnergyZero⟩ :=
    exists_normalizedFlow_energy_tendsto_zero_of_finite_absoluteDissipation_Ici
      gt hFlow hDifferentiateMovingTotalScalar hDifferentiateMovingVolume
        hFiniteDissipation
  let pairSequence : ℕ → ℝ × ℝ := fun i ↦
    closedMetricMeanTracelessEnergyPair (gt (sample i))
  have hPairCompact : IsCompact
      (closedMetricMeanTracelessEnergyPair '' closure (Set.range gt)) :=
    hOrbitCompact.image_of_continuousOn hInvariantContinuous
  have hPairMem : ∀ i : ℕ,
      pairSequence i ∈
        closedMetricMeanTracelessEnergyPair '' closure (Set.range gt) := by
    intro i
    exact ⟨gt (sample i), subset_closure ⟨sample i, rfl⟩, rfl⟩
  obtain ⟨pairLimit, hPairLimitMem, φ, hφ, hPairLimit⟩ :=
    hPairCompact.tendsto_subseq hPairMem
  have hEnergySubsequence :
      Tendsto
        (fun i ↦ ∫ x, (gt (sample (φ i))).tracelessRicciNormSqAt x
          ∂(volumeMeasure (gt (sample (φ i))))) atTop (nhds 0) :=
    hEnergyZero.comp hφ.tendsto_atTop
  have hPairSecond :
      Tendsto (fun i ↦ (pairSequence (φ i)).2) atTop
        (nhds pairLimit.2) :=
    (continuous_snd.tendsto pairLimit).comp hPairLimit
  have hPairSecondZero : pairLimit.2 = 0 := by
    apply tendsto_nhds_unique hPairSecond
    simpa [pairSequence, closedMetricMeanTracelessEnergyPair] using
      hEnergySubsequence
  have hPairFirst :
      Tendsto (fun i ↦ meanScalar (gt (sample (φ i)))) atTop
        (nhds pairLimit.1) := by
    simpa [pairSequence, closedMetricMeanTracelessEnergyPair] using
      (continuous_fst.tendsto pairLimit).comp hPairLimit
  have hPairFirstLower : c ≤ pairLimit.1 :=
    ge_of_tendsto hPairFirst <|
      Eventually.of_forall fun i ↦
        le_meanScalar_of_forall_le_scalarAt (gt (sample (φ i))) c
          (hScalarLower (sample (φ i)) (hsampleNonneg (φ i)))
  obtain ⟨gLimit, _hgLimitClosure, hPairEq⟩ := hPairLimitMem
  have hLimitEnergy :
      (∫ x, gLimit.tracelessRicciNormSqAt x
        ∂(volumeMeasure gLimit)) = 0 := by
    calc
      (∫ x, gLimit.tracelessRicciNormSqAt x
          ∂(volumeMeasure gLimit)) =
          (closedMetricMeanTracelessEnergyPair gLimit).2 := rfl
      _ = pairLimit.2 := congrArg Prod.snd hPairEq
      _ = 0 := hPairSecondZero
  have hLimitMeanLower : c ≤ meanScalar gLimit := by
    calc
      c ≤ pairLimit.1 := hPairFirstLower
      _ = (closedMetricMeanTracelessEnergyPair gLimit).1 :=
        (congrArg Prod.fst hPairEq).symm
      _ = meanScalar gLimit := rfl
  exact hamiltonConvergencePinchedLimit3Core_of_zero_tracelessRicci_energy_auto
    gLimit hLimitEnergy (hc.trans_le hLimitMeanLower)

/-- Sequential compactness is sufficient for the forward finite-dissipation
endpoint.  This is a genuinely sequential realization theorem: it assumes
`IsSeqCompact` of the metric-orbit closure and only `SeqContinuous` of the
consumed invariant pair, with no compactness or ambient first-countability
assumption on the type of smooth metrics. -/
theorem hamiltonConvergencePinchedLimit3Core_of_normalizedFlow_finiteAbsoluteDissipation_Ici_of_seqCompact_metricOrbitClosure_of_scalarLower
    [Nonempty M] [SimplyConnectedSpace M]
    [TopologicalSpace (ClosedSmoothRiemannianMetric 3 M)]
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    (hFlow : ∀ t ∈ Ici (0 : ℝ), ∀ x : M,
      IsClosedNormalizedRicciFlowSolutionAt gt t x)
    (hDifferentiateMovingTotalScalar : ∀ t ∈ Ici (0 : ℝ),
      HasDerivAt (fun s ↦ totalScalar (gt s))
        (normalizedMeanScalarEnergyNumerator (gt t)) t)
    (hDifferentiateMovingVolume : ∀ t ∈ Ici (0 : ℝ),
      HasDerivAt (fun s ↦ totalVolume (gt s))
        (totalVolumeFirstVariation (gt t) (timeDerivAt gt t)) t)
    (hFiniteDissipation :
      IntegrableOn (normalizedMeanScalarAbsoluteVarianceDissipation gt) (Ici 0))
    (hOrbitSeqCompact : IsSeqCompact (closure (Set.range gt)))
    (hInvariantSeqContinuous :
      SeqContinuous (closedMetricMeanTracelessEnergyPair (M := M)))
    {c : ℝ} (hc : 0 < c)
    (hScalarLower : ∀ t ∈ Ici (0 : ℝ), ∀ x : M,
      c ≤ (gt t).scalarAt x) :
    HamiltonConvergencePinchedLimit3Core M := by
  obtain ⟨sample, hsampleNonneg, _hsampleAtTop, _hDerivativeZero,
      _hVarianceZero, hEnergyZero⟩ :=
    exists_normalizedFlow_energy_tendsto_zero_of_finite_absoluteDissipation_Ici
      gt hFlow hDifferentiateMovingTotalScalar hDifferentiateMovingVolume
        hFiniteDissipation
  let metricSequence : ℕ → ClosedSmoothRiemannianMetric 3 M :=
    fun i ↦ gt (sample i)
  have hMetricSequenceMem : ∀ i : ℕ,
      metricSequence i ∈ closure (Set.range gt) := by
    intro i
    exact subset_closure ⟨sample i, rfl⟩
  obtain ⟨gLimit, _hgLimitClosure, φ, hφ, hMetricLimit⟩ :=
    hOrbitSeqCompact hMetricSequenceMem
  have hPairLimit :
      Tendsto
        (fun i ↦ closedMetricMeanTracelessEnergyPair
          (gt (sample (φ i))))
        atTop (nhds (closedMetricMeanTracelessEnergyPair gLimit)) := by
    simpa only [metricSequence, Function.comp_apply] using
      hInvariantSeqContinuous hMetricLimit
  have hEnergySubsequence :
      Tendsto
        (fun i ↦ ∫ x, (gt (sample (φ i))).tracelessRicciNormSqAt x
          ∂(volumeMeasure (gt (sample (φ i))))) atTop (nhds 0) :=
    hEnergyZero.comp hφ.tendsto_atTop
  have hEnergyAtLimit :
      Tendsto
        (fun i ↦ ∫ x, (gt (sample (φ i))).tracelessRicciNormSqAt x
          ∂(volumeMeasure (gt (sample (φ i))))) atTop
        (nhds
          (∫ x, gLimit.tracelessRicciNormSqAt x
            ∂(volumeMeasure gLimit))) := by
    simpa only [closedMetricMeanTracelessEnergyPair] using
      (continuous_snd.tendsto
        (closedMetricMeanTracelessEnergyPair gLimit)).comp hPairLimit
  have hLimitEnergy :
      (∫ x, gLimit.tracelessRicciNormSqAt x
        ∂(volumeMeasure gLimit)) = 0 := by
    exact tendsto_nhds_unique hEnergyAtLimit hEnergySubsequence
  have hMeanAtLimit :
      Tendsto (fun i ↦ meanScalar (gt (sample (φ i)))) atTop
        (nhds (meanScalar gLimit)) := by
    simpa only [closedMetricMeanTracelessEnergyPair] using
      (continuous_fst.tendsto
        (closedMetricMeanTracelessEnergyPair gLimit)).comp hPairLimit
  have hLimitMeanLower : c ≤ meanScalar gLimit :=
    ge_of_tendsto hMeanAtLimit <|
      Eventually.of_forall fun i ↦
        le_meanScalar_of_forall_le_scalarAt (gt (sample (φ i))) c
          (hScalarLower (sample (φ i)) (hsampleNonneg (φ i)))
  exact hamiltonConvergencePinchedLimit3Core_of_zero_tracelessRicci_energy_auto
    gLimit hLimitEnergy (hc.trans_le hLimitMeanLower)

/-- Forward corrected chart-frame endpoint with finite absolute dissipation
and compactness of the actual metric-orbit closure. -/
theorem hamiltonConvergencePinchedLimit3Core_of_finiteAbsoluteDissipation_of_globalHausdorffChartFrameScalarDomination_Ici_of_globalLichnerowiczRegularity_of_compact_metricOrbitClosure_of_scalarLower
    [Nonempty M] [SimplyConnectedSpace M]
    [TopologicalSpace (ClosedSmoothRiemannianMetric 3 M)]
    {gt : ℝ → ClosedSmoothRiemannianMetric 3 M}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hFlow : ∀ t ∈ Ici (0 : ℝ), ∀ x : M,
      IsClosedNormalizedRicciFlowSolutionAt gt t x)
    (hHausdorffVolume : GlobalFiniteHausdorffChartFrameDensityVariation gt)
    (hScalarDomination :
      GlobalFiniteHausdorffChartFrameScalarDomination hHausdorffVolume)
    (hLichnerowicz : GlobalLichnerowiczAssemblyRegularity gt)
    (hStokes : ∀ t ∈ Ici (0 : ℝ),
      ClosedLaplacianStokes (gt t) (fun y ↦ (gt t).scalarAt y))
    (hFiniteDissipation :
      IntegrableOn (normalizedMeanScalarAbsoluteVarianceDissipation gt) (Ici 0))
    (hOrbitCompact : IsCompact (closure (Set.range gt)))
    (hInvariantContinuous : ContinuousOn closedMetricMeanTracelessEnergyPair
      (closure (Set.range gt)))
    {c : ℝ} (hc : 0 < c)
    (hScalarLower : ∀ t ∈ Ici (0 : ℝ), ∀ x : M,
      c ≤ (gt t).scalarAt x) :
    HamiltonConvergencePinchedLimit3Core M := by
  apply
    hamiltonConvergencePinchedLimit3Core_of_normalizedFlow_finiteAbsoluteDissipation_Ici_of_compact_metricOrbitClosure_of_scalarLower
      gt hFlow
  · intro t ht
    exact hScalarDomination.hasDerivAt_totalScalar_energyNumerator_of_normalizedFlowAt
      hLichnerowicz t (hFlow t ht) (hStokes t ht)
  · intro t ht
    exact hHausdorffVolume.hasDerivAt_totalVolume_of_normalizedFlowAt
      t (hFlow t ht)
  · exact hFiniteDissipation
  · exact hOrbitCompact
  · exact hInvariantContinuous
  · exact hc
  · exact hScalarLower

/-- Forward corrected chart-frame endpoint with finite absolute dissipation
and sequentially compact realization of the metric-orbit closure. -/
theorem hamiltonConvergencePinchedLimit3Core_of_finiteAbsoluteDissipation_of_globalHausdorffChartFrameScalarDomination_Ici_of_globalLichnerowiczRegularity_of_seqCompact_metricOrbitClosure_of_scalarLower
    [Nonempty M] [SimplyConnectedSpace M]
    [TopologicalSpace (ClosedSmoothRiemannianMetric 3 M)]
    {gt : ℝ → ClosedSmoothRiemannianMetric 3 M}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hFlow : ∀ t ∈ Ici (0 : ℝ), ∀ x : M,
      IsClosedNormalizedRicciFlowSolutionAt gt t x)
    (hHausdorffVolume : GlobalFiniteHausdorffChartFrameDensityVariation gt)
    (hScalarDomination :
      GlobalFiniteHausdorffChartFrameScalarDomination hHausdorffVolume)
    (hLichnerowicz : GlobalLichnerowiczAssemblyRegularity gt)
    (hStokes : ∀ t ∈ Ici (0 : ℝ),
      ClosedLaplacianStokes (gt t) (fun y ↦ (gt t).scalarAt y))
    (hFiniteDissipation :
      IntegrableOn (normalizedMeanScalarAbsoluteVarianceDissipation gt) (Ici 0))
    (hOrbitSeqCompact : IsSeqCompact (closure (Set.range gt)))
    (hInvariantSeqContinuous :
      SeqContinuous (closedMetricMeanTracelessEnergyPair (M := M)))
    {c : ℝ} (hc : 0 < c)
    (hScalarLower : ∀ t ∈ Ici (0 : ℝ), ∀ x : M,
      c ≤ (gt t).scalarAt x) :
    HamiltonConvergencePinchedLimit3Core M := by
  apply
    hamiltonConvergencePinchedLimit3Core_of_normalizedFlow_finiteAbsoluteDissipation_Ici_of_seqCompact_metricOrbitClosure_of_scalarLower
      gt hFlow
  · intro t ht
    exact hScalarDomination.hasDerivAt_totalScalar_energyNumerator_of_normalizedFlowAt
      hLichnerowicz t (hFlow t ht) (hStokes t ht)
  · intro t ht
    exact hHausdorffVolume.hasDerivAt_totalVolume_of_normalizedFlowAt
      t (hFlow t ht)
  · exact hFiniteDissipation
  · exact hOrbitSeqCompact
  · exact hInvariantSeqContinuous
  · exact hc
  · exact hScalarLower

/-- Highest forward chart-frame partition compact-orbit endpoint.

Joint `C³` entries construct Lichnerowicz regularity, subordinate partition
geometry constructs Stokes, differential decay gives finite absolute
dissipation, and invariant compactness realizes the positive zero-energy
limit.  The normalized-flow equation and scalar lower bound are assumed only
on `Ici 0`. -/
theorem hamiltonConvergencePinchedLimit3Core_of_differentialDissipationDecay_of_globalHausdorffChartFrameDominationJointMetricEntriesSubordinatePartition_Ici_of_compact_metricOrbitClosure_of_scalarLower
    [Nonempty M] [SimplyConnectedSpace M]
    [TopologicalSpace (ClosedSmoothRiemannianMetric 3 M)]
    {gt : ℝ → ClosedSmoothRiemannianMetric 3 M}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hFlow : ∀ t ∈ Ici (0 : ℝ), ∀ x : M,
      IsClosedNormalizedRicciFlowSolutionAt gt t x)
    (hHausdorffVolume : GlobalFiniteHausdorffChartFrameDensityVariation gt)
    (hScalarDomination :
      GlobalFiniteHausdorffChartFrameScalarDomination hHausdorffVolume)
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
    {c : ℝ} (hc : 0 < c)
    (hScalarLower : ∀ t ∈ Ici (0 : ℝ), ∀ x : M,
      c ≤ (gt t).scalarAt x) :
    HamiltonConvergencePinchedLimit3Core M := by
  let hLichnerowicz : GlobalLichnerowiczAssemblyRegularity gt :=
    globalLichnerowiczAssemblyRegularity_of_jointMetricEntriesThree hJoint
  let hStokes : ∀ t : ℝ,
      ClosedLaplacianStokes (gt t) (fun y ↦ (gt t).scalarAt y) :=
    hPartitionGeometry.closedLaplacianStokes
  exact
    hamiltonConvergencePinchedLimit3Core_of_finiteAbsoluteDissipation_of_globalHausdorffChartFrameScalarDomination_Ici_of_globalLichnerowiczRegularity_of_compact_metricOrbitClosure_of_scalarLower
      hFlow hHausdorffVolume hScalarDomination hLichnerowicz
      (fun t _ht ↦ hStokes t)
      (normalizedMeanScalarAbsoluteVarianceDissipation_integrableOn_of_differential_decay
        gt D' hrate hDissipationDeriv hDifferentialInequality)
      hOrbitCompact hInvariantContinuous hc hScalarLower

/-- Exponential absolute-dissipation decay is a direct alternative to the
derivative/coercivity pair in the highest forward chart-frame endpoint.

This theorem does not assert the geometric exponential estimate: it isolates
that estimate, together with the minimal measurability premise needed for
dominated integration, as the remaining quantitative boundary. -/
theorem hamiltonConvergencePinchedLimit3Core_of_exponentialDissipationDecay_of_globalHausdorffChartFrameDominationJointMetricEntriesSubordinatePartition_Ici_of_compact_metricOrbitClosure_of_scalarLower
    [Nonempty M] [SimplyConnectedSpace M]
    [TopologicalSpace (ClosedSmoothRiemannianMetric 3 M)]
    {gt : ℝ → ClosedSmoothRiemannianMetric 3 M}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hFlow : ∀ t ∈ Ici (0 : ℝ), ∀ x : M,
      IsClosedNormalizedRicciFlowSolutionAt gt t x)
    (hHausdorffVolume : GlobalFiniteHausdorffChartFrameDensityVariation gt)
    (hScalarDomination :
      GlobalFiniteHausdorffChartFrameScalarDomination hHausdorffVolume)
    (hJoint : ∀ t : ℝ, ∀ y : M,
      MetricEntriesJointContDiffAt gt t y 3)
    (hPartitionGeometry :
      GlobalFiniteSubordinateHausdorffLaplacianGeometry
        gt (fun t y ↦ (gt t).scalarAt y))
    (hDissipationMeasurable : AEStronglyMeasurable
      (normalizedMeanScalarAbsoluteVarianceDissipation gt)
      (MeasureTheory.volume.restrict (Ici 0)))
    {C rate : ℝ} (hrate : 0 < rate)
    (hDecay : ∀ t ∈ Ici (0 : ℝ),
      normalizedMeanScalarAbsoluteVarianceDissipation gt t ≤
        C * Real.exp ((-rate) * t))
    (hOrbitCompact : IsCompact (closure (Set.range gt)))
    (hInvariantContinuous : ContinuousOn closedMetricMeanTracelessEnergyPair
      (closure (Set.range gt)))
    {c : ℝ} (hc : 0 < c)
    (hScalarLower : ∀ t ∈ Ici (0 : ℝ), ∀ x : M,
      c ≤ (gt t).scalarAt x) :
    HamiltonConvergencePinchedLimit3Core M := by
  let hLichnerowicz : GlobalLichnerowiczAssemblyRegularity gt :=
    globalLichnerowiczAssemblyRegularity_of_jointMetricEntriesThree hJoint
  let hStokes : ∀ t : ℝ,
      ClosedLaplacianStokes (gt t) (fun y ↦ (gt t).scalarAt y) :=
    hPartitionGeometry.closedLaplacianStokes
  exact
    hamiltonConvergencePinchedLimit3Core_of_finiteAbsoluteDissipation_of_globalHausdorffChartFrameScalarDomination_Ici_of_globalLichnerowiczRegularity_of_compact_metricOrbitClosure_of_scalarLower
      hFlow hHausdorffVolume hScalarDomination hLichnerowicz
      (fun t _ht ↦ hStokes t)
      (normalizedMeanScalarAbsoluteVarianceDissipation_integrableOn_of_exponential_bound
        gt hDissipationMeasurable hrate hDecay)
      hOrbitCompact hInvariantContinuous hc hScalarLower

/-- The strongest honest exponential-decay endpoint currently available from
concrete time regularity.  Only continuity of the moving scalar-variance
integral is assumed; measurability of the absolute mean-scalar derivative is
automatic, so no measurability premise for the assembled dissipation remains. -/
theorem hamiltonConvergencePinchedLimit3Core_of_continuousScalarVariance_exponentialDissipationDecay_of_globalHausdorffChartFrameDominationJointMetricEntriesSubordinatePartition_Ici_of_compact_metricOrbitClosure_of_scalarLower
    [Nonempty M] [SimplyConnectedSpace M]
    [TopologicalSpace (ClosedSmoothRiemannianMetric 3 M)]
    {gt : ℝ → ClosedSmoothRiemannianMetric 3 M}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hFlow : ∀ t ∈ Ici (0 : ℝ), ∀ x : M,
      IsClosedNormalizedRicciFlowSolutionAt gt t x)
    (hHausdorffVolume : GlobalFiniteHausdorffChartFrameDensityVariation gt)
    (hScalarDomination :
      GlobalFiniteHausdorffChartFrameScalarDomination hHausdorffVolume)
    (hJoint : ∀ t : ℝ, ∀ y : M,
      MetricEntriesJointContDiffAt gt t y 3)
    (hPartitionGeometry :
      GlobalFiniteSubordinateHausdorffLaplacianGeometry
        gt (fun t y ↦ (gt t).scalarAt y))
    (hScalarVarianceContinuous : ContinuousOn
      (fun t : ℝ ↦
        ∫ x, ((gt t).scalarAt x - meanScalar (gt t)) ^ 2
          ∂(volumeMeasure (gt t)))
      (Ici 0))
    {C rate : ℝ} (hrate : 0 < rate)
    (hDecay : ∀ t ∈ Ici (0 : ℝ),
      normalizedMeanScalarAbsoluteVarianceDissipation gt t ≤
        C * Real.exp ((-rate) * t))
    (hOrbitCompact : IsCompact (closure (Set.range gt)))
    (hInvariantContinuous : ContinuousOn closedMetricMeanTracelessEnergyPair
      (closure (Set.range gt)))
    {c : ℝ} (hc : 0 < c)
    (hScalarLower : ∀ t ∈ Ici (0 : ℝ), ∀ x : M,
      c ≤ (gt t).scalarAt x) :
    HamiltonConvergencePinchedLimit3Core M := by
  exact
    hamiltonConvergencePinchedLimit3Core_of_exponentialDissipationDecay_of_globalHausdorffChartFrameDominationJointMetricEntriesSubordinatePartition_Ici_of_compact_metricOrbitClosure_of_scalarLower
      hFlow hHausdorffVolume hScalarDomination hJoint hPartitionGeometry
      (normalizedMeanScalarAbsoluteVarianceDissipation_aestronglyMeasurable_of_continuousOn_scalarVariance
        gt hScalarVarianceContinuous)
      hrate hDecay hOrbitCompact hInvariantContinuous hc hScalarLower

/-- Finite chartwise domination discharges the remaining moving
scalar-variance continuity premise in the forward exponential endpoint.

Joint `C³` entries supply pointwise scalar continuity, the normalized-flow
moving-integral identities supply continuity of the mean scalar, and the
chart-frame density package supplies continuity of each coordinate density.
Only an integrable time-uniform bound for the finite coordinate variance
densities remains explicit. -/
theorem hamiltonConvergencePinchedLimit3Core_of_finiteChartScalarVarianceDomination_exponentialDissipationDecay_of_globalHausdorffChartFrameDominationJointMetricEntriesSubordinatePartition_Ici_of_compact_metricOrbitClosure_of_scalarLower
    [Nonempty M] [SimplyConnectedSpace M]
    [TopologicalSpace (ClosedSmoothRiemannianMetric 3 M)]
    {gt : ℝ → ClosedSmoothRiemannianMetric 3 M}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hFlow : ∀ t ∈ Ici (0 : ℝ), ∀ x : M,
      IsClosedNormalizedRicciFlowSolutionAt gt t x)
    (hHausdorffVolume : GlobalFiniteHausdorffChartFrameDensityVariation gt)
    (hScalarDomination :
      GlobalFiniteHausdorffChartFrameScalarDomination hHausdorffVolume)
    (hJoint : ∀ t : ℝ, ∀ y : M,
      MetricEntriesJointContDiffAt gt t y 3)
    (hPartitionGeometry :
      GlobalFiniteSubordinateHausdorffLaplacianGeometry
        gt (fun t y ↦ (gt t).scalarAt y))
    (hScalarVarianceDomination : ∀ t ∈ Ici (0 : ℝ),
      FiniteChartScalarVarianceDensityDominationAt
        (hHausdorffVolume.differentiation t))
    {C rate : ℝ} (hrate : 0 < rate)
    (hDecay : ∀ t ∈ Ici (0 : ℝ),
      normalizedMeanScalarAbsoluteVarianceDissipation gt t ≤
        C * Real.exp ((-rate) * t))
    (hOrbitCompact : IsCompact (closure (Set.range gt)))
    (hInvariantContinuous : ContinuousOn closedMetricMeanTracelessEnergyPair
      (closure (Set.range gt)))
    {c : ℝ} (hc : 0 < c)
    (hScalarLower : ∀ t ∈ Ici (0 : ℝ), ∀ x : M,
      c ≤ (gt t).scalarAt x) :
    HamiltonConvergencePinchedLimit3Core M := by
  let hLichnerowicz : GlobalLichnerowiczAssemblyRegularity gt :=
    globalLichnerowiczAssemblyRegularity_of_jointMetricEntriesThree hJoint
  let hStokes : ∀ t : ℝ,
      ClosedLaplacianStokes (gt t) (fun y ↦ (gt t).scalarAt y) :=
    hPartitionGeometry.closedLaplacianStokes
  have hMeanContinuous : ∀ t ∈ Ici (0 : ℝ),
      ContinuousAt (fun s ↦ meanScalar (gt s)) t := by
    intro t ht
    exact
      (hasDerivAt_meanScalar_energyQuotient_of_normalizedFlow
        (hFlow t ht) (by norm_num)
        (hScalarDomination.hasDerivAt_totalScalar_energyNumerator_of_normalizedFlowAt
          hLichnerowicz t (hFlow t ht) (hStokes t))
        (hHausdorffVolume.hasDerivAt_totalVolume_of_normalizedFlowAt
          t (hFlow t ht))).continuousAt
  have hScalarVarianceContinuous : ContinuousOn
      (fun t : ℝ ↦
        ∫ x, ((gt t).scalarAt x - meanScalar (gt t)) ^ 2
          ∂(volumeMeasure (gt t)))
      (Ici 0) :=
    continuousOn_centeredScalarVarianceIntegral_of_globalFiniteHausdorffChartFrameDomination
      hHausdorffVolume hJoint hMeanContinuous hScalarVarianceDomination
  exact
    hamiltonConvergencePinchedLimit3Core_of_continuousScalarVariance_exponentialDissipationDecay_of_globalHausdorffChartFrameDominationJointMetricEntriesSubordinatePartition_Ici_of_compact_metricOrbitClosure_of_scalarLower
      hFlow hHausdorffVolume hScalarDomination hJoint hPartitionGeometry
      hScalarVarianceContinuous hrate hDecay hOrbitCompact
      hInvariantContinuous hc hScalarLower

/-- Local uniform boundedness of the centered scalar curvature replaces the
coordinate-product domination premise.  The existing density derivative
majorant is converted, by the mean value theorem, into the integrable density
majorant needed for scalar-variance dominated convergence. -/
theorem hamiltonConvergencePinchedLimit3Core_of_centeredScalarLocalBound_exponentialDissipationDecay_of_globalHausdorffChartFrameDominationJointMetricEntriesSubordinatePartition_Ici_of_compact_metricOrbitClosure_of_scalarLower
    [Nonempty M] [SimplyConnectedSpace M]
    [TopologicalSpace (ClosedSmoothRiemannianMetric 3 M)]
    {gt : ℝ → ClosedSmoothRiemannianMetric 3 M}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hFlow : ∀ t ∈ Ici (0 : ℝ), ∀ x : M,
      IsClosedNormalizedRicciFlowSolutionAt gt t x)
    (hHausdorffVolume : GlobalFiniteHausdorffChartFrameDensityVariation gt)
    (hScalarDomination :
      GlobalFiniteHausdorffChartFrameScalarDomination hHausdorffVolume)
    (hJoint : ∀ t : ℝ, ∀ y : M,
      MetricEntriesJointContDiffAt gt t y 3)
    (hPartitionGeometry :
      GlobalFiniteSubordinateHausdorffLaplacianGeometry
        gt (fun t y ↦ (gt t).scalarAt y))
    (hCenteredScalarLocalBound :
      GlobalFiniteHausdorffChartFrameCenteredScalarLocalBound
        hHausdorffVolume)
    {C rate : ℝ} (hrate : 0 < rate)
    (hDecay : ∀ t ∈ Ici (0 : ℝ),
      normalizedMeanScalarAbsoluteVarianceDissipation gt t ≤
        C * Real.exp ((-rate) * t))
    (hOrbitCompact : IsCompact (closure (Set.range gt)))
    (hInvariantContinuous : ContinuousOn closedMetricMeanTracelessEnergyPair
      (closure (Set.range gt)))
    {c : ℝ} (hc : 0 < c)
    (hScalarLower : ∀ t ∈ Ici (0 : ℝ), ∀ x : M,
      c ≤ (gt t).scalarAt x) :
    HamiltonConvergencePinchedLimit3Core M := by
  exact
    hamiltonConvergencePinchedLimit3Core_of_finiteChartScalarVarianceDomination_exponentialDissipationDecay_of_globalHausdorffChartFrameDominationJointMetricEntriesSubordinatePartition_Ici_of_compact_metricOrbitClosure_of_scalarLower
      hFlow hHausdorffVolume hScalarDomination hJoint hPartitionGeometry
      (fun t ht ↦
        hCenteredScalarLocalBound.toScalarVarianceDensityDomination t ht)
      hrate hDecay hOrbitCompact hInvariantContinuous hc hScalarLower

/-- Strongest forward exponential endpoint at the moving-measure regularity
boundary.  Joint `C³` metric entries bound scalar curvature on compact local
space-time slabs, while normalized-flow first variation makes the mean scalar
locally continuous.  Thus the centered-scalar and coordinate-density
domination packages are constructed rather than assumed. -/
theorem hamiltonConvergencePinchedLimit3Core_of_automaticScalarVarianceDomination_exponentialDissipationDecay_of_globalHausdorffChartFrameDominationJointMetricEntriesSubordinatePartition_Ici_of_compact_metricOrbitClosure_of_scalarLower
    [Nonempty M] [SimplyConnectedSpace M]
    [TopologicalSpace (ClosedSmoothRiemannianMetric 3 M)]
    {gt : ℝ → ClosedSmoothRiemannianMetric 3 M}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hFlow : ∀ t ∈ Ici (0 : ℝ), ∀ x : M,
      IsClosedNormalizedRicciFlowSolutionAt gt t x)
    (hHausdorffVolume : GlobalFiniteHausdorffChartFrameDensityVariation gt)
    (hScalarDomination :
      GlobalFiniteHausdorffChartFrameScalarDomination hHausdorffVolume)
    (hJoint : ∀ t : ℝ, ∀ y : M,
      MetricEntriesJointContDiffAt gt t y 3)
    (hPartitionGeometry :
      GlobalFiniteSubordinateHausdorffLaplacianGeometry
        gt (fun t y ↦ (gt t).scalarAt y))
    {C rate : ℝ} (hrate : 0 < rate)
    (hDecay : ∀ t ∈ Ici (0 : ℝ),
      normalizedMeanScalarAbsoluteVarianceDissipation gt t ≤
        C * Real.exp ((-rate) * t))
    (hOrbitCompact : IsCompact (closure (Set.range gt)))
    (hInvariantContinuous : ContinuousOn closedMetricMeanTracelessEnergyPair
      (closure (Set.range gt)))
    {c : ℝ} (hc : 0 < c)
    (hScalarLower : ∀ t ∈ Ici (0 : ℝ), ∀ x : M,
      c ≤ (gt t).scalarAt x) :
    HamiltonConvergencePinchedLimit3Core M := by
  let hLichnerowicz : GlobalLichnerowiczAssemblyRegularity gt :=
    globalLichnerowiczAssemblyRegularity_of_jointMetricEntriesThree hJoint
  let hStokes : ∀ t : ℝ,
      ClosedLaplacianStokes (gt t) (fun y ↦ (gt t).scalarAt y) :=
    hPartitionGeometry.closedLaplacianStokes
  have hMeanContinuous : ∀ t ∈ Ici (0 : ℝ),
      ContinuousAt (fun s ↦ meanScalar (gt s)) t := by
    intro t ht
    exact
      (hasDerivAt_meanScalar_energyQuotient_of_normalizedFlow
        (hFlow t ht) (by norm_num)
        (hScalarDomination.hasDerivAt_totalScalar_energyNumerator_of_normalizedFlowAt
          hLichnerowicz t (hFlow t ht) (hStokes t))
        (hHausdorffVolume.hasDerivAt_totalVolume_of_normalizedFlowAt
          t (hFlow t ht))).continuousAt
  let hCenteredScalarLocalBound :
      GlobalFiniteHausdorffChartFrameCenteredScalarLocalBound
        hHausdorffVolume :=
    GlobalFiniteHausdorffChartFrameCenteredScalarLocalBound.of_jointMetricEntriesThree
      hHausdorffVolume hJoint hMeanContinuous
  exact
    hamiltonConvergencePinchedLimit3Core_of_centeredScalarLocalBound_exponentialDissipationDecay_of_globalHausdorffChartFrameDominationJointMetricEntriesSubordinatePartition_Ici_of_compact_metricOrbitClosure_of_scalarLower
      hFlow hHausdorffVolume hScalarDomination hJoint hPartitionGeometry
      hCenteredScalarLocalBound hrate hDecay hOrbitCompact
      hInvariantContinuous hc hScalarLower

/-- Strongest sequential-compactness form of the forward exponential
endpoint.  All moving-measure domination is automatic, while realization of
the limiting metric uses only sequential compactness of the orbit closure and
sequential continuity of the two consumed invariants. -/
theorem hamiltonConvergencePinchedLimit3Core_of_automaticScalarVarianceDomination_exponentialDissipationDecay_of_globalHausdorffChartFrameDominationJointMetricEntriesSubordinatePartition_Ici_of_seqCompact_metricOrbitClosure_of_scalarLower
    [Nonempty M] [SimplyConnectedSpace M]
    [TopologicalSpace (ClosedSmoothRiemannianMetric 3 M)]
    {gt : ℝ → ClosedSmoothRiemannianMetric 3 M}
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hFlow : ∀ t ∈ Ici (0 : ℝ), ∀ x : M,
      IsClosedNormalizedRicciFlowSolutionAt gt t x)
    (hHausdorffVolume : GlobalFiniteHausdorffChartFrameDensityVariation gt)
    (hScalarDomination :
      GlobalFiniteHausdorffChartFrameScalarDomination hHausdorffVolume)
    (hJoint : ∀ t : ℝ, ∀ y : M,
      MetricEntriesJointContDiffAt gt t y 3)
    (hPartitionGeometry :
      GlobalFiniteSubordinateHausdorffLaplacianGeometry
        gt (fun t y ↦ (gt t).scalarAt y))
    {C rate : ℝ} (hrate : 0 < rate)
    (hDecay : ∀ t ∈ Ici (0 : ℝ),
      normalizedMeanScalarAbsoluteVarianceDissipation gt t ≤
        C * Real.exp ((-rate) * t))
    (hOrbitSeqCompact : IsSeqCompact (closure (Set.range gt)))
    (hInvariantSeqContinuous :
      SeqContinuous (closedMetricMeanTracelessEnergyPair (M := M)))
    {c : ℝ} (hc : 0 < c)
    (hScalarLower : ∀ t ∈ Ici (0 : ℝ), ∀ x : M,
      c ≤ (gt t).scalarAt x) :
    HamiltonConvergencePinchedLimit3Core M := by
  let hLichnerowicz : GlobalLichnerowiczAssemblyRegularity gt :=
    globalLichnerowiczAssemblyRegularity_of_jointMetricEntriesThree hJoint
  let hStokes : ∀ t : ℝ,
      ClosedLaplacianStokes (gt t) (fun y ↦ (gt t).scalarAt y) :=
    hPartitionGeometry.closedLaplacianStokes
  have hMeanContinuous : ∀ t ∈ Ici (0 : ℝ),
      ContinuousAt (fun s ↦ meanScalar (gt s)) t := by
    intro t ht
    exact
      (hasDerivAt_meanScalar_energyQuotient_of_normalizedFlow
        (hFlow t ht) (by norm_num)
        (hScalarDomination.hasDerivAt_totalScalar_energyNumerator_of_normalizedFlowAt
          hLichnerowicz t (hFlow t ht) (hStokes t))
        (hHausdorffVolume.hasDerivAt_totalVolume_of_normalizedFlowAt
          t (hFlow t ht))).continuousAt
  let hCenteredScalarLocalBound :
      GlobalFiniteHausdorffChartFrameCenteredScalarLocalBound
        hHausdorffVolume :=
    GlobalFiniteHausdorffChartFrameCenteredScalarLocalBound.of_jointMetricEntriesThree
      hHausdorffVolume hJoint hMeanContinuous
  have hScalarVarianceContinuous : ContinuousOn
      (fun t : ℝ ↦
        ∫ x, ((gt t).scalarAt x - meanScalar (gt t)) ^ 2
          ∂(volumeMeasure (gt t)))
      (Ici 0) :=
    continuousOn_centeredScalarVarianceIntegral_of_globalFiniteHausdorffChartFrameDomination
      hHausdorffVolume hJoint hMeanContinuous
      (fun t ht ↦
        hCenteredScalarLocalBound.toScalarVarianceDensityDomination t ht)
  have hFiniteDissipation :
      IntegrableOn (normalizedMeanScalarAbsoluteVarianceDissipation gt) (Ici 0) :=
    normalizedMeanScalarAbsoluteVarianceDissipation_integrableOn_of_exponential_bound
      gt
      (normalizedMeanScalarAbsoluteVarianceDissipation_aestronglyMeasurable_of_continuousOn_scalarVariance
        gt hScalarVarianceContinuous)
      hrate hDecay
  exact
    hamiltonConvergencePinchedLimit3Core_of_finiteAbsoluteDissipation_of_globalHausdorffChartFrameScalarDomination_Ici_of_globalLichnerowiczRegularity_of_seqCompact_metricOrbitClosure_of_scalarLower
      hFlow hHausdorffVolume hScalarDomination hLichnerowicz
      (fun t _ht ↦ hStokes t) hFiniteDissipation hOrbitSeqCompact
      hInvariantSeqContinuous hc hScalarLower

end Poincare
