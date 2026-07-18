import Poincare.Global.NormalizedFlowForwardFiniteDissipationReduction
import Poincare.Global.NormalizedFlowInvariantCompactness
import Poincare.Global.PinchedLimitPositiveEinstein
import Poincare.Global.EinsteinNormalization

/-!
# Forward finite-traceless-energy compact mean endpoint

Time-integrability of total squared traceless Ricci already selects escaping
forward times at which that energy tends to zero.  A compact parameterization
continuous only in

`(mean scalar, total squared traceless-Ricci energy)`

then realizes a cluster point of those invariant pairs.  A uniform positive
lower bound for the mean scalar passes to its first coordinate, while the
second coordinate is zero.  The resulting smooth metric feeds directly into
the automatic zero-energy Hamilton endpoint.

This route uses neither scalar variance nor the normalized-flow derivative
identity.  It assumes no flow equation, moving-integral differentiation,
pointwise scalar floor, or inequality comparing scalar variance to traceless
Ricci energy.
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

/-- Finite forward traceless-Ricci energy and compact realization of the
mean-energy pair produce Hamilton's reduced positive-Einstein endpoint.

The escaping-sample theorem does not state that every selected time is
nonnegative.  Its `atTop` conclusion makes the sample eventually nonnegative;
`forwardSample` clamps only the finite exceptional prefix to zero before the
compactness argument. -/
theorem hamiltonConvergencePinchedLimit3Core_of_finiteTracelessRicciEnergy_Ici_of_compact_meanEnergy_parameterization_of_meanLower
    [Nonempty M] [SimplyConnectedSpace M]
    {K : Type v} [TopologicalSpace K] [CompactSpace K]
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    (hFiniteTracelessRicciEnergy :
      IntegrableOn (normalizedFlowTracelessRicciEnergyTrack gt) (Ici 0))
    (metric : K → ClosedSmoothRiemannianMetric 3 M)
    (parameter : Ici (0 : ℝ) → K)
    (hRealize : ∀ t : Ici (0 : ℝ), metric (parameter t) = gt t.1)
    (hInvariantContinuous :
      Continuous (fun k ↦ closedMetricMeanTracelessEnergyPair (metric k)))
    {c : ℝ} (hc : 0 < c)
    (hMeanLower : ∀ t : Ici (0 : ℝ), c ≤ meanScalar (gt t.1)) :
    HamiltonConvergencePinchedLimit3Core M := by
  have hEnergyNonneg : ∀ t ∈ Ici (0 : ℝ),
      0 ≤ normalizedFlowTracelessRicciEnergyTrack gt t := by
    intro t _ht
    exact integral_nonneg fun x ↦
      (gt t).tracelessRicciNormSqAt_nonneg x (by norm_num)
  obtain ⟨sample, hSampleAtTop, hEnergyZero⟩ :=
    exists_escaping_sample_value_tendsto_zero_of_integrableOn_nonneg
      (normalizedFlowTracelessRicciEnergyTrack gt)
      hEnergyNonneg hFiniteTracelessRicciEnergy
  have hSampleEventuallyNonneg : ∀ᶠ i in atTop, 0 ≤ sample i :=
    hSampleAtTop.eventually (eventually_ge_atTop (0 : ℝ))
  let forwardSample : ℕ → Ici (0 : ℝ) := fun i ↦
    ⟨max 0 (sample i), le_max_left 0 (sample i)⟩
  have hForwardSampleEventually : ∀ᶠ i in atTop,
      (forwardSample i).1 = sample i := by
    filter_upwards [hSampleEventuallyNonneg] with i hi
    simp only [forwardSample, max_eq_right hi]
  have hForwardEnergyZero :
      Tendsto
        (fun i ↦ normalizedFlowTracelessRicciEnergyTrack gt
          (forwardSample i).1)
        atTop (nhds 0) := by
    apply hEnergyZero.congr'
    filter_upwards [hForwardSampleEventually] with i hi
    rw [hi]
  let pairSequence : ℕ → ℝ × ℝ := fun i ↦
    closedMetricMeanTracelessEnergyPair (gt (forwardSample i).1)
  have hPairCompact : IsCompact
      (Set.range (fun k ↦ closedMetricMeanTracelessEnergyPair (metric k))) :=
    isCompact_range hInvariantContinuous
  have hPairMem : ∀ i : ℕ, pairSequence i ∈
      Set.range (fun k ↦ closedMetricMeanTracelessEnergyPair (metric k)) := by
    intro i
    refine ⟨parameter (forwardSample i), ?_⟩
    change
      closedMetricMeanTracelessEnergyPair
          (metric (parameter (forwardSample i))) =
        closedMetricMeanTracelessEnergyPair (gt (forwardSample i).1)
    rw [hRealize]
  obtain ⟨pairLimit, hPairLimitMem, φ, hφ, hPairLimit⟩ :=
    hPairCompact.tendsto_subseq hPairMem
  have hEnergySubsequence :
      Tendsto
        (fun i ↦ normalizedFlowTracelessRicciEnergyTrack gt
          (forwardSample (φ i)).1)
        atTop (nhds 0) :=
    hForwardEnergyZero.comp hφ.tendsto_atTop
  have hPairSecond :
      Tendsto (fun i ↦ (pairSequence (φ i)).2) atTop
        (nhds pairLimit.2) :=
    (continuous_snd.tendsto pairLimit).comp hPairLimit
  have hPairSecondZero : pairLimit.2 = 0 := by
    apply tendsto_nhds_unique hPairSecond
    simpa only [pairSequence, closedMetricMeanTracelessEnergyPair,
      normalizedFlowTracelessRicciEnergyTrack] using hEnergySubsequence
  have hPairFirst :
      Tendsto (fun i ↦ meanScalar (gt (forwardSample (φ i)).1))
        atTop (nhds pairLimit.1) := by
    simpa only [pairSequence, closedMetricMeanTracelessEnergyPair] using
      (continuous_fst.tendsto pairLimit).comp hPairLimit
  have hPairFirstLower : c ≤ pairLimit.1 :=
    ge_of_tendsto hPairFirst <|
      Eventually.of_forall fun i ↦ hMeanLower (forwardSample (φ i))
  obtain ⟨kLimit, hPairEq⟩ := hPairLimitMem
  have hLimitEnergy :
      (∫ x, (metric kLimit).tracelessRicciNormSqAt x
        ∂(volumeMeasure (metric kLimit))) = 0 := by
    calc
      (∫ x, (metric kLimit).tracelessRicciNormSqAt x
          ∂(volumeMeasure (metric kLimit))) =
          (closedMetricMeanTracelessEnergyPair (metric kLimit)).2 := rfl
      _ = pairLimit.2 := congrArg Prod.snd hPairEq
      _ = 0 := hPairSecondZero
  have hLimitMeanLower : c ≤ meanScalar (metric kLimit) := by
    calc
      c ≤ pairLimit.1 := hPairFirstLower
      _ = (closedMetricMeanTracelessEnergyPair (metric kLimit)).1 :=
        (congrArg Prod.fst hPairEq).symm
      _ = meanScalar (metric kLimit) := rfl
  exact hamiltonConvergencePinchedLimit3Core_of_zero_tracelessRicci_energy_auto
    (metric kLimit) hLimitEnergy (hc.trans_le hLimitMeanLower)

/-- Positive-Einstein form of the compact mean-energy endpoint. -/
theorem positiveEinsteinMetric3_of_finiteTracelessRicciEnergy_Ici_of_compact_meanEnergy_parameterization_of_meanLower
    [Nonempty M] [SimplyConnectedSpace M]
    {K : Type v} [TopologicalSpace K] [CompactSpace K]
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    (hFiniteTracelessRicciEnergy :
      IntegrableOn (normalizedFlowTracelessRicciEnergyTrack gt) (Ici 0))
    (metric : K → ClosedSmoothRiemannianMetric 3 M)
    (parameter : Ici (0 : ℝ) → K)
    (hRealize : ∀ t : Ici (0 : ℝ), metric (parameter t) = gt t.1)
    (hInvariantContinuous :
      Continuous (fun k ↦ closedMetricMeanTracelessEnergyPair (metric k)))
    {c : ℝ} (hc : 0 < c)
    (hMeanLower : ∀ t : Ici (0 : ℝ), c ≤ meanScalar (gt t.1)) :
    PositiveEinsteinMetric3 M :=
  positiveEinsteinMetric3_of_hamiltonConvergencePinchedLimit3Core <|
    hamiltonConvergencePinchedLimit3Core_of_finiteTracelessRicciEnergy_Ici_of_compact_meanEnergy_parameterization_of_meanLower
      gt hFiniteTracelessRicciEnergy metric parameter hRealize
      hInvariantContinuous hc hMeanLower

/-- The compact mean-energy endpoint produces a unit-curvature metric. -/
theorem exists_unitConstantCurvature_of_finiteTracelessRicciEnergy_Ici_of_compact_meanEnergy_parameterization_of_meanLower
    [Nonempty M] [SimplyConnectedSpace M]
    {K : Type v} [TopologicalSpace K] [CompactSpace K]
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    (hFiniteTracelessRicciEnergy :
      IntegrableOn (normalizedFlowTracelessRicciEnergyTrack gt) (Ici 0))
    (metric : K → ClosedSmoothRiemannianMetric 3 M)
    (parameter : Ici (0 : ℝ) → K)
    (hRealize : ∀ t : Ici (0 : ℝ), metric (parameter t) = gt t.1)
    (hInvariantContinuous :
      Continuous (fun k ↦ closedMetricMeanTracelessEnergyPair (metric k)))
    {c : ℝ} (hc : 0 < c)
    (hMeanLower : ∀ t : Ici (0 : ℝ), c ≤ meanScalar (gt t.1)) :
    ∃ g' : ClosedSmoothRiemannianMetric 3 M,
      HasConstantSectionalCurvature3 g' 1 := by
  apply exists_unitConstantCurvature_of_positiveEinsteinMetric3
  exact
    positiveEinsteinMetric3_of_finiteTracelessRicciEnergy_Ici_of_compact_meanEnergy_parameterization_of_meanLower
      gt hFiniteTracelessRicciEnergy metric parameter hRealize
      hInvariantContinuous hc hMeanLower

/-- With the explicit unit-curvature recognition boundary, the compact
mean-energy endpoint yields the unit `3`-sphere conclusion. -/
theorem sphereConclusion_of_finiteTracelessRicciEnergy_Ici_of_compact_meanEnergy_parameterization_of_meanLower
    [Nonempty M] [SimplyConnectedSpace M]
    {K : Type v} [TopologicalSpace K] [CompactSpace K]
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    (hFiniteTracelessRicciEnergy :
      IntegrableOn (normalizedFlowTracelessRicciEnergyTrack gt) (Ici 0))
    (metric : K → ClosedSmoothRiemannianMetric 3 M)
    (parameter : Ici (0 : ℝ) → K)
    (hRealize : ∀ t : Ici (0 : ℝ), metric (parameter t) = gt t.1)
    (hInvariantContinuous :
      Continuous (fun k ↦ closedMetricMeanTracelessEnergyPair (metric k)))
    {c : ℝ} (hc : 0 < c)
    (hMeanLower : ∀ t : Ici (0 : ℝ), c ≤ meanScalar (gt t.1))
    (hUnit : UnitConstantCurvatureSphereRecognition3 M) :
    Nonempty
      (M ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) (1 : ℝ)) := by
  apply sphereConclusion_of_positiveEinstein_of_unitRecognition _ hUnit
  exact
    positiveEinsteinMetric3_of_finiteTracelessRicciEnergy_Ici_of_compact_meanEnergy_parameterization_of_meanLower
      gt hFiniteTracelessRicciEnergy metric parameter hRealize
      hInvariantContinuous hc hMeanLower

end Poincare
