import Poincare.Global.NormalizedFlowForwardFiniteTracelessEnergyCompactMeanEndpoint

/-!
# Finite forward traceless energy with a closed invariant range

The compact-parameter endpoint does not need compactness of a space of
metrics when the two scalar invariants attained by the forward path form a
closed set.  Finite traceless-Ricci energy supplies times at which the energy
tends to zero.  Lower and upper bounds for mean scalar put the remaining
coordinate in a compact interval, so a subsequence converges.  Closedness of
the actual forward invariant range then realizes the limiting pair by one of
the original smooth metrics.

No topology on the type of smooth metrics and no continuity of a moving
integral is used in this route.
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

/-- Finite forward traceless-Ricci energy, a closed attained invariant range,
and two-sided mean-scalar bounds produce a positive Einstein metric. -/
theorem hamiltonConvergencePinchedLimit3Core_of_finiteTracelessRicciEnergy_Ici_of_closed_forward_meanEnergy_range_of_meanBounds
    [Nonempty M] [SimplyConnectedSpace M]
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    (hFiniteTracelessRicciEnergy :
      IntegrableOn (normalizedFlowTracelessRicciEnergyTrack gt) (Ici 0))
    (hRangeClosed : IsClosed
      (Set.range (fun t : Ici (0 : ℝ) ↦
        closedMetricMeanTracelessEnergyPair (gt t.1))))
    {c C : ℝ} (hc : 0 < c)
    (hMeanLower : ∀ t : Ici (0 : ℝ), c ≤ meanScalar (gt t.1))
    (hMeanUpper : ∀ t : Ici (0 : ℝ), meanScalar (gt t.1) ≤ C) :
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
  let meanSequence : ℕ → ℝ := fun i ↦
    meanScalar (gt (forwardSample i).1)
  have hMeanMem : ∀ i : ℕ, meanSequence i ∈ Icc c C := by
    intro i
    exact ⟨hMeanLower (forwardSample i), hMeanUpper (forwardSample i)⟩
  obtain ⟨meanLimit, hMeanLimitMem, phi, hphi, hMeanLimit⟩ :=
    (isCompact_Icc : IsCompact (Icc c C)).tendsto_subseq hMeanMem
  have hEnergySubsequence :
      Tendsto
        (fun i ↦ normalizedFlowTracelessRicciEnergyTrack gt
          (forwardSample (phi i)).1)
        atTop (nhds 0) :=
    hForwardEnergyZero.comp hphi.tendsto_atTop
  have hPairLimit :
      Tendsto
        (fun i ↦ closedMetricMeanTracelessEnergyPair
          (gt (forwardSample (phi i)).1))
        atTop (nhds (meanLimit, 0)) := by
    exact hMeanLimit.prodMk_nhds hEnergySubsequence
  have hLimitMem : (meanLimit, 0) ∈
      Set.range (fun t : Ici (0 : ℝ) ↦
        closedMetricMeanTracelessEnergyPair (gt t.1)) := by
    apply hRangeClosed.mem_of_tendsto hPairLimit
    exact Eventually.of_forall fun i ↦ ⟨forwardSample (phi i), rfl⟩
  obtain ⟨tLimit, hLimit⟩ := hLimitMem
  have hLimitMean : meanScalar (gt tLimit.1) = meanLimit :=
    congrArg Prod.fst hLimit
  have hLimitEnergy :
      (∫ x, (gt tLimit.1).tracelessRicciNormSqAt x
        ∂(volumeMeasure (gt tLimit.1))) = 0 :=
    congrArg Prod.snd hLimit
  exact hamiltonConvergencePinchedLimit3Core_of_zero_tracelessRicci_energy_auto
    (gt tLimit.1) hLimitEnergy <| by
      rw [hLimitMean]
      exact hc.trans_le hMeanLimitMem.1

/-- Positive-Einstein form of the closed forward invariant-range endpoint. -/
theorem positiveEinsteinMetric3_of_finiteTracelessRicciEnergy_Ici_of_closed_forward_meanEnergy_range_of_meanBounds
    [Nonempty M] [SimplyConnectedSpace M]
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    (hFiniteTracelessRicciEnergy :
      IntegrableOn (normalizedFlowTracelessRicciEnergyTrack gt) (Ici 0))
    (hRangeClosed : IsClosed
      (Set.range (fun t : Ici (0 : ℝ) ↦
        closedMetricMeanTracelessEnergyPair (gt t.1))))
    {c C : ℝ} (hc : 0 < c)
    (hMeanLower : ∀ t : Ici (0 : ℝ), c ≤ meanScalar (gt t.1))
    (hMeanUpper : ∀ t : Ici (0 : ℝ), meanScalar (gt t.1) ≤ C) :
    PositiveEinsteinMetric3 M :=
  positiveEinsteinMetric3_of_hamiltonConvergencePinchedLimit3Core <|
    hamiltonConvergencePinchedLimit3Core_of_finiteTracelessRicciEnergy_Ici_of_closed_forward_meanEnergy_range_of_meanBounds
      gt hFiniteTracelessRicciEnergy hRangeClosed hc hMeanLower hMeanUpper

/-- Unit-curvature form of the closed forward invariant-range endpoint. -/
theorem exists_unitConstantCurvature_of_finiteTracelessRicciEnergy_Ici_of_closed_forward_meanEnergy_range_of_meanBounds
    [Nonempty M] [SimplyConnectedSpace M]
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    (hFiniteTracelessRicciEnergy :
      IntegrableOn (normalizedFlowTracelessRicciEnergyTrack gt) (Ici 0))
    (hRangeClosed : IsClosed
      (Set.range (fun t : Ici (0 : ℝ) ↦
        closedMetricMeanTracelessEnergyPair (gt t.1))))
    {c C : ℝ} (hc : 0 < c)
    (hMeanLower : ∀ t : Ici (0 : ℝ), c ≤ meanScalar (gt t.1))
    (hMeanUpper : ∀ t : Ici (0 : ℝ), meanScalar (gt t.1) ≤ C) :
    ∃ g' : ClosedSmoothRiemannianMetric 3 M,
      HasConstantSectionalCurvature3 g' 1 := by
  apply exists_unitConstantCurvature_of_positiveEinsteinMetric3
  exact
    positiveEinsteinMetric3_of_finiteTracelessRicciEnergy_Ici_of_closed_forward_meanEnergy_range_of_meanBounds
      gt hFiniteTracelessRicciEnergy hRangeClosed hc hMeanLower hMeanUpper

/-- Sphere form of the closed forward invariant-range endpoint. -/
theorem sphereConclusion_of_finiteTracelessRicciEnergy_Ici_of_closed_forward_meanEnergy_range_of_meanBounds
    [Nonempty M] [SimplyConnectedSpace M]
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    (hFiniteTracelessRicciEnergy :
      IntegrableOn (normalizedFlowTracelessRicciEnergyTrack gt) (Ici 0))
    (hRangeClosed : IsClosed
      (Set.range (fun t : Ici (0 : ℝ) ↦
        closedMetricMeanTracelessEnergyPair (gt t.1))))
    {c C : ℝ} (hc : 0 < c)
    (hMeanLower : ∀ t : Ici (0 : ℝ), c ≤ meanScalar (gt t.1))
    (hMeanUpper : ∀ t : Ici (0 : ℝ), meanScalar (gt t.1) ≤ C)
    (hUnit : UnitConstantCurvatureSphereRecognition3 M) :
    Nonempty
      (M ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) (1 : ℝ)) := by
  apply sphereConclusion_of_positiveEinstein_of_unitRecognition _ hUnit
  exact
    positiveEinsteinMetric3_of_finiteTracelessRicciEnergy_Ici_of_closed_forward_meanEnergy_range_of_meanBounds
      gt hFiniteTracelessRicciEnergy hRangeClosed hc hMeanLower hMeanUpper

end Poincare
