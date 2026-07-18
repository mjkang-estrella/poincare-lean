import Poincare.Global.NormalizedFlowForwardFiniteTracelessEnergyCompactMeanEndpoint
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Forward exponential traceless-energy decay

An exponentially decaying upper bound for the total squared traceless-Ricci
energy is a concrete producer for the finite-forward-energy input of the
compact mean-energy endpoint.  Restricted almost-everywhere strong
measurability is the only analytic regularity needed; continuity on the
nonnegative time ray is recorded as a convenient sufficient condition.

The endpoint wrappers below use no flow equation, moving-integral
differentiation, or scalar-variance hypothesis.
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

omit [SecondCountableTopology M] in
/-- Total squared traceless-Ricci energy is nonnegative for every metric
path and every time. -/
theorem normalizedFlowTracelessRicciEnergyTrack_nonneg
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M) (t : ℝ) :
    0 ≤ normalizedFlowTracelessRicciEnergyTrack gt t := by
  exact integral_nonneg fun x ↦
    (gt t).tracelessRicciNormSqAt_nonneg x (by norm_num)

omit [SecondCountableTopology M] in
/-- Restricted AE strong measurability and exponential domination make the
forward traceless-Ricci energy integrable. -/
theorem normalizedFlowTracelessRicciEnergyTrack_integrableOn_of_exponential_bound
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    (hMeasurable : AEStronglyMeasurable
      (normalizedFlowTracelessRicciEnergyTrack gt)
      (MeasureTheory.volume.restrict (Ici 0)))
    {C rate : ℝ} (hrate : 0 < rate)
    (hDecay : ∀ t ∈ Ici (0 : ℝ),
      normalizedFlowTracelessRicciEnergyTrack gt t ≤
        C * Real.exp ((-rate) * t)) :
    IntegrableOn (normalizedFlowTracelessRicciEnergyTrack gt) (Ici 0) := by
  have hExpIoi : IntegrableOn
      (fun t : ℝ ↦ Real.exp ((-rate) * t)) (Ioi 0) :=
    integrableOn_exp_mul_Ioi (by linarith) 0
  have hExpIci : IntegrableOn
      (fun t : ℝ ↦ Real.exp ((-rate) * t)) (Ici 0) :=
    (integrableOn_Ici_iff_integrableOn_Ioi).2 hExpIoi
  have hDominating : IntegrableOn
      (fun t : ℝ ↦ C * Real.exp ((-rate) * t)) (Ici 0) :=
    hExpIci.const_mul C
  apply hDominating.mono' hMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
  rw [Real.norm_eq_abs, abs_of_nonneg
    (normalizedFlowTracelessRicciEnergyTrack_nonneg gt t)]
  exact hDecay t ht

omit [SecondCountableTopology M] in
/-- Continuity of the traceless-energy track on the forward ray supplies the
restricted AE strong measurability required by the decay producer. -/
theorem normalizedFlowTracelessRicciEnergyTrack_aestronglyMeasurable_of_continuousOn
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    (hContinuous : ContinuousOn
      (normalizedFlowTracelessRicciEnergyTrack gt) (Ici 0)) :
    AEStronglyMeasurable
      (normalizedFlowTracelessRicciEnergyTrack gt)
      (MeasureTheory.volume.restrict (Ici 0)) :=
  hContinuous.aestronglyMeasurable measurableSet_Ici

omit [SecondCountableTopology M] in
/-- A continuous forward energy track with an exponential upper bound has
finite forward energy. -/
theorem normalizedFlowTracelessRicciEnergyTrack_integrableOn_of_continuousOn_of_exponential_bound
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    (hContinuous : ContinuousOn
      (normalizedFlowTracelessRicciEnergyTrack gt) (Ici 0))
    {C rate : ℝ} (hrate : 0 < rate)
    (hDecay : ∀ t ∈ Ici (0 : ℝ),
      normalizedFlowTracelessRicciEnergyTrack gt t ≤
        C * Real.exp ((-rate) * t)) :
    IntegrableOn (normalizedFlowTracelessRicciEnergyTrack gt) (Ici 0) :=
  normalizedFlowTracelessRicciEnergyTrack_integrableOn_of_exponential_bound
    gt
    (normalizedFlowTracelessRicciEnergyTrack_aestronglyMeasurable_of_continuousOn
      gt hContinuous)
    hrate hDecay

/-- Exponential traceless-energy decay feeds directly into the compact
mean-energy positive-Einstein endpoint. -/
theorem positiveEinsteinMetric3_of_exponentialTracelessRicciEnergyDecay_of_compact_meanEnergy_parameterization_of_meanLower
    [Nonempty M] [SimplyConnectedSpace M]
    {K : Type v} [TopologicalSpace K] [CompactSpace K]
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    (hMeasurable : AEStronglyMeasurable
      (normalizedFlowTracelessRicciEnergyTrack gt)
      (MeasureTheory.volume.restrict (Ici 0)))
    {C rate : ℝ} (hrate : 0 < rate)
    (hDecay : ∀ t ∈ Ici (0 : ℝ),
      normalizedFlowTracelessRicciEnergyTrack gt t ≤
        C * Real.exp ((-rate) * t))
    (metric : K → ClosedSmoothRiemannianMetric 3 M)
    (parameter : Ici (0 : ℝ) → K)
    (hRealize : ∀ t : Ici (0 : ℝ), metric (parameter t) = gt t.1)
    (hInvariantContinuous :
      Continuous (fun k ↦ closedMetricMeanTracelessEnergyPair (metric k)))
    {c : ℝ} (hc : 0 < c)
    (hMeanLower : ∀ t : Ici (0 : ℝ), c ≤ meanScalar (gt t.1)) :
    PositiveEinsteinMetric3 M := by
  apply
    positiveEinsteinMetric3_of_finiteTracelessRicciEnergy_Ici_of_compact_meanEnergy_parameterization_of_meanLower
      gt
      (normalizedFlowTracelessRicciEnergyTrack_integrableOn_of_exponential_bound
        gt hMeasurable hrate hDecay)
      metric parameter hRealize hInvariantContinuous hc hMeanLower

/-- Exponential traceless-energy decay feeds directly into the compact
mean-energy unit-curvature endpoint. -/
theorem exists_unitConstantCurvature_of_exponentialTracelessRicciEnergyDecay_of_compact_meanEnergy_parameterization_of_meanLower
    [Nonempty M] [SimplyConnectedSpace M]
    {K : Type v} [TopologicalSpace K] [CompactSpace K]
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    (hMeasurable : AEStronglyMeasurable
      (normalizedFlowTracelessRicciEnergyTrack gt)
      (MeasureTheory.volume.restrict (Ici 0)))
    {C rate : ℝ} (hrate : 0 < rate)
    (hDecay : ∀ t ∈ Ici (0 : ℝ),
      normalizedFlowTracelessRicciEnergyTrack gt t ≤
        C * Real.exp ((-rate) * t))
    (metric : K → ClosedSmoothRiemannianMetric 3 M)
    (parameter : Ici (0 : ℝ) → K)
    (hRealize : ∀ t : Ici (0 : ℝ), metric (parameter t) = gt t.1)
    (hInvariantContinuous :
      Continuous (fun k ↦ closedMetricMeanTracelessEnergyPair (metric k)))
    {c : ℝ} (hc : 0 < c)
    (hMeanLower : ∀ t : Ici (0 : ℝ), c ≤ meanScalar (gt t.1)) :
    ∃ g' : ClosedSmoothRiemannianMetric 3 M,
      HasConstantSectionalCurvature3 g' 1 := by
  apply
    exists_unitConstantCurvature_of_finiteTracelessRicciEnergy_Ici_of_compact_meanEnergy_parameterization_of_meanLower
      gt
      (normalizedFlowTracelessRicciEnergyTrack_integrableOn_of_exponential_bound
        gt hMeasurable hrate hDecay)
      metric parameter hRealize hInvariantContinuous hc hMeanLower

/-- With the explicit unit-curvature recognition boundary, exponential
traceless-energy decay feeds directly into the compact mean-energy sphere
endpoint. -/
theorem sphereConclusion_of_exponentialTracelessRicciEnergyDecay_of_compact_meanEnergy_parameterization_of_meanLower
    [Nonempty M] [SimplyConnectedSpace M]
    {K : Type v} [TopologicalSpace K] [CompactSpace K]
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    (hMeasurable : AEStronglyMeasurable
      (normalizedFlowTracelessRicciEnergyTrack gt)
      (MeasureTheory.volume.restrict (Ici 0)))
    {C rate : ℝ} (hrate : 0 < rate)
    (hDecay : ∀ t ∈ Ici (0 : ℝ),
      normalizedFlowTracelessRicciEnergyTrack gt t ≤
        C * Real.exp ((-rate) * t))
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
  apply
    sphereConclusion_of_finiteTracelessRicciEnergy_Ici_of_compact_meanEnergy_parameterization_of_meanLower
      gt
      (normalizedFlowTracelessRicciEnergyTrack_integrableOn_of_exponential_bound
        gt hMeasurable hrate hDecay)
      metric parameter hRealize hInvariantContinuous hc hMeanLower hUnit

end Poincare
