import Poincare.Global.NormalizedFlowForwardTracelessEnergyDecay
import Poincare.Global.NormalizedFlowDissipationDifferentialDecay

/-!
# Forward differential decay of traceless-Ricci energy

A coercive scalar differential inequality for the actual total squared
traceless-Ricci energy implies its exponential decay from time zero.  The
forward exponential-decay producer then gives finite total time-energy and
feeds the compact mean-energy positive-Einstein endpoint.

Only the one-dimensional energy track is differentiated here.  No Ricci-flow
equation, moving spatial-integral differentiation, or scalar-variance premise
is used.
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
/-- A coercive differential inequality gives the explicit exponential
envelope for the forward traceless-Ricci energy. -/
theorem normalizedFlowTracelessRicciEnergyTrack_le_initial_mul_exp_neg_of_differential_decay
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    (E' : ℝ → ℝ) {rate : ℝ}
    (hDeriv : ∀ t ∈ Ici (0 : ℝ),
      HasDerivAt (normalizedFlowTracelessRicciEnergyTrack gt) (E' t) t)
    (hDifferentialInequality : ∀ t ∈ Ici (0 : ℝ),
      E' t ≤ -rate * normalizedFlowTracelessRicciEnergyTrack gt t)
    {t : ℝ} (ht : 0 ≤ t) :
    normalizedFlowTracelessRicciEnergyTrack gt t ≤
      normalizedFlowTracelessRicciEnergyTrack gt 0 *
        Real.exp ((-rate) * t) :=
  le_initial_mul_exp_neg_of_hasDerivAt_le_neg_mul
    (normalizedFlowTracelessRicciEnergyTrack gt) E'
    hDeriv hDifferentialInequality ht

omit [SecondCountableTopology M] in
/-- A positive-rate coercive differential inequality makes the forward
traceless-Ricci energy integrable. -/
theorem normalizedFlowTracelessRicciEnergyTrack_integrableOn_of_differential_decay
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    (E' : ℝ → ℝ) {rate : ℝ} (hrate : 0 < rate)
    (hDeriv : ∀ t ∈ Ici (0 : ℝ),
      HasDerivAt (normalizedFlowTracelessRicciEnergyTrack gt) (E' t) t)
    (hDifferentialInequality : ∀ t ∈ Ici (0 : ℝ),
      E' t ≤ -rate * normalizedFlowTracelessRicciEnergyTrack gt t) :
    IntegrableOn (normalizedFlowTracelessRicciEnergyTrack gt) (Ici 0) := by
  have hContinuous : ContinuousOn
      (normalizedFlowTracelessRicciEnergyTrack gt) (Ici (0 : ℝ)) := by
    intro t ht
    exact (hDeriv t ht).continuousAt.continuousWithinAt
  apply
    normalizedFlowTracelessRicciEnergyTrack_integrableOn_of_continuousOn_of_exponential_bound
      gt hContinuous hrate
  intro t ht
  exact
    normalizedFlowTracelessRicciEnergyTrack_le_initial_mul_exp_neg_of_differential_decay
      gt E' hDeriv hDifferentialInequality ht

/-- Differential traceless-energy decay feeds directly into the compact
mean-energy positive-Einstein endpoint. -/
theorem positiveEinsteinMetric3_of_differentialTracelessRicciEnergyDecay_of_compact_meanEnergy_parameterization_of_meanLower
    [Nonempty M] [SimplyConnectedSpace M]
    {K : Type v} [TopologicalSpace K] [CompactSpace K]
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    (E' : ℝ → ℝ) {rate : ℝ} (hrate : 0 < rate)
    (hDeriv : ∀ t ∈ Ici (0 : ℝ),
      HasDerivAt (normalizedFlowTracelessRicciEnergyTrack gt) (E' t) t)
    (hDifferentialInequality : ∀ t ∈ Ici (0 : ℝ),
      E' t ≤ -rate * normalizedFlowTracelessRicciEnergyTrack gt t)
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
      (normalizedFlowTracelessRicciEnergyTrack_integrableOn_of_differential_decay
        gt E' hrate hDeriv hDifferentialInequality)
      metric parameter hRealize hInvariantContinuous hc hMeanLower

/-- Differential traceless-energy decay feeds directly into the compact
mean-energy unit-curvature endpoint. -/
theorem exists_unitConstantCurvature_of_differentialTracelessRicciEnergyDecay_of_compact_meanEnergy_parameterization_of_meanLower
    [Nonempty M] [SimplyConnectedSpace M]
    {K : Type v} [TopologicalSpace K] [CompactSpace K]
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    (E' : ℝ → ℝ) {rate : ℝ} (hrate : 0 < rate)
    (hDeriv : ∀ t ∈ Ici (0 : ℝ),
      HasDerivAt (normalizedFlowTracelessRicciEnergyTrack gt) (E' t) t)
    (hDifferentialInequality : ∀ t ∈ Ici (0 : ℝ),
      E' t ≤ -rate * normalizedFlowTracelessRicciEnergyTrack gt t)
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
      (normalizedFlowTracelessRicciEnergyTrack_integrableOn_of_differential_decay
        gt E' hrate hDeriv hDifferentialInequality)
      metric parameter hRealize hInvariantContinuous hc hMeanLower

/-- With the explicit unit-curvature recognition boundary, differential
traceless-energy decay feeds directly into the compact mean-energy sphere
endpoint. -/
theorem sphereConclusion_of_differentialTracelessRicciEnergyDecay_of_compact_meanEnergy_parameterization_of_meanLower
    [Nonempty M] [SimplyConnectedSpace M]
    {K : Type v} [TopologicalSpace K] [CompactSpace K]
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    (E' : ℝ → ℝ) {rate : ℝ} (hrate : 0 < rate)
    (hDeriv : ∀ t ∈ Ici (0 : ℝ),
      HasDerivAt (normalizedFlowTracelessRicciEnergyTrack gt) (E' t) t)
    (hDifferentialInequality : ∀ t ∈ Ici (0 : ℝ),
      E' t ≤ -rate * normalizedFlowTracelessRicciEnergyTrack gt t)
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
      (normalizedFlowTracelessRicciEnergyTrack_integrableOn_of_differential_decay
        gt E' hrate hDeriv hDifferentialInequality)
      metric parameter hRealize hInvariantContinuous hc hMeanLower hUnit

end Poincare
