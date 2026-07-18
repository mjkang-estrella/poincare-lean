import Poincare.Global.NormalizedFlowForwardTracelessEnergyDecay
import Poincare.Global.NormalizedFlowForwardAbsoluteDissipation

/-!
# Pointwise decay produces finite forward traceless-Ricci energy

A uniform pointwise exponential bound for squared traceless Ricci curvature
becomes an exponential bound for its total energy after integration.  For a
normalized closed Ricci flow the total volume is constant on the forward ray,
so the resulting coefficient is the initial volume times the pointwise
coefficient.

This module isolates that short measure-theoretic bridge.  The moving-volume
first-variation hypothesis is retained explicitly; no differentiation of the
Hausdorff-defined volume measure is inferred automatically.
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

omit [SecondCountableTopology M] in
/-- Integrating a spatially constant upper bound multiplies it by the real
total Riemannian volume. -/
theorem normalizedFlowTracelessRicciEnergyTrack_le_mul_totalVolume_of_pointwise
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M) (t B : ℝ)
    (hPointwise : ∀ x : M,
      (gt t).tracelessRicciNormSqAt x ≤ B) :
    normalizedFlowTracelessRicciEnergyTrack gt t ≤
      B * totalVolume (gt t) := by
  letI : IsFiniteMeasure (volumeMeasure (gt t)) :=
    volumeMeasure_isFiniteMeasure (gt t)
  unfold normalizedFlowTracelessRicciEnergyTrack
  calc
    (∫ x, (gt t).tracelessRicciNormSqAt x ∂(volumeMeasure (gt t))) ≤
        ∫ _x : M, B ∂(volumeMeasure (gt t)) := by
      exact integral_mono
        (tracelessRicciNormSqAt_integrable (gt t))
        (integrable_const B) hPointwise
    _ = B * totalVolume (gt t) := by
      rw [integral_const]
      simp only [Measure.real, totalVolume]
      change ((volumeMeasure (gt t)) univ).toReal * B =
        B * ((volumeMeasure (gt t)) univ).toReal
      ring

/-- Forward volume preservation converts a uniform pointwise exponential
curvature bound into the total-energy exponential envelope consumed by the
finite-energy endpoint. -/
theorem normalizedFlowTracelessRicciEnergyTrack_le_initialVolume_mul_exp_of_pointwise_of_normalizedFlow_Ici
    [Nonempty M]
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    (hFlow : ∀ t ∈ Ici (0 : ℝ), ∀ x : M,
      IsClosedNormalizedRicciFlowSolutionAt gt t x)
    (hVolumeVariation : ∀ t ∈ Ici (0 : ℝ),
      HasDerivAt (fun s ↦ totalVolume (gt s))
        (totalVolumeFirstVariation (gt t) (timeDerivAt gt t)) t)
    {A rate : ℝ}
    (hPointwiseDecay : ∀ t ∈ Ici (0 : ℝ), ∀ x : M,
      (gt t).tracelessRicciNormSqAt x ≤
        A * Real.exp ((-rate) * t)) :
    ∀ t ∈ Ici (0 : ℝ),
      normalizedFlowTracelessRicciEnergyTrack gt t ≤
        (A * totalVolume (gt 0)) * Real.exp ((-rate) * t) := by
  intro t ht
  have hVolume : totalVolume (gt t) = totalVolume (gt 0) :=
    totalVolume_eq_of_closedNormalizedRicciFlow_Ici
      hFlow hVolumeVariation ht (by simp)
  calc
    normalizedFlowTracelessRicciEnergyTrack gt t ≤
        (A * Real.exp ((-rate) * t)) * totalVolume (gt t) :=
      normalizedFlowTracelessRicciEnergyTrack_le_mul_totalVolume_of_pointwise
        gt t (A * Real.exp ((-rate) * t))
          (hPointwiseDecay t ht)
    _ = (A * totalVolume (gt 0)) * Real.exp ((-rate) * t) := by
      rw [hVolume]
      ring

/-- A measurable total-energy track and uniform pointwise exponential decay
give finite forward total traceless-Ricci energy for a normalized flow. -/
theorem normalizedFlowTracelessRicciEnergyTrack_integrableOn_of_pointwise_exponential_decay_of_normalizedFlow_Ici
    [Nonempty M]
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    (hFlow : ∀ t ∈ Ici (0 : ℝ), ∀ x : M,
      IsClosedNormalizedRicciFlowSolutionAt gt t x)
    (hVolumeVariation : ∀ t ∈ Ici (0 : ℝ),
      HasDerivAt (fun s ↦ totalVolume (gt s))
        (totalVolumeFirstVariation (gt t) (timeDerivAt gt t)) t)
    (hMeasurable : AEStronglyMeasurable
      (normalizedFlowTracelessRicciEnergyTrack gt)
      (MeasureTheory.volume.restrict (Ici 0)))
    {A rate : ℝ} (hrate : 0 < rate)
    (hPointwiseDecay : ∀ t : Ici (0 : ℝ), ∀ x : M,
      (gt t.1).tracelessRicciNormSqAt x ≤
        A * Real.exp ((-rate) * t.1)) :
    IntegrableOn (normalizedFlowTracelessRicciEnergyTrack gt) (Ici 0) := by
  apply normalizedFlowTracelessRicciEnergyTrack_integrableOn_of_exponential_bound
    gt hMeasurable hrate
  intro t ht
  exact
    normalizedFlowTracelessRicciEnergyTrack_le_initialVolume_mul_exp_of_pointwise_of_normalizedFlow_Ici
      gt hFlow hVolumeVariation
        (fun s hs x ↦ hPointwiseDecay ⟨s, hs⟩ x) t ht

end Poincare
