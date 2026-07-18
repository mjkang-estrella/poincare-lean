import Poincare.Global.NormalizedFlowDissipationDifferentialDecay
import Poincare.Global.NormalizedFlowForwardPointwiseTracelessEnergyDecay
import Poincare.Global.NormalizedFlowPinchingLimit

/-!
# Maximum-track differential decay produces pointwise traceless-Ricci decay

The pointwise exponential hypothesis used by the forward finite-energy route
is stronger than necessary as an input.  On a compact manifold every
pointwise squared traceless-Ricci norm is bounded by its spatial maximum.  An
integrating-factor argument therefore reduces the whole pointwise family to
one scalar coercive differential inequality for that maximum track.

This is a genuine reduction: neither a pointwise exponential envelope nor a
separate initial coefficient is assumed.  The coefficient is the actual
initial spatial maximum, and the exponential estimate is proved from the
maximum-track derivative inequality.
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

/-- A scalar coercive differential inequality for the actual spatial maximum
of squared traceless Ricci yields the uniform pointwise exponential estimate.

The derivative witness is stated separately because a spatial supremum need
not be differentiable from joint continuity alone; a future parabolic
maximum-principle layer can discharge precisely this maximum-track premise. -/
theorem
    tracelessRicciNormSqAt_le_initialMaximum_mul_exp_of_maximum_differential_decay
    [Nonempty M]
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    (maximumDerivative : ℝ → ℝ) {rate : ℝ}
    (hMaximumDerivative : ∀ t ∈ Ici (0 : ℝ),
      HasDerivAt (fun s ↦ tracelessRicciMaximumAt (gt s))
        (maximumDerivative t) t)
    (hMaximumDifferentialInequality : ∀ t ∈ Ici (0 : ℝ),
      maximumDerivative t ≤
        -rate * tracelessRicciMaximumAt (gt t)) :
    ∀ t : Ici (0 : ℝ), ∀ x : M,
      (gt t.1).tracelessRicciNormSqAt x ≤
        tracelessRicciMaximumAt (gt 0) *
          Real.exp ((-rate) * t.1) := by
  intro t x
  calc
    (gt t.1).tracelessRicciNormSqAt x ≤
        tracelessRicciMaximumAt (gt t.1) :=
      tracelessRicciNormSqAt_le_tracelessRicciMaximumAt (gt t.1) x
    _ ≤ tracelessRicciMaximumAt (gt 0) *
          Real.exp ((-rate) * t.1) :=
      le_initial_mul_exp_neg_of_hasDerivAt_le_neg_mul
        (fun s ↦ tracelessRicciMaximumAt (gt s)) maximumDerivative
          hMaximumDerivative hMaximumDifferentialInequality t.2

/-- The maximum-track coercive differential inequality feeds the normalized
flow finite-energy endpoint directly.  The only decay coefficient used after
integration is the genuine initial spatial maximum. -/
theorem
    normalizedFlowTracelessRicciEnergyTrack_integrableOn_of_maximum_differential_decay_of_normalizedFlow_Ici
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
    (maximumDerivative : ℝ → ℝ) {rate : ℝ} (hrate : 0 < rate)
    (hMaximumDerivative : ∀ t ∈ Ici (0 : ℝ),
      HasDerivAt (fun s ↦ tracelessRicciMaximumAt (gt s))
        (maximumDerivative t) t)
    (hMaximumDifferentialInequality : ∀ t ∈ Ici (0 : ℝ),
      maximumDerivative t ≤
        -rate * tracelessRicciMaximumAt (gt t)) :
    IntegrableOn (normalizedFlowTracelessRicciEnergyTrack gt) (Ici 0) := by
  apply
    normalizedFlowTracelessRicciEnergyTrack_integrableOn_of_pointwise_exponential_decay_of_normalizedFlow_Ici
      gt hFlow hVolumeVariation hMeasurable hrate
  exact
    tracelessRicciNormSqAt_le_initialMaximum_mul_exp_of_maximum_differential_decay
      gt maximumDerivative hMaximumDerivative
        hMaximumDifferentialInequality

end Poincare
