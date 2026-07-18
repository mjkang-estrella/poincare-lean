import Poincare.Global.ClosedRiemannianParabolicExponentialMaximum
import Poincare.Global.NormalizedFlowForwardPointwiseTracelessEnergyDecay
import Poincare.Global.NormalizedFlowPinchingLimit
import Poincare.Global.NormalizedFlowInvariantPairJointContinuity
import Poincare.Global.NormalizedFlowJointPinchingRegularity

/-!
# Pointwise traceless-Ricci decay from a parabolic inequality

The spatial-maximum ODE route still required differentiability of the
supremum track.  Here the compact parabolic maximum principle removes that
assumption.  A pointwise coercive inequality

`∂ₜ |Ric°|² ≤ Δ |Ric°|² - rate * |Ric°|²`

together with slab continuity and spatial `C²` regularity yields the uniform
exponential estimate with the actual initial spatial maximum as coefficient.
The existing normalized-volume argument then makes the total traceless energy
integrable on forward time.
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

local notation "I" => closedSmoothModelWithCorners 3

/-- The pointwise coercive parabolic inequality proves uniform exponential
traceless-Ricci decay without differentiating the spatial maximum. -/
theorem
    tracelessRicciNormSqAt_le_initialMaximum_mul_exp_of_parabolic_decay_Ici
    [Nonempty M]
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (pointwiseDerivative : ℝ → M → ℝ) {rate : ℝ}
    (hJointContinuous : ∀ T : ℝ, 0 ≤ T →
      ContinuousOn
        (Function.uncurry
          (fun t x ↦ (gt t).tracelessRicciNormSqAt x))
        (Icc (0 : ℝ) T ×ˢ (Set.univ : Set M)))
    (hDerivative : ∀ x : M, ∀ t ∈ Ici (0 : ℝ),
      HasDerivAt (fun s ↦ (gt s).tracelessRicciNormSqAt x)
        (pointwiseDerivative t x) t)
    (hSpatialC2 : ∀ t ∈ Ici (0 : ℝ), ∀ x : M,
      ContMDiffAt I 𝓘(ℝ) 2
        (fun y : M ↦ (gt t).tracelessRicciNormSqAt y) x)
    (hParabolic : ∀ t ∈ Ici (0 : ℝ), ∀ x : M,
      pointwiseDerivative t x ≤
        (gt t).laplacianAt
            (fun y : M ↦ (gt t).tracelessRicciNormSqAt y) x -
          rate * (gt t).tracelessRicciNormSqAt x) :
    ∀ t : Ici (0 : ℝ), ∀ x : M,
      (gt t.1).tracelessRicciNormSqAt x ≤
        tracelessRicciMaximumAt (gt 0) *
          Real.exp ((-rate) * t.1) := by
  apply closedRiemannian_parabolic_exp_decay_Ici
    gt
    (fun t x ↦ (gt t).tracelessRicciNormSqAt x)
    pointwiseDerivative hJointContinuous hDerivative hSpatialC2 hParabolic
  intro x
  exact tracelessRicciNormSqAt_le_tracelessRicciMaximumAt (gt 0) x

/-- The parabolic maximum-principle producer feeds the forward normalized-flow
finite-energy theorem directly. -/
theorem
    normalizedFlowTracelessRicciEnergyTrack_integrableOn_of_parabolic_decay_of_normalizedFlow_Ici
    [Nonempty M]
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hFlow : ∀ t ∈ Ici (0 : ℝ), ∀ x : M,
      IsClosedNormalizedRicciFlowSolutionAt gt t x)
    (hVolumeVariation : ∀ t ∈ Ici (0 : ℝ),
      HasDerivAt (fun s ↦ totalVolume (gt s))
        (totalVolumeFirstVariation (gt t) (timeDerivAt gt t)) t)
    (hMeasurable : AEStronglyMeasurable
      (normalizedFlowTracelessRicciEnergyTrack gt)
      (MeasureTheory.volume.restrict (Ici 0)))
    (pointwiseDerivative : ℝ → M → ℝ) {rate : ℝ}
    (hrate : 0 < rate)
    (hJointContinuous : ∀ T : ℝ, 0 ≤ T →
      ContinuousOn
        (Function.uncurry
          (fun t x ↦ (gt t).tracelessRicciNormSqAt x))
        (Icc (0 : ℝ) T ×ˢ (Set.univ : Set M)))
    (hDerivative : ∀ x : M, ∀ t ∈ Ici (0 : ℝ),
      HasDerivAt (fun s ↦ (gt s).tracelessRicciNormSqAt x)
        (pointwiseDerivative t x) t)
    (hSpatialC2 : ∀ t ∈ Ici (0 : ℝ), ∀ x : M,
      ContMDiffAt I 𝓘(ℝ) 2
        (fun y : M ↦ (gt t).tracelessRicciNormSqAt y) x)
    (hParabolic : ∀ t ∈ Ici (0 : ℝ), ∀ x : M,
      pointwiseDerivative t x ≤
        (gt t).laplacianAt
            (fun y : M ↦ (gt t).tracelessRicciNormSqAt y) x -
          rate * (gt t).tracelessRicciNormSqAt x) :
    IntegrableOn (normalizedFlowTracelessRicciEnergyTrack gt) (Ici 0) := by
  apply
    normalizedFlowTracelessRicciEnergyTrack_integrableOn_of_pointwise_exponential_decay_of_normalizedFlow_Ici
      gt hFlow hVolumeVariation hMeasurable hrate
  exact
    tracelessRicciNormSqAt_le_initialMaximum_mul_exp_of_parabolic_decay_Ici
      gt pointwiseDerivative hJointContinuous hDerivative hSpatialC2
        hParabolic

/-- Forward normalized flow and joint `C³` metric entries automatically
supply the slab continuity and spatial `C²` hypotheses of the parabolic
maximum comparison.  The remaining decay datum is only the actual pointwise
coercive evolution inequality. -/
theorem
    tracelessRicciNormSqAt_le_initialMaximum_mul_exp_of_parabolic_decay_of_normalizedFlow_jointMetricEntries_Ici
    [Nonempty M]
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hFlow : ∀ t ∈ Ici (0 : ℝ), ∀ x : M,
      IsClosedNormalizedRicciFlowSolutionAt gt t x)
    (hJointMetricEntries : ∀ t ∈ Ici (0 : ℝ), ∀ x : M,
      MetricEntriesJointContDiffAt gt t x 3)
    (pointwiseDerivative : ℝ → M → ℝ) {rate : ℝ}
    (hDerivative : ∀ x : M, ∀ t ∈ Ici (0 : ℝ),
      HasDerivAt (fun s ↦ (gt s).tracelessRicciNormSqAt x)
        (pointwiseDerivative t x) t)
    (hParabolic : ∀ t ∈ Ici (0 : ℝ), ∀ x : M,
      pointwiseDerivative t x ≤
        (gt t).laplacianAt
            (fun y : M ↦ (gt t).tracelessRicciNormSqAt y) x -
          rate * (gt t).tracelessRicciNormSqAt x) :
    ∀ t : Ici (0 : ℝ), ∀ x : M,
      (gt t.1).tracelessRicciNormSqAt x ≤
        tracelessRicciMaximumAt (gt 0) *
          Real.exp ((-rate) * t.1) := by
  apply
    tracelessRicciNormSqAt_le_initialMaximum_mul_exp_of_parabolic_decay_Ici
      gt pointwiseDerivative
  · intro T hT
    intro p hp
    have hRic :=
      continuousAt_ricciNormSqAt_joint_of_metricEntriesJointContDiffAt_three
        (hJointMetricEntries p.1 hp.1.1 p.2)
    have hScalar :=
      continuousAt_scalarAt_joint_of_metricEntriesJointContDiffAt_three
        (hJointMetricEntries p.1 hp.1.1 p.2)
    exact (by
      simpa [Function.uncurry,
        ClosedSmoothRiemannianMetric.tracelessRicciNormSqAt] using
          (hRic.sub ((hScalar.pow 2).div_const 3)).continuousWithinAt)
  · exact hDerivative
  · intro t ht x
    exact
      contMDiffAt_two_tracelessRicciNormSqAt_of_normalizedRicciFlow_joint_metric_entries_three
        x (hFlow t ht) (hJointMetricEntries t ht)
  · exact hParabolic

/-- Consequently, joint `C³` forward normalized-flow regularity plus the
pointwise coercive parabolic inequality imply finite total traceless-Ricci
energy. -/
theorem
    normalizedFlowTracelessRicciEnergyTrack_integrableOn_of_parabolic_decay_of_normalizedFlow_jointMetricEntries_Ici
    [Nonempty M]
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hFlow : ∀ t ∈ Ici (0 : ℝ), ∀ x : M,
      IsClosedNormalizedRicciFlowSolutionAt gt t x)
    (hVolumeVariation : ∀ t ∈ Ici (0 : ℝ),
      HasDerivAt (fun s ↦ totalVolume (gt s))
        (totalVolumeFirstVariation (gt t) (timeDerivAt gt t)) t)
    (hMeasurable : AEStronglyMeasurable
      (normalizedFlowTracelessRicciEnergyTrack gt)
      (MeasureTheory.volume.restrict (Ici 0)))
    (hJointMetricEntries : ∀ t ∈ Ici (0 : ℝ), ∀ x : M,
      MetricEntriesJointContDiffAt gt t x 3)
    (pointwiseDerivative : ℝ → M → ℝ) {rate : ℝ}
    (hrate : 0 < rate)
    (hDerivative : ∀ x : M, ∀ t ∈ Ici (0 : ℝ),
      HasDerivAt (fun s ↦ (gt s).tracelessRicciNormSqAt x)
        (pointwiseDerivative t x) t)
    (hParabolic : ∀ t ∈ Ici (0 : ℝ), ∀ x : M,
      pointwiseDerivative t x ≤
        (gt t).laplacianAt
            (fun y : M ↦ (gt t).tracelessRicciNormSqAt y) x -
          rate * (gt t).tracelessRicciNormSqAt x) :
    IntegrableOn (normalizedFlowTracelessRicciEnergyTrack gt) (Ici 0) := by
  apply
    normalizedFlowTracelessRicciEnergyTrack_integrableOn_of_pointwise_exponential_decay_of_normalizedFlow_Ici
      gt hFlow hVolumeVariation hMeasurable hrate
  exact
    tracelessRicciNormSqAt_le_initialMaximum_mul_exp_of_parabolic_decay_of_normalizedFlow_jointMetricEntries_Ici
      gt hFlow hJointMetricEntries pointwiseDerivative hDerivative hParabolic

end Poincare
