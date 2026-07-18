import Poincare.Global.NormalizedFlowForwardPointwiseTracelessEnergyParabolicDecay

/-!
# Forward traceless-Ricci decay from reaction domination

The parabolic maximum-principle route can expose the geometric obstruction
more sharply than an arbitrary pointwise differential inequality.  If the
actual evolution has the form

`∂ₜ |Ric°|² = Δ |Ric°|² + reaction`

and the reaction is bounded above by `-rate * |Ric°|²`, then the coercive
parabolic inequality is automatic.  This file performs that reduction and
feeds it into the verified exponential-decay and finite-energy theorems.

Thus the remaining analytic datum is a curvature-reaction estimate, rather
than a separately chosen derivative or a prepackaged decay assertion.
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

/-- An exact Laplacian-plus-reaction evolution and coercive reaction bound
give the pointwise parabolic inequality used by the maximum principle. -/
theorem tracelessRicci_parabolic_inequality_of_reaction_domination_Ici
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    (reaction : ℝ → M → ℝ) {rate : ℝ}
    (hReaction : ∀ t ∈ Ici (0 : ℝ), ∀ x : M,
      reaction t x ≤ -rate * (gt t).tracelessRicciNormSqAt x) :
    ∀ t ∈ Ici (0 : ℝ), ∀ x : M,
      (gt t).laplacianAt
            (fun y : M ↦ (gt t).tracelessRicciNormSqAt y) x +
          reaction t x ≤
        (gt t).laplacianAt
            (fun y : M ↦ (gt t).tracelessRicciNormSqAt y) x -
          rate * (gt t).tracelessRicciNormSqAt x := by
  intro t ht x
  have h := hReaction t ht x
  linarith

/-- Exact traceless-Ricci evolution plus coercive reaction domination yields
uniform exponential pointwise decay.  Forward normalized flow and joint
`C³` metric entries automatically supply all space-time regularity used by the
compact parabolic maximum principle. -/
theorem
    tracelessRicciNormSqAt_le_initialMaximum_mul_exp_of_reaction_domination_of_normalizedFlow_jointMetricEntries_Ici
    [Nonempty M]
    (gt : ℝ → ClosedSmoothRiemannianMetric 3 M)
    [∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (gt t).leviCivita 1]
    (hFlow : ∀ t ∈ Ici (0 : ℝ), ∀ x : M,
      IsClosedNormalizedRicciFlowSolutionAt gt t x)
    (hJointMetricEntries : ∀ t ∈ Ici (0 : ℝ), ∀ x : M,
      MetricEntriesJointContDiffAt gt t x 3)
    (reaction : ℝ → M → ℝ) {rate : ℝ}
    (hEvolution : ∀ x : M, ∀ t ∈ Ici (0 : ℝ),
      HasDerivAt (fun s ↦ (gt s).tracelessRicciNormSqAt x)
        ((gt t).laplacianAt
            (fun y : M ↦ (gt t).tracelessRicciNormSqAt y) x +
          reaction t x) t)
    (hReaction : ∀ t ∈ Ici (0 : ℝ), ∀ x : M,
      reaction t x ≤ -rate * (gt t).tracelessRicciNormSqAt x) :
    ∀ t : Ici (0 : ℝ), ∀ x : M,
      (gt t.1).tracelessRicciNormSqAt x ≤
        tracelessRicciMaximumAt (gt 0) *
          Real.exp ((-rate) * t.1) := by
  apply
    tracelessRicciNormSqAt_le_initialMaximum_mul_exp_of_parabolic_decay_of_normalizedFlow_jointMetricEntries_Ici
      gt hFlow hJointMetricEntries
      (fun t x ↦
        (gt t).laplacianAt
            (fun y : M ↦ (gt t).tracelessRicciNormSqAt y) x +
          reaction t x)
  · exact hEvolution
  · exact
      tracelessRicci_parabolic_inequality_of_reaction_domination_Ici
        gt reaction hReaction

/-- Consequently, exact Laplacian-plus-reaction evolution and a positive-rate
coercive reaction estimate imply finite total forward traceless-Ricci energy.
-/
theorem
    normalizedFlowTracelessRicciEnergyTrack_integrableOn_of_reaction_domination_of_normalizedFlow_jointMetricEntries_Ici
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
    (reaction : ℝ → M → ℝ) {rate : ℝ}
    (hrate : 0 < rate)
    (hEvolution : ∀ x : M, ∀ t ∈ Ici (0 : ℝ),
      HasDerivAt (fun s ↦ (gt s).tracelessRicciNormSqAt x)
        ((gt t).laplacianAt
            (fun y : M ↦ (gt t).tracelessRicciNormSqAt y) x +
          reaction t x) t)
    (hReaction : ∀ t ∈ Ici (0 : ℝ), ∀ x : M,
      reaction t x ≤ -rate * (gt t).tracelessRicciNormSqAt x) :
    IntegrableOn (normalizedFlowTracelessRicciEnergyTrack gt) (Ici 0) := by
  apply
    normalizedFlowTracelessRicciEnergyTrack_integrableOn_of_parabolic_decay_of_normalizedFlow_jointMetricEntries_Ici
      gt hFlow hVolumeVariation hMeasurable hJointMetricEntries
      (fun t x ↦
        (gt t).laplacianAt
            (fun y : M ↦ (gt t).tracelessRicciNormSqAt y) x +
          reaction t x)
      hrate
  · exact hEvolution
  · exact
      tracelessRicci_parabolic_inequality_of_reaction_domination_Ici
        gt reaction hReaction

end Poincare
