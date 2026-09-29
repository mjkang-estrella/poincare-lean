import Poincare.Global.HamiltonScalarGradientQuotientBound
import Poincare.Global.MetricFlowJointPinchingEvolution

noncomputable section
open scoped Manifold ContDiff Topology
set_option autoImplicit false
universe u

namespace Poincare.HamiltonScalarGradientAuxiliaryEstimate

variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (ClosedSmoothModel 3) M]
  [IsManifold (closedSmoothModelWithCorners 3) ∞ M]

/-- The auxiliary combination uses genuine Laplacian linearity on a `C²` slice. -/
theorem laplacian_auxiliary_combination
    (g : ClosedSmoothRiemannianMetric 3 M) (x : M)
    (f h k : M → ℝ) (eta K : ℝ)
    (hf : ∀ y, ContMDiffAt (closedSmoothModelWithCorners 3) 𝓘(ℝ) 2 f y)
    (hh : ∀ y, ContMDiffAt (closedSmoothModelWithCorners 3) 𝓘(ℝ) 2 h y)
    (hk : ∀ y, ContMDiffAt (closedSmoothModelWithCorners 3) 𝓘(ℝ) 2 k y) :
    g.laplacianAt (fun y ↦ f y - eta * h y + K * k y) x =
      g.laplacianAt f x - eta * g.laplacianAt h x + K * g.laplacianAt k x := by
  have heq : (fun y ↦ f y - eta * h y + K * k y) =
      (f + (-eta) • h) + K • k := by
    funext y
    simp [sub_eq_add_neg]
  have hneg : ∀ y, ContMDiffAt (closedSmoothModelWithCorners 3) 𝓘(ℝ) 2
      ((-eta) • h) y := fun y ↦ contMDiffAt_const.smul (hh y)
  have hK : ∀ y, ContMDiffAt (closedSmoothModelWithCorners 3) 𝓘(ℝ) 2
      (K • k) y := fun y ↦ contMDiffAt_const.smul (hk y)
  rw [heq, g.laplacianAt_add' (fun y ↦ (hf y).add (hneg y)) hK,
    g.laplacianAt_add' hf hneg,
    g.laplacianAt_const_smul' (-eta) hh, g.laplacianAt_const_smul' K hk]
  ring

/-- The normalized auxiliary differential bound, with its mean-scalar term
retained and its derivative-energy terms cancelled by contracted Bianchi. -/
theorem auxiliary_evolution_le_cubic_of_normalizedFlow
    [CompactSpace M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M]
    [SecondCountableTopology M]
    {gt : ℝ → ClosedSmoothRiemannianMetric 3 M} {t : ℝ} (x : M) (eta : ℝ)
    (heta : 0 ≤ eta)
    (hJoint5 : ∀ s y, MetricEntriesJointContDiffAt gt s y 5)
    (hFlow : ∀ y, IsClosedNormalizedRicciFlowSolutionAt gt t y)
    (hRpos : ∀ y, 0 < (gt t).scalarAt y)
    (hq : (gt t).pinchingQuotientAt x ≤ 1) :
    let F : ℝ → M → ℝ := fun s y ↦
      (gt s).scalarGradNormSqAt y / (gt s).scalarAt y -
        eta * (gt s).scalarAt y ^ 2 +
        (84 + 60 * eta) * (gt s).tracelessRicciNormSqAt y
    deriv (fun s ↦ F s x) t -
      (gt t).laplacianAt (fun y ↦ F t y) x +
      (4 / 3 : ℝ) * meanScalar (gt t) * F t x ≤
      -(4 / 3 : ℝ) * eta * (gt t).scalarAt x ^ 3 +
        4 * (84 + 60 * eta) * (gt t).scalarAt x *
          (gt t).tracelessRicciNormSqAt x := by
  letI : Nonempty M := ⟨x⟩
  let g := gt t
  let Q : ℝ → M → ℝ := fun s y ↦ (gt s).scalarGradNormSqAt y / (gt s).scalarAt y
  let B : ℝ → M → ℝ := fun s y ↦ (gt s).scalarAt y ^ 2
  let U : ℝ → M → ℝ := fun s y ↦ (gt s).tracelessRicciNormSqAt y
  let K := 84 + 60 * eta
  have hJoint3 : ∀ s y, MetricEntriesJointContDiffAt gt s y 3 :=
    fun s y ↦ (hJoint5 s y).of_le (by norm_num)
  have hRthree := IntrinsicBochnerScalarGradient.scalar_contMDiff_three_of_metricEntries_five
    hJoint5 t
  have hRtwo : ∀ y, ContMDiffAt (closedSmoothModelWithCorners 3) 𝓘(ℝ) 2
      (fun z ↦ g.scalarAt z) y := fun y ↦ hRthree.contMDiffAt.of_le (by norm_num)
  have hStwo : ∀ y, ContMDiffAt (closedSmoothModelWithCorners 3) 𝓘(ℝ) 2
      (fun z ↦ g.scalarGradNormSqAt z) y :=
    IntrinsicBochnerScalarGradient.gradientNormSq_contMDiffAt_two g _ hRthree
  have hQtwo : ∀ y, ContMDiffAt (closedSmoothModelWithCorners 3) 𝓘(ℝ) 2 (Q t) y :=
    fun y ↦ (hStwo y).div₀ (hRtwo y) (hRpos y).ne'
  have hBtwo : ∀ y, ContMDiffAt (closedSmoothModelWithCorners 3) 𝓘(ℝ) 2 (B t) y := by
    intro y
    simpa [B, pow_two] using (hRtwo y).smul (hRtwo y)
  have hUtwo : ∀ y, ContMDiffAt (closedSmoothModelWithCorners 3) 𝓘(ℝ) 2 (U t) y :=
    fun y ↦ contMDiffAt_two_tracelessRicciNormSqAt g y
      (ricciNormSqAt_contMDiffAt_two_canonical g y) (hRtwo y)
  have hRd : SatisfiesNormalizedHamiltonScalarEvolutionAt gt t x :=
    satisfiesNormalizedHamiltonScalarEvolutionAt_of_normalizedFlow_of_globalLichnerowicz
      hFlow (globalLichnerowiczAssemblyRegularity_of_jointMetricEntriesThree hJoint3)
  have hSd := IntrinsicBochnerScalarGradient.satisfiesScalarGradientEvolutionAt_of_normalizedFlow
    (x := x) hJoint5 hFlow
  have hQd := hSd.div hRd (hRpos x).ne'
  have hBd := hasDerivAt_scalarAt_sq_of_satisfiesNormalizedHamiltonScalarEvolutionAt
    hRd hRtwo
  have hUd :=
    hasDerivAt_tracelessRicciNormSqAt_eq_laplacianAt_add_actualNormalizedReaction_of_global_jointMetricEntries
      (x := x) hFlow hJoint3
  have hderiv :
      deriv (fun s ↦ Q s x - eta * B s x + K * U s x) t =
      deriv (fun s ↦ Q s x) t - eta * deriv (fun s ↦ B s x) t +
        K * deriv (fun s ↦ U s x) t := by
    exact ((hQd.differentiableAt.hasDerivAt.sub
      (hBd.differentiableAt.hasDerivAt.const_mul eta)).add
      (hUd.differentiableAt.hasDerivAt.const_mul K)).deriv
  have hlap := laplacian_auxiliary_combination g x (Q t) (B t) (U t) eta K
    hQtwo hBtwo hUtwo
  have hBheat : deriv (fun s ↦ B s x) t - g.laplacianAt (B t) x =
      -2 * g.scalarGradNormSqAt x + 4 * g.scalarAt x * g.ricciNormSqAt x -
        (4 / 3 : ℝ) * meanScalar g * B t x := by
    rw [hBd.deriv]
    simp only [B, g]
    ring
  have hQheat := HamiltonScalarGradientQuotientBound.quotient_evolution_le_eight_covRicci
    x hJoint5 hFlow hRpos
  have hUheat := HamiltonScalarGradientEstimate.tracelessEnergy_evolution_damped
    x hJoint3 hFlow
  have hBianchi := HamiltonScalarGradientEstimate.scalarGradNormSq_le_twentySevenths_covRicciNormSq g x
  have hCubic := HamiltonScalarGradientEstimate.cubic_reaction_le_four_scalar_mul_traceless
    g x (hRpos x) hq
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hKheat := mul_le_mul_of_nonneg_left hUheat hK
  have hKT := mul_le_mul_of_nonneg_left hCubic hK
  have hS := mul_le_mul_of_nonneg_left hBianchi (show 0 ≤ 2 * eta by positivity)
  have hRN := mul_le_mul_of_nonneg_left
    (g.scalarAt_sq_le_nat_mul_ricciNormSqAt x)
    (show 0 ≤ eta * g.scalarAt x by exact mul_nonneg heta (hRpos x).le)
  dsimp only
  change deriv (fun s ↦ Q s x - eta * B s x + K * U s x) t -
    g.laplacianAt (fun y ↦ Q t y - eta * B t y + K * U t y) x +
    (4 / 3 : ℝ) * meanScalar g * (Q t x - eta * B t x + K * U t x) ≤ _
  rw [hderiv, hlap]
  change deriv (fun s ↦ Q s x) t - g.laplacianAt (Q t) x ≤
    8 * covRicciNormSqAt g x - (4 / 3 : ℝ) * meanScalar g * Q t x at hQheat
  change deriv (fun s ↦ U s x) t - g.laplacianAt (U t) x ≤ _ at hUheat
  change K * (deriv (fun s ↦ U s x) t - g.laplacianAt (U t) x) ≤
    K * (-(2 / 21 : ℝ) * covRicciNormSqAt g x +
      g.pinchingTracelessRicciReactionTrace3At x
        (g.pinchingRicciNormReactionMotionTraceCubicAt x) -
      (4 / 3 : ℝ) * meanScalar g * U t x) at hKheat
  dsimp [K] at hKheat hKT ⊢
  dsimp [B] at hBheat hRN
  nlinarith [hQheat, hBheat, hKheat, hKT, hS, hRN]

end Poincare.HamiltonScalarGradientAuxiliaryEstimate
