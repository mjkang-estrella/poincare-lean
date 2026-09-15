import Poincare.Global.IntrinsicBochnerScalarGradient

noncomputable section
open Bundle FiberBundle Filter Set
open scoped Manifold ContDiff Topology
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u

namespace Poincare.HamiltonScalarGradientEstimate

variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (ClosedSmoothModel 3) M]
  [IsManifold (closedSmoothModelWithCorners 3) ∞ M]


/-- Recover the Laplacian of a quotient from the product rule on a nonzero slice. -/
theorem laplacian_div
    (g : ClosedSmoothRiemannianMetric 3 M) {f h : M → ℝ} (x : M)
    (hf : ∀ y, ContMDiffAt (closedSmoothModelWithCorners 3) 𝓘(ℝ) 2 f y)
    (hh : ∀ y, ContMDiffAt (closedSmoothModelWithCorners 3) 𝓘(ℝ) 2 h y)
    (hne : ∀ y, h y ≠ 0) :
    g.laplacianAt (fun y ↦ f y / h y) x =
      g.laplacianAt f x / h x - f x * g.laplacianAt h x / h x ^ 2 -
        2 * g.inner x (g.gradientAt (fun y ↦ f y / h y) x)
          (g.gradientAt h x) / h x := by
  have hq : ∀ y, ContMDiffAt (closedSmoothModelWithCorners 3) 𝓘(ℝ) 2 (fun z ↦ f z / h z) y :=
    fun y ↦ (hf y).div₀ (hh y) (hne y)
  have heq : (fun y ↦ f y / h y) * h = f := by
    funext y
    exact div_mul_cancel₀ (f y) (hne y)
  have hp := g.laplacianAt_mul' (x := x) hq hh
  rw [heq] at hp
  field_simp (discharger := exact hne x) at hp ⊢
  nlinarith [hp]

/-- The drift form of the heat-operator quotient rule. -/
theorem heatOperator_div
    (g : ClosedSmoothRiemannianMetric 3 M) {f h : ℝ → M → ℝ}
    {t f' h' : ℝ} (x : M)
    (hft : HasDerivAt (fun s ↦ f s x) f' t)
    (hht : HasDerivAt (fun s ↦ h s x) h' t)
    (hf : ∀ y, ContMDiffAt (closedSmoothModelWithCorners 3) 𝓘(ℝ) 2 (f t) y)
    (hh : ∀ y, ContMDiffAt (closedSmoothModelWithCorners 3) 𝓘(ℝ) 2 (h t) y)
    (hne : ∀ y, h t y ≠ 0) :
    deriv (fun s ↦ f s x / h s x) t -
        g.laplacianAt (fun y ↦ f t y / h t y) x =
      (f' - g.laplacianAt (f t) x) / h t x -
        f t x * (h' - g.laplacianAt (h t) x) / h t x ^ 2 +
        2 * g.inner x (g.gradientAt (fun y ↦ f t y / h t y) x)
          (g.gradientAt (h t) x) / h t x := by
  have hd : deriv (fun s ↦ f s x / h s x) t =
      (f' * h t x - f t x * h') / h t x ^ 2 :=
    (hft.div hht (hne x)).deriv
  rw [hd, laplacian_div g x hf hh hne]
  field_simp (discharger := exact hne x)
  ring

/-- Pairing the quotient gradient with the denominator gradient. -/
theorem gradient_div_pairing
    (g : ClosedSmoothRiemannianMetric 3 M) {f h : M → ℝ} (x : M)
    (hf : MDifferentiableAt (closedSmoothModelWithCorners 3) 𝓘(ℝ) f x)
    (hh : MDifferentiableAt (closedSmoothModelWithCorners 3) 𝓘(ℝ) h x)
    (hne : h x ≠ 0) :
    g.inner x (g.gradientAt (fun y ↦ f y / h y) x) (g.gradientAt h x) =
      g.inner x (g.gradientAt f x) (g.gradientAt h x) / h x -
        f x * g.inner x (g.gradientAt h x) (g.gradientAt h x) / h x ^ 2 := by
  have hq := hf.div hh hne
  have heq : (fun y ↦ f y / h y) * h =ᶠ[𝓝 x] f := by
    filter_upwards [hh.continuousAt.eventually_ne hne] with y hy
    exact div_mul_cancel₀ (f y) hy
  have hp := g.gradientAt_mul (f := fun y ↦ f y / h y) hq hh
  rw [g.gradientAt_congr_of_eventuallyEq heq] at hp
  have hp' := congrArg (fun v ↦ g.inner x v (g.gradientAt h x)) hp
  simp only [map_add, map_smul, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul] at hp'
  field_simp (discharger := exact hne) at hp' ⊢
  nlinarith [hp']

/-- Expand the quotient drift into numerator and denominator gradient terms. -/
theorem heatOperator_div_expanded
    (g : ClosedSmoothRiemannianMetric 3 M) {f h : ℝ → M → ℝ}
    {t f' h' : ℝ} (x : M)
    (hft : HasDerivAt (fun s ↦ f s x) f' t)
    (hht : HasDerivAt (fun s ↦ h s x) h' t)
    (hf : ∀ y, ContMDiffAt (closedSmoothModelWithCorners 3) 𝓘(ℝ) 2 (f t) y)
    (hh : ∀ y, ContMDiffAt (closedSmoothModelWithCorners 3) 𝓘(ℝ) 2 (h t) y)
    (hne : ∀ y, h t y ≠ 0) :
    deriv (fun s ↦ f s x / h s x) t -
        g.laplacianAt (fun y ↦ f t y / h t y) x =
      (f' - g.laplacianAt (f t) x) / h t x -
        f t x * (h' - g.laplacianAt (h t) x) / h t x ^ 2 +
        2 * g.inner x (g.gradientAt (h t) x) (g.gradientAt (f t) x) / h t x ^ 2 -
        2 * f t x * g.inner x (g.gradientAt (h t) x) (g.gradientAt (h t) x) /
          h t x ^ 3 := by
  rw [heatOperator_div g x hft hht hf hh hne,
    gradient_div_pairing g x ((hf x).mdifferentiableAt two_ne_zero)
      ((hh x).mdifferentiableAt two_ne_zero) (hne x),
    g.inner_symm x (g.gradientAt (f t) x) (g.gradientAt (h t) x)]
  field_simp (discharger := exact hne x)
  ring

variable [CompactSpace M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M]

/-- The exact scalar-gradient quotient evolution, including the normalized scaling term. -/
theorem scalarGradientQuotient_evolution
    {gt : ℝ → ClosedSmoothRiemannianMetric 3 M} {t : ℝ} (x : M)
    (hS : IntrinsicBochnerScalarGradient.SatisfiesScalarGradientEvolutionAt gt t x)
    (hR : SatisfiesNormalizedHamiltonScalarEvolutionAt gt t x)
    (hRthree : ContMDiff (closedSmoothModelWithCorners 3) 𝓘(ℝ) 3 (fun y ↦ (gt t).scalarAt y))
    (hRpos : ∀ y, 0 < (gt t).scalarAt y) :
    let g := gt t
    let R := fun y ↦ g.scalarAt y
    let S := fun y ↦ g.scalarGradNormSqAt y
    let H := ∑ i, g.inner x
      (g.leviCivita (g.gradient R) x ((Module.finBasis ℝ (ClosedSmoothModel 3)) i))
      (g.leviCivita (g.gradient R) x
        (metricDualVectorAt g x ((Module.finBasis ℝ (ClosedSmoothModel 3)).coord i)))
    deriv (fun s ↦ (gt s).scalarGradNormSqAt x / (gt s).scalarAt x) t -
        g.laplacianAt (fun y ↦ S y / R y) x =
      -2 * H / R x +
        4 * g.inner x (g.gradientAt R x) (g.gradientAt (fun y ↦ g.ricciNormSqAt y) x) / R x -
        2 * S x * g.ricciNormSqAt x / R x ^ 2 -
        (4 / 3 : ℝ) * meanScalar g * (S x / R x) +
        2 * g.inner x (g.gradientAt R x) (g.gradientAt S x) / R x ^ 2 -
        2 * S x ^ 2 / R x ^ 3 := by
  have hS₂ : ∀ y, ContMDiffAt (closedSmoothModelWithCorners 3) 𝓘(ℝ) 2
      (fun z ↦ (gt t).scalarGradNormSqAt z) y :=
    IntrinsicBochnerScalarGradient.gradientNormSq_contMDiffAt_two (gt t) _ hRthree
  have hR₂ : ∀ y, ContMDiffAt (closedSmoothModelWithCorners 3) 𝓘(ℝ) 2 (fun z ↦ (gt t).scalarAt z) y :=
    fun y ↦ hRthree.contMDiffAt.of_le (by norm_num)
  have he := heatOperator_div_expanded (gt t) x hS hR hS₂ hR₂
    (fun y ↦ (hRpos y).ne')
  dsimp only
  rw [he]
  unfold ClosedSmoothRiemannianMetric.scalarGradNormSqAt
  field_simp (discharger := first | exact (hRpos x).ne' | norm_num)
  ring

variable [SecondCountableTopology M]

/-- Joint fifth-order metric entries supply all scalar regularity for the quotient identity. -/
theorem scalarGradientQuotient_evolution_of_normalizedFlow
    {gt : ℝ → ClosedSmoothRiemannianMetric 3 M} {t : ℝ} (x : M)
    (hJoint5 : ∀ s y, MetricEntriesJointContDiffAt gt s y 5)
    (hFlow : ∀ y, IsClosedNormalizedRicciFlowSolutionAt gt t y)
    (hRpos : ∀ y, 0 < (gt t).scalarAt y) :
    let g := gt t
    let R := fun y ↦ g.scalarAt y
    let S := fun y ↦ g.scalarGradNormSqAt y
    let H := ∑ i, g.inner x
      (g.leviCivita (g.gradient R) x ((Module.finBasis ℝ (ClosedSmoothModel 3)) i))
      (g.leviCivita (g.gradient R) x
        (metricDualVectorAt g x ((Module.finBasis ℝ (ClosedSmoothModel 3)).coord i)))
    deriv (fun s ↦ (gt s).scalarGradNormSqAt x / (gt s).scalarAt x) t -
        g.laplacianAt (fun y ↦ S y / R y) x =
      -2 * H / R x +
        4 * g.inner x (g.gradientAt R x) (g.gradientAt (fun y ↦ g.ricciNormSqAt y) x) / R x -
        2 * S x * g.ricciNormSqAt x / R x ^ 2 -
        (4 / 3 : ℝ) * meanScalar g * (S x / R x) +
        2 * g.inner x (g.gradientAt R x) (g.gradientAt S x) / R x ^ 2 -
        2 * S x ^ 2 / R x ^ 3 := by
  letI : Nonempty M := ⟨x⟩
  exact scalarGradientQuotient_evolution x
    (IntrinsicBochnerScalarGradient.satisfiesScalarGradientEvolutionAt_of_normalizedFlow
      hJoint5 hFlow)
    (satisfiesNormalizedHamiltonScalarEvolutionAt_of_normalizedFlow_of_globalLichnerowicz
      hFlow (globalLichnerowiczAssemblyRegularity_of_jointMetricEntriesThree
        (fun s y ↦ (hJoint5 s y).of_le (by norm_num))))
    (IntrinsicBochnerScalarGradient.scalar_contMDiff_three_of_metricEntries_five hJoint5 t)
    hRpos

end Poincare.HamiltonScalarGradientEstimate
