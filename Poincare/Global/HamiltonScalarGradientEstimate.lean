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

/-- The factor-three trace estimate removes the derivative term, with no strict damping. -/
theorem tracelessEnergy_evolution_le_cubic
    {gt : ℝ → ClosedSmoothRiemannianMetric 3 M} {t : ℝ} (x : M)
    (hJoint : ∀ s y, MetricEntriesJointContDiffAt gt s y 3)
    (hFlow : ∀ y, IsClosedNormalizedRicciFlowSolutionAt gt t y) :
    deriv (fun s ↦ (gt s).tracelessRicciNormSqAt x) t -
        (gt t).laplacianAt (fun y ↦ (gt t).tracelessRicciNormSqAt y) x ≤
      (gt t).pinchingTracelessRicciReactionTrace3At x
        ((gt t).pinchingRicciNormReactionMotionTraceCubicAt x) -
        (4 / 3 : ℝ) * meanScalar (gt t) * (gt t).tracelessRicciNormSqAt x := by
  letI : Nonempty M := ⟨x⟩
  have hd :=
    hasDerivAt_tracelessRicciNormSqAt_eq_laplacianAt_add_actualNormalizedReaction_of_global_jointMetricEntries
      (x := x) hFlow hJoint
  rw [hd.deriv]
  dsimp only [normalizedTracelessRicciEvolutionReactionAt]
  have hb := (gt t).scalarGradNormSqAt_le_three_covRicciNormSqAt rfl x
  linarith

/-- Exactly which damping coefficients follow from the factor-three scalar trace bound. -/
theorem factorThree_damping_iff (c : ℝ) :
    (∀ A S : ℝ, 0 ≤ A → S ≤ 3 * A →
      -2 * A + (2 / 3 : ℝ) * S ≤ -c * A) ↔ c ≤ 0 := by
  constructor
  · intro h
    have htest := h 1 3 (by norm_num) (by norm_num)
    linarith
  · intro hc A S hA hS
    have hcA := mul_nonpos_of_nonpos_of_nonneg hc hA
    linarith

/-- The sharper scalar trace bound would supply Hamilton's strict damping coefficient. -/
theorem factorTwentySevenths_damping {A S : ℝ}
    (hS : S ≤ (20 / 7 : ℝ) * A) :
    -2 * A + (2 / 3 : ℝ) * S ≤ -(2 / 21 : ℝ) * A := by
  linarith

/-- The two traces determine the pairing with Hamilton's trace tensor. -/
theorem weighted_bianchi_trace_pairing
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (d D : ι → ℝ) (C : ι → ι → ι → ℝ)
    (hd : ∀ i, d i ≠ 0)
    (htrace : ∀ a, ∑ i, C a i i / d i = D a)
    (hdiv : ∀ j, ∑ a, C a a j / d a = D j / 2)
    (hsymm : ∀ a i j, C a i j = C a j i) :
    (∑ a, ∑ i, ∑ j, C a i j *
      ((if i = j then (3 / 10 : ℝ) * d i * D a else 0) +
       (if a = i then (1 / 20 : ℝ) * d a * D j else 0) +
       (if a = j then (1 / 20 : ℝ) * d a * D i else 0)) /
        (d a * d i * d j)) = (7 / 20 : ℝ) * ∑ a, D a ^ 2 / d a := by
  classical
  have hterm (a i j : ι) : C a i j *
      ((if i = j then (3 / 10 : ℝ) * d i * D a else 0) +
       (if a = i then (1 / 20 : ℝ) * d a * D j else 0) +
       (if a = j then (1 / 20 : ℝ) * d a * D i else 0)) /
        (d a * d i * d j) =
      (if i = j then (3 / 10 : ℝ) * (D a / d a) * (C a i i / d i) else 0) +
      (if a = i then (1 / 20 : ℝ) * (D j / d j) * (C a a j / d a) else 0) +
      (if a = j then (1 / 20 : ℝ) * (D i / d i) * (C a a i / d a) else 0) := by
    have hs := hsymm a i a
    split_ifs <;> subst_vars <;> simp_all only <;>
      field_simp (discharger := exact hd _) <;> ring
  simp_rw [hterm, Finset.sum_add_distrib]
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq]
  simp [-one_div]
  have hfirst : (∑ a, ∑ i, (3 / 10 : ℝ) * (D a / d a) * (C a i i / d i)) =
      (3 / 10 : ℝ) * ∑ a, D a ^ 2 / d a := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    rw [← Finset.mul_sum, htrace]
    ring
  have hother : (∑ a, ∑ j, (1 / 20 : ℝ) * (D j / d j) * (C a a j / d a)) =
      (1 / 40 : ℝ) * ∑ a, D a ^ 2 / d a := by
    rw [Finset.sum_comm]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    rw [← Finset.mul_sum, hdiv]
    ring
  rw [hfirst, hother]
  linarith

omit [CompactSpace M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [SecondCountableTopology M] in
/-- Contracted Bianchi in the same orthogonal frame used by the Ricci derivative norm. -/
theorem contractedBianchi_orthogonal_trace
    (g : Poincare.ClosedSmoothRiemannianMetric 3 M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (x : M) (w : TangentSpace (Poincare.closedSmoothModelWithCorners 3) x) :
    (let b := Poincare.metricOrthogonalBasisAt g x
     ∑ i, Poincare.covTensor2DerivAt g (Poincare.ricciVariationField g) x
       (b i) (b i) w / g.metricBilinAt x (b i) (b i)) =
      extDerivFun (fun y ↦ g.scalarAt y) x w / 2 := by
  classical
  letI : FiniteDimensional ℝ (TangentSpace (Poincare.closedSmoothModelWithCorners 3) x) :=
    inferInstanceAs (FiniteDimensional ℝ (Poincare.ClosedSmoothModel 3))
  let B : LinearMap.BilinForm ℝ (TangentSpace (Poincare.closedSmoothModelWithCorners 3) x) :=
    LinearMap.mk₂ ℝ
      (fun p v ↦ Poincare.covTensor2DerivAt g (Poincare.ricciVariationField g) x v p w)
      (fun p p' v ↦ Poincare.covTensor2DerivAt_add_left
        (Poincare.covTensor2ExtDifferentiableAt_ricciVariationField_canonical g x)
        (Poincare.tensor2AddLeft_ricciVariationField g) v p p' w)
      (fun c p v ↦ Poincare.covTensor2DerivAt_smul_left
        (Poincare.covTensor2ExtDifferentiableAt_ricciVariationField_canonical g x)
        (Poincare.tensor2SMulLeft_ricciVariationField g) c v p w)
      (fun p v v' ↦ Poincare.covTensor2DerivAt_add_deriv
        (Poincare.tensor2AddLeft_ricciVariationField g)
        (Poincare.tensor2AddRight_ricciVariationField g) v v' p w)
      (fun c p v ↦ Poincare.covTensor2DerivAt_smul_deriv
        (Poincare.tensor2SMulLeft_ricciVariationField g)
        (Poincare.tensor2SMulRight_ricciVariationField g) c v p w)
  let b := Poincare.metricOrthogonalBasisAt g x
  have hOrtho : (g.metricBilinAt x).IsOrthoᵢ b := by
    exact Classical.choose_spec
      (LinearMap.BilinForm.exists_orthogonal_basis
        (B := g.metricBilinAt x) (g.metricBilinAt_isSymm x))
  have hchange := Poincare.metricTraceInBasisAt_eq_metricTraceInBasisAt g x B
    (Module.finBasis ℝ (TangentSpace (Poincare.closedSmoothModelWithCorners 3) x)) b
  have hdiv : Poincare.tensorDivergenceOneFormAt g (Poincare.ricciVariationField g) x w =
      ∑ i, Poincare.covTensor2DerivAt g (Poincare.ricciVariationField g) x
        (b i) (b i) w / g.metricBilinAt x (b i) (b i) := by
    change Poincare.metricTraceInBasisAt g x B _ = _
    rw [hchange]
    unfold Poincare.metricTraceInBasisAt
    apply Finset.sum_congr rfl
    intro i _
    rw [Poincare.metricDualVectorAt_orthogonalBasis_coord_eq g x b hOrtho i]
    simp only [B, LinearMap.mk₂_apply,
      Poincare.covTensor2DerivAt_smul_deriv
        (Poincare.tensor2SMulLeft_ricciVariationField g)
        (Poincare.tensor2SMulRight_ricciVariationField g), smul_eq_mul]
    ring
  rw [← hdiv]
  have h := (Poincare.eventually_closedContractedBianchiOneFormAt_canonical g x).self_of_nhds w
  exact h.trans (by ring)

/-- The weighted square completion for a symmetric three-tensor with Bianchi traces. -/
theorem weighted_bianchi_gradient_bound
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hcard : Fintype.card ι = 3)
    (d D : ι → ℝ) (C : ι → ι → ι → ℝ)
    (hd : ∀ i, 0 < d i)
    (htrace : ∀ a, ∑ i, C a i i / d i = D a)
    (hdiv : ∀ j, ∑ a, C a a j / d a = D j / 2)
    (hsymm : ∀ a i j, C a i j = C a j i) :
    (∑ a, D a ^ 2 / d a) ≤ (20 / 7 : ℝ) *
      ∑ a, ∑ i, ∑ j, C a i j ^ 2 / (d a * d i * d j) := by
  classical
  let B : ι → ι → ι → ℝ := fun a i j ↦
      (if i = j then (3 / 10 : ℝ) * d i * D a else 0) +
      (if a = i then (1 / 20 : ℝ) * d a * D j else 0) +
      (if a = j then (1 / 20 : ℝ) * d a * D i else 0)
  have hdne : ∀ i, d i ≠ 0 := fun i ↦ ne_of_gt (hd i)
  have hBt (a : ι) : ∑ i, B a i i / d i = D a := by
    have he (i : ι) : B a i i / d i = (3 / 10 : ℝ) * D a +
        (if a = i then (1 / 10 : ℝ) * D a else 0) := by
      by_cases h : a = i
      · subst i
        dsimp [B]
        simp only [ite_true]
        field_simp (discharger := exact hdne _)
        ring
      · simp [B, h]
        field_simp (discharger := exact hdne _)
    simp_rw [he, Finset.sum_add_distrib]
    simp [hcard]
    ring
  have hBd (j : ι) : ∑ a, B a a j / d a = D j / 2 := by
    have he (a : ι) : B a a j / d a = (1 / 20 : ℝ) * D j +
        (if a = j then (7 / 20 : ℝ) * D j else 0) := by
      by_cases h : a = j
      · subst a
        dsimp [B]
        simp only [ite_true]
        field_simp (discharger := exact hdne _)
        ring
      · simp [B, h]
        field_simp (discharger := exact hdne _)
    simp_rw [he, Finset.sum_add_distrib]
    simp [hcard]
    ring
  have hBs (a i j : ι) : B a i j = B a j i := by
    dsimp [B]
    by_cases h : i = j
    · subst j
      rfl
    · simp [h, Ne.symm h]
      ring
  have hp := Poincare.HamiltonScalarGradientEstimate.weighted_bianchi_trace_pairing
    d D C hdne htrace hdiv hsymm
  have hn := Poincare.HamiltonScalarGradientEstimate.weighted_bianchi_trace_pairing
    d D B hdne hBt hBd hBs
  change (∑ a, ∑ i, ∑ j, C a i j * B a i j / (d a * d i * d j)) = _ at hp
  change (∑ a, ∑ i, ∑ j, B a i j * B a i j / (d a * d i * d j)) = _ at hn
  have hnonneg : 0 ≤ ∑ a, ∑ i, ∑ j,
      (C a i j - B a i j) ^ 2 / (d a * d i * d j) := by
    exact Finset.sum_nonneg fun a _ ↦ Finset.sum_nonneg fun i _ ↦
      Finset.sum_nonneg fun j _ ↦ div_nonneg (sq_nonneg _)
        (le_of_lt (mul_pos (mul_pos (hd a) (hd i)) (hd j)))
  have hexpand : (∑ a, ∑ i, ∑ j,
      (C a i j - B a i j) ^ 2 / (d a * d i * d j)) =
      (∑ a, ∑ i, ∑ j, C a i j ^ 2 / (d a * d i * d j)) -
      2 * (∑ a, ∑ i, ∑ j, C a i j * B a i j / (d a * d i * d j)) +
      (∑ a, ∑ i, ∑ j, B a i j * B a i j / (d a * d i * d j)) := by
    simp only [Finset.mul_sum]
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a _
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hexpand, hp, hn] at hnonneg
  linarith

omit [CompactSpace M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [SecondCountableTopology M] in
/-- Hamilton's contracted-Bianchi improvement of the scalar trace-gradient bound. -/
theorem scalarGradNormSq_le_twentySevenths_covRicciNormSq
    (g : Poincare.ClosedSmoothRiemannianMetric 3 M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (x : M) :
    Poincare.ClosedSmoothRiemannianMetric.scalarGradNormSqAt g x ≤
      (20 / 7 : ℝ) * Poincare.covRicciNormSqAt g x := by
  classical
  letI : FiniteDimensional ℝ (TangentSpace (Poincare.closedSmoothModelWithCorners 3) x) :=
    inferInstanceAs (FiniteDimensional ℝ (Poincare.ClosedSmoothModel 3))
  let b := Poincare.metricOrthogonalBasisAt g x
  let d := fun i ↦ g.metricBilinAt x (b i) (b i)
  let D := fun a ↦ extDerivFun (fun y ↦ g.scalarAt y) x (b a)
  let C := fun a i j ↦
    Poincare.covTensor2DerivAt g (Poincare.ricciVariationField g) x (b a) (b i) (b j)
  have hcard : Fintype.card (Fin (Module.finrank ℝ
      (TangentSpace (Poincare.closedSmoothModelWithCorners 3) x))) = 3 := by
    simp [Poincare.ClosedSmoothRiemannianMetric.finrank_tangentSpace_eq (n := 3) (M := M) x]
  have hd : ∀ i, 0 < d i := fun i ↦ g.metricBilinAt_pos x (b.ne_zero i)
  have ht : ∀ a, ∑ i, C a i i / d i = D a := by
    intro a
    exact (g.extDerivFun_scalarAt_eq_metricOrthogonalBasis_covRicci_trace x (b a)).symm
  have hv : ∀ j, ∑ a, C a a j / d a = D j / 2 := by
    intro j
    exact Poincare.HamiltonScalarGradientEstimate.contractedBianchi_orthogonal_trace g x (b j)
  have hs : ∀ a i j, C a i j = C a j i := fun a i j ↦
    Poincare.covTensor2DerivAt_ricciVariationField_symm g x (b a) (b i) (b j)
  rw [g.scalarGradNormSqAt_eq_metricOrthogonalBasis_sum x,
    Poincare.covRicciNormSqAt_eq_metricOrthogonalBasis_sum g x]
  exact Poincare.HamiltonScalarGradientEstimate.weighted_bianchi_gradient_bound
    hcard d D C hd ht hv hs

end Poincare.HamiltonScalarGradientEstimate
