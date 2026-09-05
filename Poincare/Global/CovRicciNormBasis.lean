import Poincare.Global.ScalarVariation

/-!
# Arbitrary-basis formula for the covariant Ricci norm

This module identifies the orthogonal-frame definition of `|∇Ric|²` with the
full contraction in any finite tangent basis and its metric-raised dual basis.
-/

noncomputable section

open Bundle FiberBundle
open scoped Manifold ContDiff

universe u

namespace Poincare

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "I" => closedSmoothModelWithCorners n
local notation "E" => ClosedSmoothModel n
local notation "TM" => (TangentSpace I : M → Type _)

namespace ClosedSmoothRiemannianMetric

/-- The metric pairing of two symmetric bilinear forms is their full
contraction in any basis and its metric-raised dual basis. -/
theorem tensor2PairingTraceInBasisAt_eq_basis_sum_of_symm
    (g : ClosedSmoothRiemannianMetric n M) (x : M)
    [FiniteDimensional ℝ (TM x)]
    (A B : LinearMap.BilinForm ℝ (TM x))
    (hA : ∀ p q, A p q = A q p)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ (TM x)) :
    tensor2PairingTraceInBasisAt g x A B b =
      ∑ i, ∑ j,
        A (metricDualVectorAt g x (b.coord i))
            (metricDualVectorAt g x (b.coord j)) *
          B (b i) (b j) := by
  let sharp : ι → TM x := fun i ↦ metricDualVectorAt g x (b.coord i)
  let A' := metricTraceEndomorphismAt g x A
  let B' := metricTraceEndomorphismAt g x B
  have hinner (D : LinearMap.BilinForm ℝ (TM x)) (p q : TM x) :
      g.inner x (metricTraceEndomorphismAt g x D p) q = D p q := by
    unfold metricTraceEndomorphismAt
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    change
      g.metricBilinAt x
          ((LinearMap.BilinForm.toDual (g.metricBilinAt x)
            (g.metricBilinAt_nondegenerate x)).symm (D p)) q =
        D p q
    rw [LinearMap.BilinForm.apply_toDual_symm_apply]
  rw [tensor2PairingTraceInBasisAt_eq_linearMap_trace
    (g := g) (x := x) (A := A) (B := B) (b := b)]
  rw [LinearMap.trace_eq_matrix_trace ℝ b, Matrix.trace]
  change
    ∑ i, ((LinearMap.toMatrix b b) (A' ∘ₗ B')).diag i =
      ∑ i, ∑ j, A (sharp i) (sharp j) * B (b i) (b j)
  symm
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Matrix.diag_apply, LinearMap.toMatrix_apply]
  change
    (∑ j, A (sharp i) (sharp j) * B (b i) (b j)) =
      b.coord i ((A' ∘ₗ B') (b i))
  rw [LinearMap.comp_apply,
    coord_eq_inner_metricDualVectorAt_of_basis
      (g := g) (x := x) (b := b)]
  have hcoord : ∀ j, A (sharp i) (sharp j) = b.coord j (A' (sharp i)) := by
    intro j
    rw [coord_eq_inner_metricDualVectorAt_of_basis
      (g := g) (x := x) (b := b)]
    exact (hinner A (sharp i) (sharp j)).symm
  have hslot : ∀ j, B (b i) (b j) = g.inner x (b j) (B' (b i)) := by
    intro j
    calc
      B (b i) (b j) = g.inner x (B' (b i)) (b j) :=
        (hinner B (b i) (b j)).symm
      _ = g.inner x (b j) (B' (b i)) := g.inner_symm x _ _
  calc
    (∑ j, A (sharp i) (sharp j) * B (b i) (b j)) =
        ∑ j, b.coord j (A' (sharp i)) * g.inner x (b j) (B' (b i)) := by
          refine Finset.sum_congr rfl fun j _ ↦ ?_
          rw [hcoord j, hslot j]
    _ = g.inner x (A' (sharp i)) (B' (b i)) := by
          exact sum_basis_coord_inner_eq_inner g x b _ _
    _ = A (sharp i) (B' (b i)) := hinner A _ _
    _ = A (B' (b i)) (sharp i) := hA _ _
    _ = g.inner x (A' (B' (b i))) (sharp i) :=
          (hinner A _ _).symm

set_option maxHeartbeats 5000000 in
/-- The squared covariant Ricci norm is the full contraction of `∇Ric` in any
finite tangent basis and its metric-raised dual basis. -/
theorem covRicciNormSqAt_eq_basis_sum
    (g : ClosedSmoothRiemannianMetric n M)
    [CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita 1]
    (x : M) [FiniteDimensional ℝ (TM x)]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ (TM x)) :
    covRicciNormSqAt g x =
      ∑ a, ∑ i, ∑ j,
        covTensor2DerivAt g (ricciVariationField g) x
            (metricDualVectorAt g x (b.coord a))
            (metricDualVectorAt g x (b.coord i))
            (metricDualVectorAt g x (b.coord j)) *
          covTensor2DerivAt g (ricciVariationField g) x
            (b a) (b i) (b j) := by
  classical
  let T : TM x →ₗ[ℝ] TM x →ₗ[ℝ] TM x →ₗ[ℝ] ℝ :=
    { toFun := fun v ↦
        { toFun := fun p ↦
            { toFun := fun q ↦
                covTensor2DerivAt g (ricciVariationField g) x v p q
              map_add' := fun q q' ↦
                covTensor2DerivAt_add_right
                  (g := g) (h := ricciVariationField g) (x := x)
                  (covTensor2ExtDifferentiableAt_ricciVariationField_canonical g x)
                  (tensor2AddRight_ricciVariationField g) v p q q'
              map_smul' := fun c q ↦
                covTensor2DerivAt_smul_right
                  (g := g) (h := ricciVariationField g) (x := x)
                  (covTensor2ExtDifferentiableAt_ricciVariationField_canonical g x)
                  (tensor2SMulRight_ricciVariationField g) c v p q }
          map_add' := by
            intro p p'
            apply LinearMap.ext
            intro q
            exact covTensor2DerivAt_add_left
              (g := g) (h := ricciVariationField g) (x := x)
              (covTensor2ExtDifferentiableAt_ricciVariationField_canonical g x)
              (tensor2AddLeft_ricciVariationField g) v p p' q
          map_smul' := by
            intro c p
            apply LinearMap.ext
            intro q
            exact covTensor2DerivAt_smul_left
              (g := g) (h := ricciVariationField g) (x := x)
              (covTensor2ExtDifferentiableAt_ricciVariationField_canonical g x)
              (tensor2SMulLeft_ricciVariationField g) c v p q }
      map_add' := by
        intro v v'
        apply LinearMap.ext
        intro p
        apply LinearMap.ext
        intro q
        exact covTensor2DerivAt_add_deriv
          (g := g) (h := ricciVariationField g) (x := x)
          (tensor2AddLeft_ricciVariationField g)
          (tensor2AddRight_ricciVariationField g) v v' p q
      map_smul' := by
        intro c v
        apply LinearMap.ext
        intro p
        apply LinearMap.ext
        intro q
        exact covTensor2DerivAt_smul_deriv
          (g := g) (h := ricciVariationField g) (x := x)
          (tensor2SMulLeft_ricciVariationField g)
          (tensor2SMulRight_ricciVariationField g) c v p q }
  let C : LinearMap.BilinForm ℝ (TM x) :=
    covRicciDerivativePairingBilinFormAt g x
  have hC_basis : ∀ u w : TM x,
      C u w =
        ∑ i, ∑ j,
          T w (metricDualVectorAt g x (b.coord i))
              (metricDualVectorAt g x (b.coord j)) *
            T u (b i) (b j) := by
    intro u w
    change
      tensor2PairingTraceInBasisAt g x
          (covRicciDerivativeBilinFormAt g (extend E w) x)
          (covRicciDerivativeBilinFormAt g (extend E u) x)
          (Module.finBasis ℝ (TM x)) = _
    rw [tensor2PairingTraceInBasisAt_eq_tensor2PairingTraceInBasisAt
      (g := g) (x := x)
      (A := covRicciDerivativeBilinFormAt g (extend E w) x)
      (B := covRicciDerivativeBilinFormAt g (extend E u) x)
      (Module.finBasis ℝ (TM x)) b]
    simpa [T, covRicciDerivativeBilinFormAt] using
      tensor2PairingTraceInBasisAt_eq_basis_sum_of_symm
        (g := g) (x := x)
        (A := covRicciDerivativeBilinFormAt g (extend E w) x)
        (B := covRicciDerivativeBilinFormAt g (extend E u) x)
        (fun p q ↦ by
          simpa [covRicciDerivativeBilinFormAt] using
            covTensor2DerivAt_ricciVariationField_symm
              (g := g) (x := x) w p q) b
  let b₀ := metricOrthogonalBasisAt g x
  let sharp₀ : Fin (Module.finrank ℝ (TM x)) → TM x :=
    fun i ↦ metricDualVectorAt g x (b₀.coord i)
  let diag : Fin (Module.finrank ℝ (TM x)) → ℝ :=
    fun i ↦ g.metricBilinAt x (b₀ i) (b₀ i)
  have hOrtho : (g.metricBilinAt x).IsOrthoᵢ b₀ := by
    simpa [b₀, metricOrthogonalBasisAt] using
      Classical.choose_spec
        (LinearMap.BilinForm.exists_orthogonal_basis
          (B := g.metricBilinAt x) (g.metricBilinAt_isSymm x))
  have hsharp₀ : ∀ i, sharp₀ i = (diag i)⁻¹ • b₀ i := by
    intro i
    simpa [sharp₀, diag] using
      metricDualVectorAt_orthogonalBasis_coord_eq
        (g := g) (x := x) (b := b₀) hOrtho i
  have hC_orth : ∀ u w : TM x,
      C u w =
        ∑ i, ∑ j,
          T w (sharp₀ i) (sharp₀ j) * T u (b₀ i) (b₀ j) := by
    intro u w
    change
      tensor2PairingTraceInBasisAt g x
          (covRicciDerivativeBilinFormAt g (extend E w) x)
          (covRicciDerivativeBilinFormAt g (extend E u) x)
          (Module.finBasis ℝ (TM x)) = _
    rw [tensor2PairingTraceInBasisAt_eq_tensor2PairingTraceInBasisAt
      (g := g) (x := x)
      (A := covRicciDerivativeBilinFormAt g (extend E w) x)
      (B := covRicciDerivativeBilinFormAt g (extend E u) x)
      (Module.finBasis ℝ (TM x)) b₀]
    simpa [T, covRicciDerivativeBilinFormAt, sharp₀] using
      tensor2PairingTraceInBasisAt_eq_basis_sum_of_symm
        (g := g) (x := x)
        (A := covRicciDerivativeBilinFormAt g (extend E w) x)
        (B := covRicciDerivativeBilinFormAt g (extend E u) x)
        (fun p q ↦ by
          simpa [covRicciDerivativeBilinFormAt] using
            covTensor2DerivAt_ricciVariationField_symm
              (g := g) (x := x) w p q) b₀
  have hOrthTrace : metricTraceInBasisAt g x C b₀ = covRicciNormSqAt g x := by
    unfold metricTraceInBasisAt
    calc
      (∑ a, C (b₀ a) (sharp₀ a)) =
          ∑ a, ∑ i, ∑ j,
            (diag a)⁻¹ * (diag i)⁻¹ * (diag j)⁻¹ *
              (T (b₀ a) (b₀ i) (b₀ j)) ^ 2 := by
            refine Finset.sum_congr rfl fun a _ ↦ ?_
            rw [hC_orth (b₀ a) (sharp₀ a)]
            refine Finset.sum_congr rfl fun i _ ↦ ?_
            refine Finset.sum_congr rfl fun j _ ↦ ?_
            rw [hsharp₀ a, hsharp₀ i, hsharp₀ j]
            simp [smul_eq_mul]
            ring
      _ = ∑ a, ∑ i, ∑ j,
          (covTensor2DerivAt g (ricciVariationField g) x
            (b₀ a) (b₀ i) (b₀ j)) ^ 2 /
            (g.metricBilinAt x (b₀ a) (b₀ a) *
              g.metricBilinAt x (b₀ i) (b₀ i) *
              g.metricBilinAt x (b₀ j) (b₀ j)) := by
            refine Finset.sum_congr rfl fun a _ ↦ ?_
            refine Finset.sum_congr rfl fun i _ ↦ ?_
            refine Finset.sum_congr rfl fun j _ ↦ ?_
            have ha : diag a ≠ 0 :=
              ne_of_gt (g.metricBilinAt_pos x (b₀.ne_zero a))
            have hi : diag i ≠ 0 :=
              ne_of_gt (g.metricBilinAt_pos x (b₀.ne_zero i))
            have hj : diag j ≠ 0 :=
              ne_of_gt (g.metricBilinAt_pos x (b₀.ne_zero j))
            simp [T, diag] at ha hi hj ⊢
            field_simp [ha, hi, hj]
      _ = covRicciNormSqAt g x := by
            simpa [b₀] using
              (covRicciNormSqAt_eq_metricOrthogonalBasis_sum
                (g := g) (x := x)).symm
  calc
    covRicciNormSqAt g x = metricTraceInBasisAt g x C b₀ := hOrthTrace.symm
    _ = metricTraceInBasisAt g x C b :=
      metricTraceInBasisAt_eq_metricTraceInBasisAt
        (g := g) (x := x) (B := C) b₀ b
    _ = ∑ a, ∑ i, ∑ j,
        covTensor2DerivAt g (ricciVariationField g) x
            (metricDualVectorAt g x (b.coord a))
            (metricDualVectorAt g x (b.coord i))
            (metricDualVectorAt g x (b.coord j)) *
          covTensor2DerivAt g (ricciVariationField g) x
            (b a) (b i) (b j) := by
      unfold metricTraceInBasisAt
      refine Finset.sum_congr rfl fun a _ ↦ ?_
      simpa [T] using hC_basis (b a) (metricDualVectorAt g x (b.coord a))

end ClosedSmoothRiemannianMetric
end Poincare
