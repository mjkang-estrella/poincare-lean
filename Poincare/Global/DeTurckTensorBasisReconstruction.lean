import Poincare.Global.DeTurckTensorBasisDefinitions

noncomputable section
set_option autoImplicit false
open scoped BigOperators

namespace Poincare.DeTurckTensorBasis
open DeTurckPrincipalSecondJet

local instance : NormedAddCommGroup Jet1 :=
  ContinuousLinearMap.toNormedAddCommGroup
    (𝕜 := ℝ) (𝕜₂ := ℝ) (E := E) (F := Bilin) (σ₁₂ := RingHom.id ℝ)
local instance : NormedSpace ℝ Jet1 :=
  ContinuousLinearMap.toNormedSpace
    (𝕜 := ℝ) (𝕜₂ := ℝ) (E := E) (F := Bilin)
    (σ₁₂ := RingHom.id ℝ) (𝕜' := ℝ)

private theorem coordinate_apply (a : Fin 3) (v : E) : coordinate a v = v a := by
  rfl

/-- Reconstruction retains all ordered tensor slots. -/
theorem tensor_expansion (h : Bilin) :
    h = ∑ a : Fin 3, ∑ b : Fin 3, h (basis3 a) (basis3 b) • tensor a b := by
  ext v w
  have hv : (∑ a : Fin 3, v a • basis3 a) = v :=
    (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr v
  have hw : (∑ b : Fin 3, w b • basis3 b) = w :=
    (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr w
  calc
    h v w = h (∑ a : Fin 3, v a • basis3 a) (∑ b : Fin 3, w b • basis3 b) := by
      rw [hv, hw]
    _ = _ := by
      simp only [map_sum, map_smul, ContinuousLinearMap.sum_apply,
        ContinuousLinearMap.smul_apply, smul_eq_mul, Finset.mul_sum,
        tensor, ContinuousLinearMap.smulRight_apply, coordinate_apply]
      conv_lhs => rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      ring

/-- Reconstruction retains all ordered first-jet direction and tensor slots. -/
theorem firstJet_expansion (J : Jet1) :
    J = ∑ p : Fin 3, ∑ a : Fin 3, ∑ b : Fin 3,
      J (basis3 p) (basis3 a) (basis3 b) • firstJet p a b := by
  ext r v w
  have hr : (∑ p : Fin 3, r p • basis3 p) = r :=
    (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr r
  have hv : (∑ a : Fin 3, v a • basis3 a) = v :=
    (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr v
  have hw : (∑ b : Fin 3, w b • basis3 b) = w :=
    (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr w
  calc
    J r v w = J (∑ p : Fin 3, r p • basis3 p)
        (∑ a : Fin 3, v a • basis3 a) (∑ b : Fin 3, w b • basis3 b) := by
      rw [hr, hv, hw]
    _ = _ := by
      simp only [map_sum, map_smul, ContinuousLinearMap.sum_apply,
        ContinuousLinearMap.smul_apply, smul_eq_mul, Finset.mul_sum,
        firstJet, tensor, ContinuousLinearMap.smulRight_apply, coordinate_apply]
      conv_lhs =>
        rw [Finset.sum_comm]
        arg 2
        ext a
        rw [Finset.sum_comm]
      conv_lhs => rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro p _
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      ring

/-- Actual basis evaluations determine both coupled coefficient actions. -/
theorem coefficient_action (L0 : Bilin →L[ℝ] Bilin) (L1 : Jet1 →L[ℝ] Bilin)
    (h : Bilin) (J : Jet1) (c d : Fin 3) :
    DeTurckInverseEntryDerivative.entryCLM c d (L0 h) =
      ∑ a : Fin 3, ∑ b : Fin 3,
        DeTurckInverseEntryDerivative.entryCLM c d (L0 (tensor a b)) *
          h (basis3 a) (basis3 b) ∧
    DeTurckInverseEntryDerivative.entryCLM c d (L1 J) =
      ∑ p : Fin 3, ∑ a : Fin 3, ∑ b : Fin 3,
        DeTurckInverseEntryDerivative.entryCLM c d (L1 (firstJet p a b)) *
          J (basis3 p) (basis3 a) (basis3 b) := by
  constructor
  · conv_lhs => rw [tensor_expansion h]
    simp only [map_sum, map_smul, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    exact mul_comm _ _
  · conv_lhs => rw [firstJet_expansion J]
    simp only [map_sum, map_smul, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro p _
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    exact mul_comm _ _

end Poincare.DeTurckTensorBasis
