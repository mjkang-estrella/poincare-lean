import Poincare.Global.DeTurckInverseEntryDerivativeDefinitions
import Poincare.Global.DeTurckMetricJetNonsingular
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Calculus.FDeriv.Mul

noncomputable section
set_option autoImplicit false
open scoped BigOperators

namespace Poincare.DeTurckInverseEntryDerivative
open DeTurckPrincipalSecondJet

section MatrixCalculation
open scoped Matrix.Norms.Operator

private abbrev Mat := Matrix (Fin 3) (Fin 3) ℝ

private def coordinateMatrix : Bilin →L[ℝ] Mat :=
  LinearMap.toContinuousLinearMap
    { toFun := fun G i j => G (basis3 i) (basis3 j)
      map_add' := by
        intro G H
        ext i j
        simp only [ContinuousLinearMap.add_apply, Matrix.add_apply]
      map_smul' := by
        intro r G
        ext i j
        simp only [ContinuousLinearMap.smul_apply, Matrix.smul_apply, smul_eq_mul,
          RingHom.id_apply] }

private def matrixEntry (i j : Fin 3) : Mat →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A => A i j
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }

/-- The scalar inverse coefficient has the true two-sided inverse variation.
It is the principal coefficient input for the full DeTurck differential. -/
theorem hasFDerivAt_inverseEntry (G0 : Bilin) (i j : Fin 3)
    (hG0 : G0.IsInvertible) :
    HasFDerivAt (fun G : Bilin => inverseEntries G i j)
      (inverseEntryDerivative G0 i j) G0 := by
  obtain ⟨U, hU⟩ := DeTurckMetricJetNonsingular.coordinate_matrix_isUnit G0 hG0
  have hUval : (U : Mat) = coordinateMatrix G0 := hU
  have hInv : (↑U⁻¹ : Mat) = inverseEntries G0 := by
    rw [Matrix.coe_units_inv, hUval]
    rfl
  have hDinv := hasFDerivAt_ringInverse (𝕜 := ℝ) U
  rw [hUval] at hDinv
  have hD := hDinv.comp G0 coordinateMatrix.hasFDerivAt
  have hE := (matrixEntry i j).hasFDerivAt.comp G0 hD
  have hfun : (fun G : Bilin => matrixEntry i j (Ring.inverse (coordinateMatrix G))) =
      (fun G : Bilin => inverseEntries G i j) := by
    funext G
    simp only [matrixEntry, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk,
      AddHom.coe_mk, inverseEntries, Matrix.nonsing_inv_eq_ringInverse]
    rfl
  change HasFDerivAt (fun G : Bilin =>
    matrixEntry i j (Ring.inverse (coordinateMatrix G))) _ G0 at hE
  rw [hfun] at hE
  convert hE using 1
  ext H
  simp only [inverseEntryDerivative, entryCLM, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.neg_apply, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.apply_apply,
    matrixEntry, coordinateMatrix, LinearMap.coe_toContinuousLinearMap',
    LinearMap.coe_mk, AddHom.coe_mk, ContinuousLinearMap.mulLeftRight_apply,
    hInv, Matrix.neg_apply, Matrix.mul_apply, smul_eq_mul]
  rw [Finset.sum_comm]
  simp only [Finset.sum_mul]
  apply congrArg Neg.neg
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  ring

end MatrixCalculation
end Poincare.DeTurckInverseEntryDerivative
