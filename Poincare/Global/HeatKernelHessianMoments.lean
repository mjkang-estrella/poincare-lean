import Poincare.Global.HeatCauchyNext2
import Poincare.Global.HeatSemigroupBUCPositiveGenerator
import Poincare.Global.RiemannianContext
import Mathlib.Analysis.SpecificLimits.Normed

noncomputable section

open MeasureTheory
open scoped Topology RealInnerProductSpace

namespace Poincare.HeatKernelHessianMoments

local notation "E" => Poincare.ClosedSmoothModel 3
local instance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local notation "Hess" => fun (t : ℝ) (x : E) =>
  fderiv ℝ (fderiv ℝ (fun z : E => Poincare.heatKernel t z)) x

/-- Dilation of the full spatial Hessian in dimension three. -/
theorem hessian_sq_smul (a : ℝ) (ha : 0 < a) (x : E) :
    Hess (a ^ 2) (a • x) = ((a ^ 3)⁻¹ * (a ^ 2)⁻¹) • Hess 1 x := by
  ext v w
  have hformula (t : ℝ) (ht : t ≠ 0) (u : E) :=
    iteratedFDeriv_two_heatKernel_apply_bilinear_for_domination ht u v w
  simp [iteratedFDeriv_two_apply] at hformula
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [hformula _ (pow_ne_zero _ ha.ne'), hformula _ one_ne_zero,
    heatKernel_sq_smul a ha x]
  simp only [inner_smul_left, conj_trivial, finrank_euclideanSpace_fin]
  field_simp

/-- A fractional radial weight is absorbed by a fixed Gaussian. -/
theorem rpow_mul_gaussian_le_eight {α : ℝ} (hα : 0 ≤ α) (hα2 : α ≤ 2)
    {r : ℝ} (hr : 0 ≤ r) : r ^ α * Real.exp (-(r ^ 2 / 8)) ≤ 8 := by
  have hpoly : r ^ α ≤ 1 + r ^ 2 := by
    by_cases hr1 : r ≤ 1
    · exact (Real.rpow_le_one hr hr1 hα).trans (by nlinarith [sq_nonneg r])
    · have h := Real.rpow_le_rpow_of_exponent_le (le_of_not_ge hr1) hα2
      rw [Real.rpow_two] at h
      linarith
  have hbound : 1 + r ^ 2 ≤ 8 * Real.exp (r ^ 2 / 8) := by
    have h := Real.add_one_le_exp (r ^ 2 / 8)
    linarith
  calc
    r ^ α * Real.exp (-(r ^ 2 / 8)) ≤
        (8 * Real.exp (r ^ 2 / 8)) * Real.exp (-(r ^ 2 / 8)) :=
      mul_le_mul_of_nonneg_right (hpoly.trans hbound) (Real.exp_pos _).le
    _ = 8 := by rw [mul_assoc, ← Real.exp_add]; simp

end Poincare.HeatKernelHessianMoments
