import Poincare.Global.ParabolicHolderMultiplier
import Poincare.Global.DuhamelSolutionOperatorBound
import Mathlib.Analysis.Calculus.MeanValue

noncomputable section

namespace Poincare.ParabolicCutoffCommutator

open Set ParabolicHolder ParabolicSolutionGraph

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A bounded Hessian gives the quadratic remainder along a unit direction. -/
theorem quadratic_remainder
    {h : E → ℝ} {dh : E → E →L[ℝ] ℝ}
    {ddh : E → E →L[ℝ] E →L[ℝ] ℝ} {B η : ℝ}
    (hd : ∀ x, HasFDerivAt h (dh x) x)
    (hdd : ∀ x, HasFDerivAt dh (ddh x) x)
    (hb : ∀ x, ‖ddh x‖ ≤ B) (hη : 0 ≤ η)
    (x v : E) (hv : ‖v‖ = 1) :
    |h (x + η • v) - h x - η * dh x v| ≤ B * η ^ 2 / 2 := by
  have hlip (y : E) : ‖dh y - dh x‖ ≤ B * ‖y - x‖ :=
    Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
      (fun z _ => (hdd z).hasFDerivWithinAt) (fun z _ => hb z)
      convex_univ (mem_univ x) (mem_univ y)
  have hdline (s : ℝ) : HasDerivAt (fun s : ℝ => h (x + s • v))
      (dh (x + s • v) v) s := by
    simpa using (hd (x + s • v)).comp_hasDerivAt s
      (((hasDerivAt_id s).smul_const v).const_add x)
  have hdr (s : ℝ) : HasDerivAt
      (fun s : ℝ => h (x + s • v) - h x - s * dh x v)
      (dh (x + s • v) v - dh x v) s := by
    simpa using ((hdline s).sub_const (h x)).sub
      ((hasDerivAt_id s).mul_const (dh x v))
  have hquad (s : ℝ) : HasDerivAt (fun s : ℝ => B * s ^ 2 / 2) (B * s) s := by
    convert (((hasDerivAt_id s).pow 2).const_mul B).div_const 2 using 1
    simp only [id_eq]
    ring
  have hr := image_norm_le_of_norm_deriv_right_le_deriv_boundary
    (fun s _ => (hdr s).continuousAt.continuousWithinAt)
    (fun s _ => (hdr s).hasDerivWithinAt)
    (by simp : ‖h (x + (0 : ℝ) • v) - h x - 0 * dh x v‖ ≤ B * 0 ^ 2 / 2)
    hquad (fun s hs => ?_) (show η ∈ Icc 0 η from ⟨hη, le_rfl⟩)
  · exact hr
  · calc
      ‖dh (x + s • v) v - dh x v‖ = ‖(dh (x + s • v) - dh x) v‖ := rfl
      _ ≤ ‖dh (x + s • v) - dh x‖ := by
        simpa [hv] using (dh (x + s • v) - dh x).le_opNorm v
      _ ≤ B * s := by simpa [norm_smul, hv, abs_of_nonneg hs.1] using hlip (x + s • v)

/-- The finite-difference estimate with an arbitrary positive step. -/
theorem finite_difference_derivative
    {h : E → ℝ} {dh : E → E →L[ℝ] ℝ}
    {ddh : E → E →L[ℝ] E →L[ℝ] ℝ} {A B η : ℝ}
    (hd : ∀ x, HasFDerivAt h (dh x) x)
    (hdd : ∀ x, HasFDerivAt dh (ddh x) x)
    (ha : ∀ x, |h x| ≤ A) (hb : ∀ x, ‖ddh x‖ ≤ B)
    (hη : 0 < η) (x v : E) (hv : ‖v‖ = 1) :
    |dh x v| ≤ 2 * A / η + (η / 2) * B := by
  have hr := quadratic_remainder hd hdd hb hη.le x v hv
  have hu : |h (x + η • v) - h x| ≤ 2 * A :=
    (abs_sub _ _).trans (by linarith [ha (x + η • v), ha x])
  have ht : |η * dh x v| ≤ 2 * A + B * η ^ 2 / 2 := by
    calc
      |η * dh x v| = |(h (x + η • v) - h x) -
          (h (x + η • v) - h x - η * dh x v)| := by ring_nf
      _ ≤ |h (x + η • v) - h x| +
          |h (x + η • v) - h x - η * dh x v| := abs_sub _ _
      _ ≤ _ := add_le_add hu hr
  rw [abs_mul, abs_of_pos hη] at ht
  apply (mul_le_mul_iff_right₀ hη).mp
  have he : η * (2 * A / η + η / 2 * B) = 2 * A + B * η ^ 2 / 2 := by
    field_simp
  rw [he]
  nlinarith

end Poincare.ParabolicCutoffCommutator
