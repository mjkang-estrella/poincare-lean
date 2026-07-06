import Poincare.Global.HeatKernel
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Pointwise heat-kernel PDE identities

This file continues `Poincare.Global.HeatKernel` with the first pointwise
calculus facts for the explicit Gaussian heat kernel.  The general time
derivative is stated in product-rule form.  The fully closed PDE identity is
proved in one spatial dimension and then transported to the Laplacian notation.
-/

noncomputable section

open scoped InnerProductSpace Laplacian

namespace Poincare

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private lemma heatKernel_time_exponent_hasDerivAt {c t : ℝ} (ht : t ≠ 0) :
    HasDerivAt (fun τ : ℝ ↦ (-c) / (4 * τ)) (c / (4 * t ^ 2)) t := by
  convert ((hasDerivAt_inv ht).const_mul (-(c / 4))) using 1
  · ext τ
    ring
  · field_simp [pow_two]

/--
The positive-time derivative of the heat kernel in the time variable.

The right-hand side is intentionally left in the exact product-rule form:
derivative of the normalization plus derivative of the exponential factor.
-/
theorem hasDerivAt_heatKernel_time [FiniteDimensional ℝ E] {t : ℝ} (ht : 0 < t) (x : E) :
    HasDerivAt (fun τ : ℝ ↦ heatKernel (E := E) τ x)
      (((4 * Real.pi) * (-(Module.finrank ℝ E : ℝ) / 2) *
          (4 * Real.pi * t) ^ (-(Module.finrank ℝ E : ℝ) / 2 - 1)) *
          Real.exp (-(‖x‖ ^ 2) / (4 * t)) +
        (4 * Real.pi * t) ^ (-(Module.finrank ℝ E : ℝ) / 2) *
          (Real.exp (-(‖x‖ ^ 2) / (4 * t)) * (‖x‖ ^ 2 / (4 * t ^ 2)))) t := by
  have hbase_pos : 0 < 4 * Real.pi * t := by
    exact mul_pos (mul_pos (by norm_num) Real.pi_pos) ht
  have hnorm :
      HasDerivAt
        (fun τ : ℝ ↦ (4 * Real.pi * τ) ^ (-(Module.finrank ℝ E : ℝ) / 2))
        ((4 * Real.pi) * (-(Module.finrank ℝ E : ℝ) / 2) *
          (4 * Real.pi * t) ^ (-(Module.finrank ℝ E : ℝ) / 2 - 1)) t := by
    simpa [mul_assoc] using
      (((hasDerivAt_id t).const_mul (4 * Real.pi)).rpow_const
        (p := (-(Module.finrank ℝ E : ℝ) / 2)) (Or.inl hbase_pos.ne'))
  have hexp :
      HasDerivAt (fun τ : ℝ ↦ Real.exp (-(‖x‖ ^ 2) / (4 * τ)))
        (Real.exp (-(‖x‖ ^ 2) / (4 * t)) * (‖x‖ ^ 2 / (4 * t ^ 2))) t :=
    (heatKernel_time_exponent_hasDerivAt (c := ‖x‖ ^ 2) ht.ne').exp
  simpa [heatKernel] using hnorm.mul hexp

/-- The positive-time derivative as a `deriv` equality. -/
theorem deriv_heatKernel_time [FiniteDimensional ℝ E] {t : ℝ} (ht : 0 < t) (x : E) :
    deriv (fun τ : ℝ ↦ heatKernel (E := E) τ x) t =
      ((4 * Real.pi) * (-(Module.finrank ℝ E : ℝ) / 2) *
          (4 * Real.pi * t) ^ (-(Module.finrank ℝ E : ℝ) / 2 - 1)) *
          Real.exp (-(‖x‖ ^ 2) / (4 * t)) +
        (4 * Real.pi * t) ^ (-(Module.finrank ℝ E : ℝ) / 2) *
          (Real.exp (-(‖x‖ ^ 2) / (4 * t)) * (‖x‖ ^ 2 / (4 * t ^ 2))) :=
  (hasDerivAt_heatKernel_time (E := E) ht x).deriv

/-- The one-dimensional Gaussian formula obtained by unfolding `heatKernel (E := ℝ)`. -/
def heatKernelReal (t x : ℝ) : ℝ :=
  (4 * Real.pi * t) ^ (-(1 : ℝ) / 2) * Real.exp (-(x ^ 2) / (4 * t))

theorem heatKernel_real_eq (t x : ℝ) :
    heatKernel (E := ℝ) t x = heatKernelReal t x := by
  unfold heatKernel heatKernelReal
  simp [Module.finrank_self, Real.norm_eq_abs, sq_abs]

private lemma heatKernelReal_space_exponent_hasDerivAt {t x : ℝ} (ht : t ≠ 0) :
    HasDerivAt (fun y : ℝ ↦ -(y ^ 2) / (4 * t)) (-(x / (2 * t))) x := by
  have hsq : HasDerivAt (fun y : ℝ ↦ y ^ 2) (2 * x) x := by
    simpa using (hasDerivAt_id x).pow 2
  convert hsq.neg.div_const (4 * t) using 1
  · field_simp [ht]
    ring

private lemma hasDerivAt_heatKernelReal_space {t x : ℝ} (ht : t ≠ 0) :
    HasDerivAt (fun y : ℝ ↦ heatKernelReal t y)
      (heatKernelReal t x * (-(x / (2 * t)))) x := by
  have hexp :
      HasDerivAt (fun y : ℝ ↦ Real.exp (-(y ^ 2) / (4 * t)))
        (Real.exp (-(x ^ 2) / (4 * t)) * (-(x / (2 * t)))) x :=
    (heatKernelReal_space_exponent_hasDerivAt (t := t) ht).exp
  simpa [heatKernelReal, mul_assoc] using
    ((hasDerivAt_const x ((4 * Real.pi * t) ^ (-(1 : ℝ) / 2))).mul hexp)

private lemma deriv_heatKernelReal_space {t x : ℝ} (ht : t ≠ 0) :
    deriv (fun y : ℝ ↦ heatKernelReal t y) x =
      heatKernelReal t x * (-(x / (2 * t))) :=
  (hasDerivAt_heatKernelReal_space (t := t) (x := x) ht).deriv

private lemma hasDerivAt_heatKernelReal_space_deriv {t x : ℝ} (ht : t ≠ 0) :
    HasDerivAt (fun y : ℝ ↦ heatKernelReal t y * (-(y / (2 * t))))
      (heatKernelReal t x * (x ^ 2 / (4 * t ^ 2) - 1 / (2 * t))) x := by
  have hk := hasDerivAt_heatKernelReal_space (t := t) (x := x) ht
  have hlin : HasDerivAt (fun y : ℝ ↦ -(y / (2 * t))) (-(1 / (2 * t))) x := by
    simpa using ((hasDerivAt_id x).div_const (2 * t)).neg
  convert hk.mul hlin using 1
  field_simp [ht]
  ring

private lemma iteratedDeriv_two_heatKernelReal {t x : ℝ} (ht : t ≠ 0) :
    iteratedDeriv 2 (fun y : ℝ ↦ heatKernelReal t y) x =
      heatKernelReal t x * (x ^ 2 / (4 * t ^ 2) - 1 / (2 * t)) := by
  rw [show iteratedDeriv 2 (fun y : ℝ ↦ heatKernelReal t y) =
      deriv (iteratedDeriv 1 (fun y : ℝ ↦ heatKernelReal t y)) by
    simpa using (iteratedDeriv_succ (n := 1) (f := fun y : ℝ ↦ heatKernelReal t y))]
  rw [iteratedDeriv_one]
  rw [show deriv (fun y : ℝ ↦ heatKernelReal t y) =
      fun y : ℝ ↦ heatKernelReal t y * (-(y / (2 * t))) by
    funext y
    exact deriv_heatKernelReal_space (t := t) (x := y) ht]
  exact (hasDerivAt_heatKernelReal_space_deriv (t := t) (x := x) ht).deriv

private lemma heatKernelReal_time_deriv {t x : ℝ} (ht : 0 < t) :
    deriv (fun τ : ℝ ↦ heatKernelReal τ x) t =
      heatKernelReal t x * (x ^ 2 / (4 * t ^ 2) - 1 / (2 * t)) := by
  have hbase_pos : 0 < 4 * Real.pi * t := by
    exact mul_pos (mul_pos (by norm_num) Real.pi_pos) ht
  rw [show (fun τ : ℝ ↦ heatKernelReal τ x) = fun τ : ℝ ↦ heatKernel (E := ℝ) τ x by
    funext τ
    exact (heatKernel_real_eq τ x).symm]
  rw [deriv_heatKernel_time (E := ℝ) ht]
  unfold heatKernelReal
  simp [Module.finrank_self, Real.norm_eq_abs, sq_abs]
  rw [Real.rpow_sub_one hbase_pos.ne' (-(1 : ℝ) / 2)]
  field_simp [ht.ne', Real.pi_ne_zero]
  ring

/--
The one-dimensional heat equation for the explicit real Gaussian:
the time derivative equals the second spatial derivative.
-/
theorem heatKernelReal_heatEquation {t x : ℝ} (ht : 0 < t) :
    deriv (fun τ : ℝ ↦ heatKernelReal τ x) t =
      iteratedDeriv 2 (fun y : ℝ ↦ heatKernelReal t y) x := by
  rw [heatKernelReal_time_deriv ht, iteratedDeriv_two_heatKernelReal ht.ne']

/--
The one-dimensional heat equation for `heatKernel (E := ℝ)`.
-/
theorem heatKernel_real_heatEquation {t x : ℝ} (ht : 0 < t) :
    deriv (fun τ : ℝ ↦ heatKernel (E := ℝ) τ x) t =
      iteratedDeriv 2 (fun y : ℝ ↦ heatKernel (E := ℝ) t y) x := by
  rw [show (fun τ : ℝ ↦ heatKernel (E := ℝ) τ x) = fun τ : ℝ ↦ heatKernelReal τ x by
    funext τ
    exact heatKernel_real_eq τ x]
  rw [show (fun y : ℝ ↦ heatKernel (E := ℝ) t y) = fun y : ℝ ↦ heatKernelReal t y by
    funext y
    exact heatKernel_real_eq t y]
  exact heatKernelReal_heatEquation ht

/-- The same one-dimensional identity in Mathlib's Laplacian notation. -/
theorem heatKernel_real_heatEquation_laplacian {t x : ℝ} (ht : 0 < t) :
    deriv (fun τ : ℝ ↦ heatKernel (E := ℝ) τ x) t =
      (Δ fun y : ℝ ↦ heatKernel (E := ℝ) t y) x := by
  rw [InnerProductSpace.laplacian_eq_iteratedDeriv_real]
  exact heatKernel_real_heatEquation ht

end Poincare
