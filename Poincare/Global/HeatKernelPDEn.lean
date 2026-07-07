import Poincare.Global.HeatKernelPDE

/-!
# The finite-dimensional Euclidean heat-kernel PDE

This file closes the positive-time heat equation for the explicit Gaussian
heat kernel on a finite-dimensional real inner-product space.  The final
theorem keeps the target statement from `M2-heat-2`: the only spelling
adaptation is the explicit `(E := E)` arguments already used throughout the
heat-kernel files.
-/

noncomputable section

open scoped InnerProductSpace Laplacian

namespace Poincare

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- First spatial derivative of the negative scaled squared norm. -/
theorem hasFDerivAt_neg_norm_sq_div (t : ℝ) (ht : t ≠ 0) (x : E) :
    HasFDerivAt (fun y : E ↦ -(‖y‖ ^ 2) / (4 * t))
      ((-(1 / (2 * t))) • (innerSL ℝ x)) x := by
  have h := (hasStrictFDerivAt_norm_sq x).hasFDerivAt.const_mul (-(1 / (4 * t)))
  convert h using 1
  · ext y
    field_simp [ht]
  · ext y
    simp
    field_simp [ht]
    ring

/-- First spatial derivative of `exp (-(‖x‖²)/(4t))`. -/
theorem hasFDerivAt_exp_neg_norm_sq_div (t : ℝ) (ht : t ≠ 0) (x : E) :
    HasFDerivAt (fun y : E ↦ Real.exp (-(‖y‖ ^ 2) / (4 * t)))
      (Real.exp (-(‖x‖ ^ 2) / (4 * t)) • ((-(1 / (2 * t))) • (innerSL ℝ x))) x := by
  exact (hasFDerivAt_neg_norm_sq_div (E := E) t ht x).exp

private lemma fderiv_exp_neg_norm_sq_div (t : ℝ) (ht : t ≠ 0) (x : E) :
    fderiv ℝ (fun y : E ↦ Real.exp (-(‖y‖ ^ 2) / (4 * t))) x =
      Real.exp (-(‖x‖ ^ 2) / (4 * t)) • ((-(1 / (2 * t))) • (innerSL ℝ x)) :=
  (hasFDerivAt_exp_neg_norm_sq_div (E := E) t ht x).fderiv

private lemma hasFDerivAt_fderiv_exp_neg_norm_sq_div (t : ℝ) (ht : t ≠ 0) (x : E) :
    HasFDerivAt
      (fun y : E ↦ fderiv ℝ (fun z : E ↦ Real.exp (-(‖z‖ ^ 2) / (4 * t))) y)
      (let A : E →L[ℝ] E →L[ℝ] ℝ := (-(1 / (2 * t))) • (innerSL ℝ)
       Real.exp (-(‖x‖ ^ 2) / (4 * t)) • A +
          (Real.exp (-(‖x‖ ^ 2) / (4 * t)) • A x).smulRight (A x)) x := by
  let A : E →L[ℝ] E →L[ℝ] ℝ := (-(1 / (2 * t))) • (innerSL ℝ)
  have hfun :
      (fun y : E ↦ fderiv ℝ (fun z : E ↦ Real.exp (-(‖z‖ ^ 2) / (4 * t))) y) =
        fun y : E ↦ Real.exp (-(‖y‖ ^ 2) / (4 * t)) • A y := by
    funext y
    rw [fderiv_exp_neg_norm_sq_div (E := E) t ht y]
    rfl
  rw [hfun]
  exact (hasFDerivAt_exp_neg_norm_sq_div (E := E) t ht x).smul
    (ContinuousLinearMap.hasFDerivAt A)

/--
The diagonal second Fréchet derivative of the unnormalised spatial Gaussian
`x ↦ exp (-(‖x‖²)/(4t))`.
-/
theorem iteratedFDeriv_two_exp_neg_norm_sq_div_apply (t : ℝ) (ht : t ≠ 0)
    (x v : E) :
    iteratedFDeriv ℝ 2 (fun y : E ↦ Real.exp (-(‖y‖ ^ 2) / (4 * t))) x ![v, v] =
      Real.exp (-(‖x‖ ^ 2) / (4 * t)) *
        (⟪x, v⟫_ℝ ^ 2 / (4 * t ^ 2) - ‖v‖ ^ 2 / (2 * t)) := by
  rw [iteratedFDeriv_two_apply]
  rw [(hasFDerivAt_fderiv_exp_neg_norm_sq_div (E := E) t ht x).fderiv]
  dsimp
  ring_nf
  change Real.exp (‖x‖ ^ 2 * t⁻¹ * (-1 / 4)) * ((t⁻¹ * (-1 / 2)) * ⟪v, v⟫_ℝ) +
      Real.exp (‖x‖ ^ 2 * t⁻¹ * (-1 / 4)) * ((t⁻¹ * (-1 / 2)) * ⟪x, v⟫_ℝ) ^ 2 =
    t⁻¹ * Real.exp (‖x‖ ^ 2 * t⁻¹ * (-1 / 4)) * ‖v‖ ^ 2 * (-1 / 2) +
      t⁻¹ ^ 2 * Real.exp (‖x‖ ^ 2 * t⁻¹ * (-1 / 4)) * ⟪x, v⟫_ℝ ^ 2 * (1 / 4)
  rw [real_inner_self_eq_norm_sq]
  ring_nf

/-- Parseval's identity for the standard finite-dimensional orthonormal basis. -/
theorem sum_sq_inner_stdOrthonormalBasis [FiniteDimensional ℝ E] (x : E) :
    (∑ i : Fin (Module.finrank ℝ E), ⟪x, (stdOrthonormalBasis ℝ E) i⟫_ℝ ^ 2) = ‖x‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq x]
  calc
    (∑ i : Fin (Module.finrank ℝ E), ⟪x, (stdOrthonormalBasis ℝ E) i⟫_ℝ ^ 2)
        = ∑ i : Fin (Module.finrank ℝ E),
            ⟪x, (stdOrthonormalBasis ℝ E) i⟫_ℝ * ⟪(stdOrthonormalBasis ℝ E) i, x⟫_ℝ := by
          apply Finset.sum_congr rfl
          intro i _hi
          rw [real_inner_comm]
          ring
    _ = ⟪x, x⟫_ℝ := by
          exact (stdOrthonormalBasis ℝ E).sum_inner_mul_inner x x

/-- Laplacian of the unnormalised spatial Gaussian. -/
theorem laplacian_exp_neg_norm_sq_div [FiniteDimensional ℝ E] (t : ℝ) (ht : t ≠ 0) (x : E) :
    (Δ fun y : E ↦ Real.exp (-(‖y‖ ^ 2) / (4 * t))) x =
      Real.exp (-(‖x‖ ^ 2) / (4 * t)) *
        (‖x‖ ^ 2 / (4 * t ^ 2) - (Module.finrank ℝ E : ℝ) / (2 * t)) := by
  let b := stdOrthonormalBasis ℝ E
  have hlap : (Δ fun y : E ↦ Real.exp (-(‖y‖ ^ 2) / (4 * t))) x =
      ∑ i : Fin (Module.finrank ℝ E),
        iteratedFDeriv ℝ 2 (fun y : E ↦ Real.exp (-(‖y‖ ^ 2) / (4 * t))) x ![b i, b i] := by
    simpa [b] using congrFun
      (InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis
        (fun y : E ↦ Real.exp (-(‖y‖ ^ 2) / (4 * t))) b) x
  rw [hlap]
  simp_rw [iteratedFDeriv_two_exp_neg_norm_sq_div_apply (E := E) t ht x]
  simp [b, OrthonormalBasis.norm_eq_one]
  rw [← Finset.mul_sum]
  congr 1
  rw [Finset.sum_sub_distrib]
  rw [← Finset.sum_div]
  rw [sum_sq_inner_stdOrthonormalBasis (E := E) x]
  simp
  ring

/--
The positive-time heat equation for the finite-dimensional Euclidean heat kernel.
-/
theorem heatKernel_heatEquation_laplacian
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {t : ℝ} (ht : 0 < t) (x : E) :
    deriv (fun τ : ℝ ↦ heatKernel (E := E) τ x) t =
      (Δ fun y : E ↦ heatKernel (E := E) t y) x := by
  rw [deriv_heatKernel_time (E := E) ht x]
  unfold heatKernel
  let A : ℝ := (4 * Real.pi * t) ^ (-(Module.finrank ℝ E : ℝ) / 2)
  let G : E → ℝ := fun y ↦ Real.exp (-(‖y‖ ^ 2) / (4 * t))
  have hG : ContDiffAt ℝ 2 G x := by
    dsimp [G]
    exact (((contDiff_norm_sq ℝ).neg.div_const (4 * t)).exp).contDiffAt
  have hR : (Δ fun y : E ↦ A * G y) x = A * (Δ G) x := by
    rw [show (fun y : E ↦ A * G y) = A • G by rfl]
    simpa [smul_eq_mul] using InnerProductSpace.laplacian_smul (E := E) (𝕜 := ℝ)
      (F := ℝ) (x := x) (f := G) A hG
  change ((4 * Real.pi) * (-(Module.finrank ℝ E : ℝ) / 2) *
          (4 * Real.pi * t) ^ (-(Module.finrank ℝ E : ℝ) / 2 - 1)) *
          Real.exp (-(‖x‖ ^ 2) / (4 * t)) +
        A * (Real.exp (-(‖x‖ ^ 2) / (4 * t)) * (‖x‖ ^ 2 / (4 * t ^ 2))) =
      (Δ fun y : E ↦ A * G y) x
  rw [hR]
  rw [laplacian_exp_neg_norm_sq_div (E := E) t ht.ne' x]
  dsimp [A, G]
  have hbase_pos : 0 < 4 * Real.pi * t := by
    exact mul_pos (mul_pos (by norm_num) Real.pi_pos) ht
  rw [Real.rpow_sub_one hbase_pos.ne' (-(Module.finrank ℝ E : ℝ) / 2)]
  field_simp [ht.ne', Real.pi_ne_zero]
  ring

end Poincare
