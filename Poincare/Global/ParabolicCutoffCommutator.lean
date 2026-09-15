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

/-- Optimizing the step gives a square-root bound on the full derivative. -/
theorem derivative_norm_le_sqrt
    {h : E → ℝ} {dh : E → E →L[ℝ] ℝ}
    {ddh : E → E →L[ℝ] E →L[ℝ] ℝ} {δ M : ℝ}
    (hd : ∀ x, HasFDerivAt h (dh x) x)
    (hdd : ∀ x, HasFDerivAt dh (ddh x) x)
    (hδ : 0 < δ) (hM : 0 ≤ M)
    (ha : ∀ x, |h x| ≤ δ * M) (hb : ∀ x, ‖ddh x‖ ≤ 2 * M)
    (x : E) : ‖dh x‖ ≤ 3 * Real.sqrt δ * M := by
  apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
  intro v hv
  have h := finite_difference_derivative hd hdd ha hb (Real.sqrt_pos.mpr hδ) x v hv
  have he : 2 * (δ * M) / Real.sqrt δ + Real.sqrt δ / 2 * (2 * M) =
      3 * Real.sqrt δ * M := by
    have hs := Real.sq_sqrt hδ.le
    have hp := Real.sqrt_pos.mpr hδ
    field_simp
    nlinarith [congrArg (fun z : ℝ => z * M) hs]
  exact h.trans_eq he

variable {α T : ℝ}

/-- Time increments of the value are controlled by the stored time derivative. -/
theorem value_time_increment (G : Graph (E := E) α T)
    {s t : ℝ} (hs : s ∈ Icc 0 T) (ht : t ∈ Icc 0 T) (x : E) :
    |G.u (t, x) - G.u (s, x)| ≤ |t - s| * ‖G‖ := by
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun r hr => G.hasDeriv_time r hr x)
    (fun r _ => sup_ut_le G (r, x)) (convex_Icc (0 : ℝ) T) hs ht
  simpa only [Real.norm_eq_abs, mul_comm] using h

/-- The gradient of any derivative graph is uniformly small at short times. -/
theorem gradient_bound (G : Graph (E := E) α T) (hT : 0 < T)
    {t : ℝ} (ht : t ∈ Icc 0 T) (x : E) :
    ‖G.du (t, x)‖ ≤ 3 * Real.sqrt T * ‖G‖ := by
  apply derivative_norm_le_sqrt (G.hasFDeriv t ht) (G.hasFDeriv_du t ht) hT
    (norm_nonneg G) ?_ ?_ x
  · intro y
    calc
      |G.u (t, y)| ≤ t * ‖G.ut‖ := time_bound G ht y
      _ ≤ T * ‖G‖ := mul_le_mul ht.2 (norm_ut_le G) (norm_nonneg _) hT.le
  · intro y
    exact (sup_ddu_le G (t, y)).trans (by linarith [norm_nonneg G])

/-- The supremum of the gradient has the same square-root gain. -/
theorem supNorm_gradient_le (G : Graph (E := E) α T) (hT : 0 < T) :
    supNorm (cylinder T) G.du ≤ 3 * Real.sqrt T * ‖G‖ := by
  apply csSup_le (insert_nonempty _ _)
  rintro r (rfl | ⟨p, rfl⟩)
  · positivity
  · exact gradient_bound G hT p.property.1 p.val.2

/-- Time differences of the gradient require no mixed time-space derivative. -/
theorem gradient_time_increment (G : Graph (E := E) α T)
    {s t : ℝ} (hs : s ∈ Icc 0 T) (ht : t ∈ Icc 0 T) (x : E) :
    ‖G.du (t, x) - G.du (s, x)‖ ≤ 3 * Real.sqrt |t - s| * ‖G‖ := by
  by_cases hst : t = s
  · simp [hst]
  · apply derivative_norm_le_sqrt
      (fun y => (G.hasFDeriv t ht y).sub (G.hasFDeriv s hs y))
      (fun y => (G.hasFDeriv_du t ht y).sub (G.hasFDeriv_du s hs y))
      (abs_pos.mpr (sub_ne_zero.mpr hst)) (norm_nonneg G)
      (value_time_increment G hs ht) ?_ x
    intro y
    exact (norm_sub_le (G.ddu (t, y)) (G.ddu (s, y))).trans
      (by linarith [sup_ddu_le G (t, y), sup_ddu_le G (s, y)])

/-- Spatial gradient increments are Lipschitz with the Hessian bound. -/
theorem gradient_space_increment (G : Graph (E := E) α T)
    {t : ℝ} (ht : t ∈ Icc 0 T) (x y : E) :
    ‖G.du (t, x) - G.du (t, y)‖ ≤ ‖G‖ * ‖x - y‖ :=
  Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun z _ => (G.hasFDeriv_du t ht z).hasFDerivWithinAt)
    (fun z _ => sup_ddu_le G (t, z)) convex_univ (mem_univ y) (mem_univ x)

/-- Spatial value increments inherit the improved gradient bound. -/
theorem value_space_increment (G : Graph (E := E) α T) (hT : 0 < T)
    {t : ℝ} (ht : t ∈ Icc 0 T) (x y : E) :
    |G.u (t, x) - G.u (t, y)| ≤ (3 * Real.sqrt T * ‖G‖) * ‖x - y‖ :=
  Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun z _ => (G.hasFDeriv t ht z).hasFDerivWithinAt)
    (fun z _ => gradient_bound G hT ht z) convex_univ (mem_univ y) (mem_univ x)

end Poincare.ParabolicCutoffCommutator
