import Poincare.Global.ParabolicHolderMultiplier
import Poincare.Global.DuhamelSolutionOperatorBound
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.RCLike

noncomputable section

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

namespace Poincare.ParabolicCutoffCommutator

open Set ParabolicHolder ParabolicSolutionGraph
open scoped ContDiff

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
    have hc := div_mul_cancel₀ (2 * A) (ne_of_gt hη)
    calc
      η * (2 * A / η + η / 2 * B) = (2 * A / η) * η + B * η ^ 2 / 2 := by ring
      _ = _ := by rw [hc]
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
    have hc : δ / Real.sqrt δ = Real.sqrt δ := by
      apply (div_eq_iff (ne_of_gt hp)).2
      nlinarith
    rw [show 2 * (δ * M) / Real.sqrt δ = 2 * M * (δ / Real.sqrt δ) by ring, hc]
    ring
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

/-- Split a power at a larger positive scale. -/
theorem power_scale_bound {r R a b : ℝ} (hr : 0 ≤ r) (_hR : 0 < R)
    (hrR : r ≤ R) (_ha : 0 ≤ a) (hab : a ≤ b) (hb : 0 < b) :
    r ^ b ≤ R ^ (b - a) * r ^ a := by
  have he : r ^ b = r ^ (b - a) * r ^ a := by
    rw [← Real.rpow_add' hr (by linarith : b - a + a ≠ 0)]
    congr 1
    ring
  rw [he]
  exact mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow hr hrR (sub_nonneg.mpr hab)) (Real.rpow_nonneg hr a)

/-- Interpolate a Lipschitz bound and a bound at scale R. -/
theorem scale_interpolation {a L r R α : ℝ}
    (hL : 0 ≤ L) (hr : 0 ≤ r) (hR : 0 < R) (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (hl : a ≤ L * r) (hb : a ≤ L * R) :
    a ≤ L * R ^ (1 - α) * r ^ α := by
  by_cases h : r ≤ R
  · have hp := power_scale_bound hr hR h hα hα1 zero_lt_one
    rw [Real.rpow_one] at hp
    exact hl.trans (by nlinarith [mul_le_mul_of_nonneg_left hp hL])
  · have he : R ^ (1 - α) * R ^ α = R := by
      rw [← Real.rpow_add hR]
      convert Real.rpow_one R using 2
      ring
    calc
      a ≤ L * R := hb
      _ = L * R ^ (1 - α) * R ^ α := by rw [mul_assoc, he]
      _ ≤ L * R ^ (1 - α) * r ^ α := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow hR.le (le_of_not_ge h) hα) (by positivity)

/-- The parabolic spatial scale is the square root of the time scale. -/
theorem sqrt_rpow (hT : 0 ≤ T) (p : ℝ) :
    (Real.sqrt T) ^ p = T ^ (p / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hT]
  congr 1
  ring

/-- Spatial Hölder gradient increments carry the desired positive time power. -/
theorem gradient_space_holder (G : Graph (E := E) α T)
    (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T)
    {t : ℝ} (ht : t ∈ Icc 0 T) (x y : E) :
    ‖G.du (t, x) - G.du (t, y)‖ ≤
      6 * T ^ ((1 - α) / 2) * ‖G‖ * ‖x - y‖ ^ α := by
  have h := scale_interpolation (a := ‖G.du (t, x) - G.du (t, y)‖)
    (L := 6 * ‖G‖) (by positivity)
    (norm_nonneg (x - y)) (Real.sqrt_pos.mpr hT) hα.le hα1.le
    ((gradient_space_increment G ht x y).trans (by nlinarith [norm_nonneg G, norm_nonneg (x-y)]))
    ((norm_sub_le (G.du (t,x)) (G.du (t,y))).trans
      (by linarith [gradient_bound G hT ht x, gradient_bound G hT ht y]))
  rw [sqrt_rpow hT.le] at h
  nlinarith [h]

/-- Spatial Hölder value increments gain one additional half power of time. -/
theorem value_space_holder (G : Graph (E := E) α T)
    (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T)
    {t : ℝ} (ht : t ∈ Icc 0 T) (x y : E) :
    |G.u (t, x) - G.u (t, y)| ≤
      3 * T ^ (1 - α / 2) * ‖G‖ * ‖x - y‖ ^ α := by
  have hu (z : E) : |G.u (t, z)| ≤ T * ‖G‖ :=
    (time_bound G ht z).trans (mul_le_mul ht.2 (norm_ut_le G) (norm_nonneg _) hT.le)
  have h := scale_interpolation (a := |G.u (t, x) - G.u (t, y)|)
    (L := 3 * Real.sqrt T * ‖G‖) (by positivity)
    (norm_nonneg (x-y)) (Real.sqrt_pos.mpr hT) hα.le hα1.le
    (value_space_increment G hT ht x y)
    ((abs_sub _ _).trans (by
      have hs := congrArg (fun z : ℝ => z * ‖G‖) (Real.sq_sqrt hT.le)
      nlinarith [hu x, hu y, mul_nonneg hT.le (norm_nonneg G)]))
  have he : Real.sqrt T * (Real.sqrt T) ^ (1 - α) = T ^ (1 - α / 2) := by
    nth_rw 1 [← Real.rpow_one (Real.sqrt T)]
    rw [← Real.rpow_add (Real.sqrt_pos.mpr hT)]
    rw [sqrt_rpow hT.le]
    congr 1
    ring
  calc
    |G.u (t,x) - G.u (t,y)| ≤ _ := h
    _ = _ := by rw [show 3 * Real.sqrt T * ‖G‖ * (Real.sqrt T) ^ (1 - α) =
        3 * (Real.sqrt T * (Real.sqrt T) ^ (1 - α)) * ‖G‖ by ring, he]

/-- The temporal Hölder gradient bound follows from the square-root increment. -/
theorem gradient_time_holder (G : Graph (E := E) α T)
    (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T)
    {s t : ℝ} (hs : s ∈ Icc 0 T) (ht : t ∈ Icc 0 T) (x : E) :
    ‖G.du (t, x) - G.du (s, x)‖ ≤
      3 * T ^ ((1 - α) / 2) * ‖G‖ * |t - s| ^ (α / 2) := by
  have hδ : |t-s| ≤ T := abs_le.mpr ⟨by linarith [hs.2, ht.1], by linarith [ht.2, hs.1]⟩
  have hp := power_scale_bound (abs_nonneg (t-s)) hT hδ
    (show 0 ≤ α / 2 by linarith) (show α / 2 ≤ 1 / 2 by linarith)
    (show (0 : ℝ) < 1 / 2 by norm_num)
  rw [show (1 / 2 : ℝ) - α / 2 = (1 - α) / 2 by ring] at hp
  have hi := gradient_time_increment G hs ht x
  rw [Real.sqrt_eq_rpow] at hi
  nlinarith [mul_le_mul_of_nonneg_left hp (show 0 ≤ 3 * ‖G‖ by positivity)]

/-- Time-Lipschitz values have the stronger temporal Hölder gain. -/
theorem value_time_holder (G : Graph (E := E) α T)
    (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T)
    {s t : ℝ} (hs : s ∈ Icc 0 T) (ht : t ∈ Icc 0 T) (x : E) :
    |G.u (t, x) - G.u (s, x)| ≤
      T ^ (1 - α / 2) * ‖G‖ * |t - s| ^ (α / 2) := by
  have hδ : |t-s| ≤ T := abs_le.mpr ⟨by linarith [hs.2, ht.1], by linarith [ht.2, hs.1]⟩
  have hp := power_scale_bound (abs_nonneg (t-s)) hT hδ
    (show 0 ≤ α / 2 by linarith) (show α / 2 ≤ 1 by linarith) zero_lt_one
  rw [Real.rpow_one] at hp
  exact (value_time_increment G hs ht x).trans (by
    nlinarith [mul_le_mul_of_nonneg_right hp (norm_nonneg G)])

omit [NormedSpace ℝ E] in
/-- Split a mixed increment through the point with the first time and second position. -/
theorem holder_of_increments {F : Type*} [NormedAddCommGroup F]
    {f : ℝ × E → F} {Kx Kt : ℝ} (hα : 0 ≤ α) (hx : 0 ≤ Kx) (ht : 0 ≤ Kt)
    (hspace : ∀ t ∈ Icc 0 T, ∀ x y,
      ‖f (t,x) - f (t,y)‖ ≤ Kx * ‖x-y‖ ^ α)
    (htime : ∀ s ∈ Icc 0 T, ∀ t ∈ Icc 0 T, ∀ x,
      ‖f (t,x) - f (s,x)‖ ≤ Kt * |t-s| ^ (α/2)) :
    HasHolderBound α (cylinder T) f (Kx + Kt) := by
  intro p hp q hq
  have hxpow : ‖p.2-q.2‖ ^ α ≤ parabolicDist p q ^ α :=
    Real.rpow_le_rpow (norm_nonneg _) (by
      dsimp [parabolicDist]; linarith [Real.sqrt_nonneg |p.1-q.1|]) hα
  have htpow : |p.1-q.1| ^ (α/2) ≤ parabolicDist p q ^ α := by
    rw [← sqrt_rpow (abs_nonneg (p.1-q.1)) α]
    exact Real.rpow_le_rpow (Real.sqrt_nonneg _) (by
      dsimp [parabolicDist]; linarith [norm_nonneg (p.2-q.2)]) hα
  calc
    ‖f p - f q‖ ≤ ‖f p - f (p.1,q.2)‖ + ‖f (p.1,q.2) - f q‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ Kx * ‖p.2-q.2‖ ^ α + Kt * |p.1-q.1| ^ (α/2) :=
      add_le_add (hspace p.1 hp.1 p.2 q.2) (htime q.1 hq.1 p.1 hp.1 q.2)
    _ ≤ (Kx + Kt) * parabolicDist p q ^ α := by
      nlinarith [mul_le_mul_of_nonneg_left hxpow hx, mul_le_mul_of_nonneg_left htpow ht]

/-- Full gradient Hölder control, including mixed increments. -/
theorem gradient_holder (G : Graph (E := E) α T)
    (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T) :
    HasHolderBound α (cylinder T) G.du (9 * T ^ ((1 - α) / 2) * ‖G‖) := by
  have h := holder_of_increments hα.le
    (show 0 ≤ 6 * T ^ ((1-α)/2) * ‖G‖ by positivity)
    (show 0 ≤ 3 * T ^ ((1-α)/2) * ‖G‖ by positivity)
    (fun t ht => gradient_space_holder G hα hα1 hT ht)
    (fun s hs t ht => gradient_time_holder G hα hα1 hT hs ht)
  convert h using 1
  ring

/-- Full value Hölder control with its stronger time power. -/
theorem value_holder (G : Graph (E := E) α T)
    (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T) :
    HasHolderBound α (cylinder T) G.u (4 * T ^ (1 - α / 2) * ‖G‖) := by
  have h := holder_of_increments (f := G.u) hα.le
    (show 0 ≤ 3 * T ^ (1-α/2) * ‖G‖ by positivity)
    (show 0 ≤ T ^ (1-α/2) * ‖G‖ by positivity)
    (fun t ht x y => by simpa only [Real.norm_eq_abs] using value_space_holder G hα hα1 hT ht x y)
    (fun s hs t ht x => by simpa only [Real.norm_eq_abs] using value_time_holder G hα hα1 hT hs ht x)
  convert h using 1
  ring

/-- The complete lower-derivative norms gain positive powers on short cylinders. -/
theorem interpolation_bounds (G : Graph (E := E) α T)
    (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T) (hT1 : T ≤ 1) :
    ‖G.u‖ ≤ 12 * T ^ (1 - α / 2) * ‖G‖ ∧
    ‖G.du‖ ≤ 12 * T ^ ((1 - α) / 2) * ‖G‖ := by
  constructor
  · have h := ParabolicHolder.norm_le_of_bounds G.u
      (show 0 ≤ T * ‖G‖ by positivity)
      (show 0 ≤ 4 * T ^ (1-α/2) * ‖G‖ by positivity)
      (fun p hp => (time_bound G hp.1 p.2).trans
        (mul_le_mul hp.1.2 (norm_ut_le G) (norm_nonneg _) hT.le))
      (value_holder G hα hα1 hT)
    have hp : T ≤ T ^ (1-α/2) := by
      convert Real.rpow_le_rpow_of_exponent_ge hT hT1 (show 1-α/2 ≤ 1 by linarith) using 1
      exact (Real.rpow_one T).symm
    nlinarith [mul_le_mul_of_nonneg_right hp (norm_nonneg G),
      mul_nonneg (Real.rpow_nonneg hT.le (1-α/2)) (norm_nonneg G)]
  · have h := ParabolicHolder.norm_le_of_bounds G.du
      (show 0 ≤ 3 * Real.sqrt T * ‖G‖ by positivity)
      (show 0 ≤ 9 * T ^ ((1-α)/2) * ‖G‖ by positivity)
      (fun p hp => gradient_bound G hT hp.1 p.2)
      (gradient_holder G hα hα1 hT)
    have hp : Real.sqrt T ≤ T ^ ((1-α)/2) := by
      rw [Real.sqrt_eq_rpow]
      exact Real.rpow_le_rpow_of_exponent_ge hT hT1 (by linarith)
    nlinarith [mul_le_mul_of_nonneg_right hp (norm_nonneg G)]

/-- A universal constant satisfies the frozen interpolation target. -/
theorem interpolation : ∀ α : ℝ, 0 < α → α < 1 →
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 0 < T → T ≤ 1 → ∀ G : Graph (E := E) α T,
      ‖G.u‖ ≤ C * T ^ (1 - α / 2) * ‖G‖ ∧
      ‖G.du‖ ≤ C * T ^ ((1 - α) / 2) * ‖G‖ := by
  intro α hα hα1
  exact ⟨12, by norm_num, fun T hT hT1 G => interpolation_bounds G hα hα1 hT hT1⟩

/-- Smooth supported spatial data have uniformly bounded cylinder carriers. -/
theorem exists_cutoff_carrier {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {ψ : E → F} (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (hα : 0 < α) (hα1 : α < 1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ T : ℝ, ∃ f : Y (E := E) α T F,
      (∀ p ∈ cylinder T, f p = ψ p.2) ∧ ‖f‖ ≤ K := by
  classical
  obtain ⟨A, hA⟩ := hc.exists_bound_of_continuous hψ.continuous
  have hA0 : 0 ≤ A := (norm_nonneg (ψ 0)).trans (hA 0)
  obtain ⟨B, hB⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hc hψ (by simp)
  have hh (x y : E) : ‖ψ x - ψ y‖ ≤ (2 * A + B) * ‖x-y‖ ^ α := by
    have h := scale_interpolation (L := 2*A+B) (R := 1)
      (by positivity) (norm_nonneg (x-y)) zero_lt_one hα.le hα1.le
      ((hB.norm_sub_le x y).trans (by nlinarith [norm_nonneg (x-y), B.coe_nonneg]))
      ((norm_sub_le (ψ x) (ψ y)).trans (by linarith [hA x, hA y, B.coe_nonneg]))
    simpa using h
  refine ⟨A + (2*A+B), by positivity, ?_⟩
  intro T
  let f : ℝ × E → F := fun p => if p ∈ cylinder T then ψ p.2 else 0
  have hoff : ∀ p, p ∉ cylinder T → f p = 0 := by
    intro p hp; simp [f, hp]
  have hb : ∀ p ∈ cylinder T, ‖f p‖ ≤ A := by
    intro p hp; simpa [f, hp] using hA p.2
  have hholder : HasHolderBound α (cylinder T) f (2*A+B) := by
    intro p hp q hq
    simp only [f, if_pos hp, if_pos hq]
    exact (hh p.2 q.2).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (norm_nonneg _) (by
        dsimp [parabolicDist]; linarith [Real.sqrt_nonneg |p.1-q.1|]) hα.le) (by positivity))
  let fY := ofFunction f hoff ⟨A, hb⟩ ⟨2*A+B, hholder⟩
  refine ⟨fY, ?_, ?_⟩
  · intro p hp
    change f p = ψ p.2
    simp [f, hp]
  · exact ParabolicHolder.norm_le_of_bounds fY hA0 (by positivity) hb hholder

/-- The cutoff value, gradient, and Hessian all have genuine Hölder carriers. -/
theorem exists_cutoff_jet_carriers {ψ : E → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (hα : 0 < α) (hα1 : α < 1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ T : ℝ,
      ∃ (f : Y (E := E) α T ℝ)
        (df : Y (E := E) α T (E →L[ℝ] ℝ))
        (ddf : Y (E := E) α T (E →L[ℝ] E →L[ℝ] ℝ)),
      (∀ p ∈ cylinder T, f p = ψ p.2 ∧ df p = fderiv ℝ ψ p.2 ∧
        ddf p = fderiv ℝ (fderiv ℝ ψ) p.2) ∧
      ‖f‖ + ‖df‖ + ‖ddf‖ ≤ K := by
  have hdψ : ContDiff ℝ ∞ (fderiv ℝ ψ) := hψ.fderiv_right (by simp)
  have hddψ : ContDiff ℝ ∞ (fderiv ℝ (fderiv ℝ ψ)) := hdψ.fderiv_right (by simp)
  obtain ⟨K0, hK0, h0⟩ := exists_cutoff_carrier hψ hc hα hα1
  obtain ⟨K1, hK1, h1⟩ := exists_cutoff_carrier hdψ (hc.fderiv ℝ) hα hα1
  obtain ⟨K2, hK2, h2⟩ := exists_cutoff_carrier hddψ ((hc.fderiv ℝ).fderiv ℝ) hα hα1
  refine ⟨K0+K1+K2, by positivity, ?_⟩
  intro T
  obtain ⟨f, hf, hfb⟩ := h0 T
  obtain ⟨df, hdf, hdfb⟩ := h1 T
  obtain ⟨ddf, hddf, hddfb⟩ := h2 T
  exact ⟨f, df, ddf, fun p hp => ⟨hf p hp, hdf p hp, hddf p hp⟩, by linarith⟩

/-- The first spatial product rule uses the cutoff derivative and the solution value. -/
theorem cutoff_hasFDeriv {ψ : E → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (G : Graph (E := E) α T) {t : ℝ} (ht : t ∈ Icc 0 T) (x : E) :
    HasFDerivAt (fun z => ψ z * G.u (t,z))
      (ψ x • G.du (t,x) + G.u (t,x) • fderiv ℝ ψ x) x :=
  (hψ.differentiable (by simp) x).hasFDerivAt.mul (G.hasFDeriv t ht x)

/-- The second spatial product rule includes both mixed Hessian terms. -/
theorem cutoff_hasFDeriv_du {ψ : E → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (G : Graph (E := E) α T) {t : ℝ} (ht : t ∈ Icc 0 T) (x : E) :
    HasFDerivAt (fun z => ψ z • G.du (t,z) + G.u (t,z) • fderiv ℝ ψ z)
      ((ψ x • G.ddu (t,x) + (fderiv ℝ ψ x).smulRight (G.du (t,x))) +
        (G.u (t,x) • fderiv ℝ (fderiv ℝ ψ) x +
          (G.du (t,x)).smulRight (fderiv ℝ ψ x))) x := by
  have hdψ : ContDiff ℝ ∞ (fderiv ℝ ψ) := hψ.fderiv_right (by simp)
  exact ((hψ.differentiable (by simp) x).hasFDerivAt.smul (G.hasFDeriv_du t ht x)).add
    ((G.hasFDeriv t ht x).smul (hdψ.differentiable (by simp) x).hasFDerivAt)

/-- A spatial cutoff is constant in the within-time product rule. -/
theorem cutoff_hasDeriv_time (ψ : E → ℝ) (G : Graph (E := E) α T)
    {t : ℝ} (ht : t ∈ Icc 0 T) (x : E) :
    HasDerivWithinAt (fun s => ψ x * G.u (s,x)) (ψ x * G.ut (t,x)) (Icc 0 T) t :=
  (G.hasDeriv_time t ht x).const_mul (ψ x)

section Bilinear
variable {F H J : Type*}
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup H] [NormedSpace ℝ H]
  [NormedAddCommGroup J] [NormedSpace ℝ J]

omit [NormedSpace ℝ E] in
/-- Continuous bilinear operations preserve the cylinder Hölder bound. -/
theorem bilinear_holder (B : F →L[ℝ] H →L[ℝ] J)
    (f : Y (E := E) α T F) (g : Y (E := E) α T H) :
    HasHolderBound α (cylinder T) (fun p => B (f p) (g p)) (2 * ‖B‖ * ‖f‖ * ‖g‖) := by
  intro p hp q hq
  have hf := ParabolicHolder.holder_le f hp hq
  have hg := ParabolicHolder.holder_le g hp hq
  have hf0 := ParabolicHolder.norm_le f p
  have hg0 := ParabolicHolder.norm_le g q
  have hp0 := Real.rpow_nonneg (parabolicDist_nonneg p q) α
  calc
    ‖B (f p) (g p) - B (f q) (g q)‖ =
        ‖B (f p) (g p - g q) + B (f p - f q) (g q)‖ := by
      congr 1
      simp only [map_sub, ContinuousLinearMap.sub_apply]
      abel
    _ ≤ ‖B (f p) (g p - g q)‖ + ‖B (f p - f q) (g q)‖ := norm_add_le _ _
    _ ≤ ‖B‖ * ‖f p‖ * ‖g p - g q‖ + ‖B‖ * ‖f p - f q‖ * ‖g q‖ :=
      add_le_add (B.le_opNorm₂ _ _) (B.le_opNorm₂ _ _)
    _ ≤ ‖B‖ * ‖f‖ * (‖g‖ * parabolicDist p q ^ α) +
        ‖B‖ * (‖f‖ * parabolicDist p q ^ α) * ‖g‖ := by
      apply add_le_add
      · exact mul_le_mul (mul_le_mul_of_nonneg_left hf0 (norm_nonneg B)) hg
          (norm_nonneg _) (by positivity)
      · exact mul_le_mul (mul_le_mul_of_nonneg_left hf (norm_nonneg B)) hg0
          (norm_nonneg _) (by positivity)
    _ = _ := by ring

/-- Pointwise application of a continuous bilinear map to two Hölder carriers. -/
def bilinearY (B : F →L[ℝ] H →L[ℝ] J)
    (f : Y (E := E) α T F) (g : Y (E := E) α T H) : Y (E := E) α T J :=
  ofFunction (fun p => B (f p) (g p))
    (fun p hp => by simp [zero_off f hp])
    ⟨‖B‖ * ‖f‖ * ‖g‖, fun p _ => (B.le_opNorm₂ _ _).trans
      (mul_le_mul (mul_le_mul_of_nonneg_left (ParabolicHolder.norm_le f p) (norm_nonneg B))
        (ParabolicHolder.norm_le g p) (norm_nonneg _) (by positivity))⟩
    ⟨2 * ‖B‖ * ‖f‖ * ‖g‖, bilinear_holder B f g⟩

omit [NormedSpace ℝ E] in
/-- The bilinear carrier norm has an explicit product bound. -/
theorem norm_bilinearY_le (B : F →L[ℝ] H →L[ℝ] J)
    (f : Y (E := E) α T F) (g : Y (E := E) α T H) :
    ‖bilinearY B f g‖ ≤ 3 * ‖B‖ * ‖f‖ * ‖g‖ := by
  have h := ParabolicHolder.norm_le_of_bounds (bilinearY B f g)
    (show 0 ≤ ‖B‖ * ‖f‖ * ‖g‖ by positivity)
    (show 0 ≤ 2 * ‖B‖ * ‖f‖ * ‖g‖ by positivity)
    (fun p _ => (B.le_opNorm₂ _ _).trans
      (mul_le_mul (mul_le_mul_of_nonneg_left (ParabolicHolder.norm_le f p) (norm_nonneg B))
        (ParabolicHolder.norm_le g p) (norm_nonneg _) (by positivity)))
    (bilinear_holder B f g)
  nlinarith [h]

end Bilinear

local instance hessianBoundedSMul : IsBoundedSMul ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  .of_norm_smul_le (fun c A => ContinuousLinearMap.opNorm_smul_le c A)

/-- Assemble the cutoff graph from its three spatial carriers. -/
def cutoffGraphOfCarriers {ψ : E → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (f : Y (E := E) α T ℝ) (df : Y (E := E) α T (E →L[ℝ] ℝ))
    (ddf : Y (E := E) α T (E →L[ℝ] E →L[ℝ] ℝ))
    (hf : ∀ p ∈ cylinder T, f p = ψ p.2)
    (hdf : ∀ p ∈ cylinder T, df p = fderiv ℝ ψ p.2)
    (hddf : ∀ p ∈ cylinder T, ddf p = fderiv ℝ (fderiv ℝ ψ) p.2)
    (G : Graph (E := E) α T) : Graph (E := E) α T where
  u := f * G.u
  ut := f * G.ut
  du := bilinearY (ContinuousLinearMap.lsmul ℝ ℝ) f G.du +
    bilinearY (ContinuousLinearMap.lsmul ℝ ℝ) G.u df
  ddu := (bilinearY (ContinuousLinearMap.lsmul ℝ ℝ (E := E →L[ℝ] E →L[ℝ] ℝ)) f G.ddu +
    bilinearY (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) df G.du) +
    (bilinearY (ContinuousLinearMap.lsmul ℝ ℝ (E := E →L[ℝ] E →L[ℝ] ℝ)) G.u ddf +
    bilinearY (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) G.du df)
  zero_trace := by intro x; simp [mul_apply, G.zero_trace]
  hasFDeriv := by
    intro t ht x
    have hmem (z : E) : (t,z) ∈ cylinder T := ⟨ht, mem_univ z⟩
    convert cutoff_hasFDeriv hψ G ht x using 1
    · funext z
      simp only [mul_apply, hf (t,z) (hmem z)]
    · simp only [add_apply, bilinearY, ofFunction_apply, ContinuousLinearMap.lsmul_apply,
        hf (t,x) (hmem x), hdf (t,x) (hmem x)]
  hasFDeriv_du := by
    intro t ht x
    have hmem (z : E) : (t,z) ∈ cylinder T := ⟨ht, mem_univ z⟩
    convert cutoff_hasFDeriv_du hψ G ht x using 1
    · funext z
      simp only [add_apply, bilinearY, ofFunction_apply, ContinuousLinearMap.lsmul_apply,
        hf (t,z) (hmem z), hdf (t,z) (hmem z)]
    · simp only [add_apply, bilinearY, ofFunction_apply, ContinuousLinearMap.lsmul_apply,
        hf (t,x) (hmem x), hdf (t,x) (hmem x), hddf (t,x) (hmem x)]
      rfl
  hasDeriv_time := by
    intro t ht x
    have he (s : ℝ) : (f * G.u) (s,x) = ψ x * G.u (s,x) := by
      by_cases hs : (s,x) ∈ cylinder T
      · simp [mul_apply, hf (s,x) hs]
      · simp [mul_apply, zero_off G.u hs]
    convert cutoff_hasDeriv_time ψ G ht x using 1
    · funext s; exact he s
    · simp [mul_apply, hf (t,x) ⟨ht, mem_univ x⟩]

/-- Equality of the four stored carriers determines a derivative graph. -/
theorem graph_ext_components {G H : Graph (E := E) α T}
    (hu : G.u = H.u) (hut : G.ut = H.ut) (hdu : G.du = H.du) (hddu : G.ddu = H.ddu) :
    G = H := by
  cases G
  cases H
  simp_all

/-- Multiplication by the fixed cutoff carriers is linear on derivative graphs. -/
def cutoffLinearMapOfCarriers {ψ : E → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (f : Y (E := E) α T ℝ) (df : Y (E := E) α T (E →L[ℝ] ℝ))
    (ddf : Y (E := E) α T (E →L[ℝ] E →L[ℝ] ℝ))
    (hf : ∀ p ∈ cylinder T, f p = ψ p.2)
    (hdf : ∀ p ∈ cylinder T, df p = fderiv ℝ ψ p.2)
    (hddf : ∀ p ∈ cylinder T, ddf p = fderiv ℝ (fderiv ℝ ψ) p.2) :
    Graph (E := E) α T →ₗ[ℝ] Graph (E := E) α T where
  toFun := cutoffGraphOfCarriers hψ f df ddf hf hdf hddf
  map_add' G H := by
    apply graph_ext_components
    · apply ParabolicHolder.ext
      intro p hp
      change f p * (G.u p + H.u p) = (f p * (G.u p)) + (f p * (H.u p))
      ring
    · apply ParabolicHolder.ext
      intro p hp
      change f p * (G.ut p + H.ut p) = (f p * (G.ut p)) + (f p * (H.ut p))
      ring
    · apply ParabolicHolder.ext
      intro p hp
      change f p • (G.du p + H.du p) + (G.u p + H.u p) • df p = (f p • (G.du p) + (G.u p) • df p) + (f p • (H.du p) + (H.u p) • df p)
      module
    · apply ParabolicHolder.ext
      intro p hp
      change (f p • (G.ddu p + H.ddu p) + (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (df p) (G.du p + H.du p)) + ((G.u p + H.u p) • ddf p + (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (G.du p + H.du p) (df p)) = ((f p • (G.ddu p) + (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (df p) (G.du p)) + ((G.u p) • ddf p + (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (G.du p) (df p))) + ((f p • (H.ddu p) + (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (df p) (H.du p)) + ((H.u p) • ddf p + (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (H.du p) (df p)))
      simp only [map_add, ContinuousLinearMap.add_apply]
      module
  map_smul' c G := by
    apply graph_ext_components
    · apply ParabolicHolder.ext
      intro p hp
      change f p * (c • G.u p) = c • (f p * (G.u p))
      ring
    · apply ParabolicHolder.ext
      intro p hp
      change f p * (c • G.ut p) = c • (f p * (G.ut p))
      ring
    · apply ParabolicHolder.ext
      intro p hp
      change f p • (c • G.du p) + (c • G.u p) • df p = c • (f p • (G.du p) + (G.u p) • df p)
      module
    · apply ParabolicHolder.ext
      intro p hp
      change (f p • (c • G.ddu p) + (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (df p) (c • G.du p)) + ((c • G.u p) • ddf p + (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (c • G.du p) (df p)) = c • ((f p • (G.ddu p) + (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (df p) (G.du p)) + ((G.u p) • ddf p + (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) (G.du p) (df p)))
      simp only [map_smul, ContinuousLinearMap.smul_apply]
      module


set_option maxHeartbeats 4000000 in
/-- The cutoff graph map is bounded in the original four-component norm. -/
theorem exists_cutoffGraph_bound {ψ : E → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (f : Y (E := E) α T ℝ) (df : Y (E := E) α T (E →L[ℝ] ℝ))
    (ddf : Y (E := E) α T (E →L[ℝ] E →L[ℝ] ℝ))
    (hf : ∀ p ∈ cylinder T, f p = ψ p.2)
    (hdf : ∀ p ∈ cylinder T, df p = fderiv ℝ ψ p.2)
    (hddf : ∀ p ∈ cylinder T, ddf p = fderiv ℝ (fderiv ℝ ψ) p.2) :
    ∃ C : ℝ, ∀ G : Graph (E := E) α T,
      ‖cutoffGraphOfCarriers hψ f df ddf hf hdf hddf G‖ ≤ C * ‖G‖ := by
  letI : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
  letI : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
  letI : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
  letI : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
  let L1 : ℝ →L[ℝ] (E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ) := ContinuousLinearMap.lsmul ℝ ℝ
  let L2 : ℝ →L[ℝ] (E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] E →L[ℝ] ℝ) :=
    ContinuousLinearMap.lsmul ℝ ℝ (E := E →L[ℝ] E →L[ℝ] ℝ)
  let Q : (E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] E →L[ℝ] ℝ) :=
    ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)
  let A := ‖f‖ + ‖df‖ + ‖ddf‖
  let B : ℝ := 1 + ‖L1‖ + ‖L2‖ + ‖Q‖
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hfA : ‖f‖ ≤ A := by change ‖f‖ ≤ ‖f‖ + ‖df‖ + ‖ddf‖; linarith [norm_nonneg df, norm_nonneg ddf]
  have hdfA : ‖df‖ ≤ A := by change _ ≤ ‖f‖ + ‖df‖ + ‖ddf‖; linarith [norm_nonneg f, norm_nonneg ddf]
  have hddfA : ‖ddf‖ ≤ A := by change _ ≤ ‖f‖ + ‖df‖ + ‖ddf‖; linarith [norm_nonneg f, norm_nonneg df]
  have hL1 : ‖L1‖ ≤ B := by dsimp [B]; linarith [norm_nonneg L2, norm_nonneg Q]
  have hL2 : ‖L2‖ ≤ B := by dsimp [B]; linarith [norm_nonneg L1, norm_nonneg Q]
  have hQ : ‖Q‖ ≤ B := by dsimp [B]; linarith [norm_nonneg L1, norm_nonneg L2]
  have hB1 : 1 ≤ B := by dsimp [B]; linarith [norm_nonneg L1, norm_nonneg L2, norm_nonneg Q]
  refine ⟨20 * B * A, ?_⟩
  intro G
  have hGu := norm_u_le G
  have hGut := norm_ut_le G
  have hGdu := norm_du_le G
  have hGddu := norm_ddu_le G
  have hu : ‖f * G.u‖ ≤ B * A * ‖G‖ := by
    calc
      ‖f * G.u‖ ≤ ‖f‖ * ‖G.u‖ := ParabolicHolder.norm_mul_le _ _
      _ ≤ B * A * ‖G‖ := by
        calc
          ‖f‖ * ‖G.u‖ ≤ A * ‖G‖ := mul_le_mul hfA hGu (norm_nonneg _) hA
          _ ≤ B * A * ‖G‖ := by nlinarith [mul_le_mul_of_nonneg_right hB1 (mul_nonneg hA (norm_nonneg G))]
  have hut : ‖f * G.ut‖ ≤ B * A * ‖G‖ := by
    calc
      ‖f * G.ut‖ ≤ ‖f‖ * ‖G.ut‖ := ParabolicHolder.norm_mul_le _ _
      _ ≤ B * A * ‖G‖ := by
        calc
          ‖f‖ * ‖G.ut‖ ≤ A * ‖G‖ := mul_le_mul hfA hGut (norm_nonneg _) hA
          _ ≤ B * A * ‖G‖ := by nlinarith [mul_le_mul_of_nonneg_right hB1 (mul_nonneg hA (norm_nonneg G))]
  have ha : ‖bilinearY L1 f G.du‖ ≤ 3 * B * A * ‖G‖ := by
    calc
      ‖bilinearY L1 f G.du‖ ≤ 3 * ‖L1‖ * ‖f‖ * ‖G.du‖ := norm_bilinearY_le _ _ _
      _ ≤ 3 * B * A * ‖G‖ := by gcongr
  have hb : ‖bilinearY L1 G.u df‖ ≤ 3 * B * A * ‖G‖ := by
    calc
      ‖bilinearY L1 G.u df‖ ≤ 3 * ‖L1‖ * ‖G.u‖ * ‖df‖ := norm_bilinearY_le _ _ _
      _ ≤ 3 * B * ‖G‖ * A := by gcongr
      _ = _ := by ring
  have hc : ‖bilinearY L2 f G.ddu‖ ≤ 3 * B * A * ‖G‖ := by
    calc
      ‖bilinearY L2 f G.ddu‖ ≤ 3 * ‖L2‖ * ‖f‖ * ‖G.ddu‖ := norm_bilinearY_le _ _ _
      _ ≤ 3 * B * A * ‖G‖ := by gcongr
  have hd : ‖bilinearY Q df G.du‖ ≤ 3 * B * A * ‖G‖ := by
    calc
      ‖bilinearY Q df G.du‖ ≤ 3 * ‖Q‖ * ‖df‖ * ‖G.du‖ := norm_bilinearY_le _ _ _
      _ ≤ 3 * B * A * ‖G‖ := by gcongr
  have he : ‖bilinearY L2 G.u ddf‖ ≤ 3 * B * A * ‖G‖ := by
    calc
      ‖bilinearY L2 G.u ddf‖ ≤ 3 * ‖L2‖ * ‖G.u‖ * ‖ddf‖ := norm_bilinearY_le _ _ _
      _ ≤ 3 * B * ‖G‖ * A := by gcongr
      _ = _ := by ring
  have hk : ‖bilinearY Q G.du df‖ ≤ 3 * B * A * ‖G‖ := by
    calc
      ‖bilinearY Q G.du df‖ ≤ 3 * ‖Q‖ * ‖G.du‖ * ‖df‖ := norm_bilinearY_le _ _ _
      _ ≤ 3 * B * ‖G‖ * A := by gcongr
      _ = _ := by ring
  rw [ParabolicSolutionGraph.norm_eq]
  change ‖f * G.u‖ + ‖f * G.ut‖ +
    ‖bilinearY L1 f G.du + bilinearY L1 G.u df‖ +
    ‖(bilinearY L2 f G.ddu + bilinearY Q df G.du) +
      (bilinearY L2 G.u ddf + bilinearY Q G.du df)‖ ≤ _
  have hdu := norm_add_le (bilinearY L1 f G.du) (bilinearY L1 G.u df)
  have hddu := norm_add_le (bilinearY L2 f G.ddu + bilinearY Q df G.du)
    (bilinearY L2 G.u ddf + bilinearY Q G.du df)
  have hdd0 := norm_add_le (bilinearY L2 f G.ddu) (bilinearY Q df G.du)
  have hdd1 := norm_add_le (bilinearY L2 G.u ddf) (bilinearY Q G.du df)
  nlinarith

/-- Smooth compact cutoffs act by bounded linear maps with the actual product jets. -/
theorem exists_cutoff_operator {ψ : E → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hc : HasCompactSupport ψ) (hα : 0 < α) (hα1 : α < 1) :
    ∃ C : Graph (E := E) α T →L[ℝ] Graph (E := E) α T,
      (∀ G p, (C G).u p = ψ p.2 * G.u p) ∧
      (∀ G t, t ∈ Icc 0 T → ∀ x,
        (C G).ut (t,x) = ψ x * G.ut (t,x) ∧
        (C G).du (t,x) = ψ x • G.du (t,x) + G.u (t,x) • fderiv ℝ ψ x ∧
        (C G).ddu (t,x) =
          (ψ x • G.ddu (t,x) + (fderiv ℝ ψ x).smulRight (G.du (t,x))) +
          (G.u (t,x) • fderiv ℝ (fderiv ℝ ψ) x +
            (G.du (t,x)).smulRight (fderiv ℝ ψ x))) := by
  obtain ⟨K, hK, hcarriers⟩ := exists_cutoff_jet_carriers hψ hc hα hα1
  obtain ⟨f, df, ddf, heq, hnorm⟩ := hcarriers T
  have hf := fun p hp => (heq p hp).1
  have hdf := fun p hp => (heq p hp).2.1
  have hddf := fun p hp => (heq p hp).2.2
  obtain ⟨B, hB⟩ := exists_cutoffGraph_bound hψ f df ddf hf hdf hddf
  let L := cutoffLinearMapOfCarriers hψ f df ddf hf hdf hddf
  let C := L.mkContinuous B hB
  refine ⟨C, ?_, ?_⟩
  · intro G p
    change f p * G.u p = ψ p.2 * G.u p
    by_cases hp : p ∈ cylinder T
    · rw [hf p hp]
    · simp [zero_off G.u hp]
  · intro G t ht x
    have hp : (t,x) ∈ cylinder T := ⟨ht, mem_univ x⟩
    change f (t,x) * G.ut (t,x) = _ ∧
      (bilinearY (ContinuousLinearMap.lsmul ℝ ℝ) f G.du +
        bilinearY (ContinuousLinearMap.lsmul ℝ ℝ) G.u df) (t,x) = _ ∧ _
    refine ⟨by rw [hf (t,x) hp], ?_, ?_⟩
    · simp only [add_apply, bilinearY, ofFunction_apply, ContinuousLinearMap.lsmul_apply,
        hf (t,x) hp, hdf (t,x) hp]
    · change (cutoffGraphOfCarriers hψ f df ddf hf hdf hddf G).ddu (t,x) = _
      simp only [cutoffGraphOfCarriers, add_apply, bilinearY, ofFunction_apply, ContinuousLinearMap.lsmul_apply,
        hf (t,x) hp, hdf (t,x) hp, hddf (t,x) hp]
      rfl

end Poincare.ParabolicCutoffCommutator
