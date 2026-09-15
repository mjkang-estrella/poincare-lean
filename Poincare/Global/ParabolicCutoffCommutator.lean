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

end Poincare.ParabolicCutoffCommutator
