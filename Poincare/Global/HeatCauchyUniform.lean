import Poincare.Global.HeatCauchyFrechet

/-!
# Uniform translate envelopes for the heat Cauchy problem

This file starts the `M2-heat-13` surface.  It isolates a closed-ball translate
estimate for the Euclidean heat kernel: for `x` in `closedBall x₀ R`, the
Gaussian in `x - y`, multiplied by any polynomial factor of order at most
three, is dominated by one fixed integrable Gaussian-polynomial function of
`y`.

The constants are intentionally generous.  They keep the statement elementary
and stable enough to feed the spatial dominated-differentiation layer.
-/

noncomputable section

open MeasureTheory
open scoped Topology InnerProductSpace Laplacian

namespace Poincare

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

section Measurable

variable [MeasurableSpace E] [BorelSpace E]

/-- The fixed `y`-Gaussian used for closed-ball translate envelopes. -/
def heatKernelUniformTranslateEnvelope (t A : ℝ) (y : E) : ℝ :=
  A * ((1 + ‖y‖ ^ 2) * Real.exp (-(1 / (16 * t)) * ‖y‖ ^ 2))

/-- A deliberately broad constant absorbing polynomial orders `0,1,2,3`. -/
def heatKernelUniformTranslateConstant (t M : ℝ) : ℝ :=
  (4 * Real.pi * t) ^ (-(Module.finrank ℝ E : ℝ) / 2) *
    Real.exp (M ^ 2 / (4 * t)) *
      (8 * (1 + M) ^ 3 * (1 + 32 * t) ^ 2)

/-- Integrability of the fixed uniform translate envelope. -/
theorem integrable_heatKernelUniformTranslateEnvelope {t : ℝ} (ht : 0 < t) (A : ℝ) :
    Integrable (fun y : E => heatKernelUniformTranslateEnvelope (E := E) t A y) := by
  have ha : 0 < 1 / (16 * t) := by positivity
  exact (integrable_one_add_norm_sq_mul_exp_neg_mul_norm_sq (E := E) ha).const_mul A

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Norm control for `x` in `closedBall x₀ R`. -/
theorem norm_le_center_add_radius {R : ℝ} {x₀ x : E}
    (hx : x ∈ Metric.closedBall x₀ R) :
    ‖x‖ ≤ ‖x₀‖ + R := by
  have hdist : dist x x₀ ≤ R := by
    simpa [Metric.mem_closedBall] using hx
  calc
    ‖x‖ = ‖x₀ + (x - x₀)‖ := by
      congr 1
      abel
    _ ≤ ‖x₀‖ + ‖x - x₀‖ := norm_add_le _ _
    _ = ‖x₀‖ + dist x x₀ := by rw [dist_eq_norm]
    _ ≤ ‖x₀‖ + R := by nlinarith [hdist]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Quadratic lower bound behind the translate Gaussian estimate. -/
theorem half_norm_sq_sub_norm_sq_le_norm_sub_sq (x y : E) :
    (1 / 2 : ℝ) * ‖y‖ ^ 2 - ‖x‖ ^ 2 ≤ ‖x - y‖ ^ 2 := by
  have hy : ‖y‖ ≤ ‖x - y‖ + ‖x‖ := by
    calc
      ‖y‖ = ‖x - (x - y)‖ := by
        congr 1
        abel
      _ ≤ ‖x‖ + ‖x - y‖ := norm_sub_le x (x - y)
      _ = ‖x - y‖ + ‖x‖ := by ring
  have hy_sq : ‖y‖ ^ 2 ≤ (‖x - y‖ + ‖x‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg y) hy 2
  have hquad : (‖x - y‖ + ‖x‖) ^ 2 ≤ 2 * ‖x - y‖ ^ 2 + 2 * ‖x‖ ^ 2 := by
    nlinarith [sq_nonneg (‖x - y‖ - ‖x‖)]
  nlinarith [hy_sq.trans hquad]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- A quadratic polynomial is absorbed by a widened Gaussian. -/
theorem one_add_sq_le_exp_quarter {a r : ℝ} (ha : 0 < a) :
    1 + r ^ 2 ≤ (1 + 4 / a) * Real.exp ((a / 4) * r ^ 2) := by
  set q : ℝ := (a / 4) * r ^ 2
  have hq_nonneg : 0 ≤ q := by
    dsimp [q]
    positivity
  have hq_le_exp : q ≤ Real.exp q := by
    exact (le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp q)
  have hr2_le : r ^ 2 ≤ (4 / a) * Real.exp q := by
    calc
      r ^ 2 = (4 / a) * q := by
        dsimp [q]
        field_simp [ha.ne']
      _ ≤ (4 / a) * Real.exp q := by
        exact mul_le_mul_of_nonneg_left hq_le_exp (by positivity)
  have hone_le : 1 ≤ Real.exp q := Real.one_le_exp hq_nonneg
  have hfour_nonneg : 0 ≤ 4 / a := by positivity
  calc
    1 + r ^ 2 ≤ Real.exp q + (4 / a) * Real.exp q :=
      add_le_add hone_le hr2_le
    _ = (1 + 4 / a) * Real.exp q := by ring

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/--
Uniform polynomial absorption for every order up to three.  The right-hand side
keeps only the quadratic polynomial used by the envelope and widens the
Gaussian by a factor of two.
-/
theorem add_pow_le_cubic_absorbed_gaussian {a M r : ℝ} (ha : 0 < a)
    (hM : 0 ≤ M) (hr : 0 ≤ r) {m : ℕ} (hm : m ≤ 3) :
    (M + r) ^ m * Real.exp (-a * r ^ 2) ≤
      (8 * (1 + M) ^ 3 * (1 + 4 / a) ^ 2) *
        ((1 + r ^ 2) * Real.exp (-(a / 2) * r ^ 2)) := by
  set B : ℝ := 2 * (1 + M) * (1 + r ^ 2)
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    positivity
  have hB_one : 1 ≤ B := by
    dsimp [B]
    nlinarith [sq_nonneg r, hM]
  have hMr_le_B : M + r ≤ B := by
    dsimp [B]
    nlinarith [sq_nonneg r, sq_nonneg (r - 1), hM, hr]
  have hMr_nonneg : 0 ≤ M + r := add_nonneg hM hr
  have hpow_le_Bpow : (M + r) ^ m ≤ B ^ m :=
    pow_le_pow_left₀ hMr_nonneg hMr_le_B m
  have hBpow_le_B3 : B ^ m ≤ B ^ 3 := by
    exact pow_le_pow_right₀ hB_one hm
  have hpoly :
      (M + r) ^ m ≤ 8 * (1 + M) ^ 3 * (1 + r ^ 2) ^ 3 := by
    calc
      (M + r) ^ m ≤ B ^ m := hpow_le_Bpow
      _ ≤ B ^ 3 := hBpow_le_B3
      _ = 8 * (1 + M) ^ 3 * (1 + r ^ 2) ^ 3 := by
        dsimp [B]
        ring
  have hquad := one_add_sq_le_exp_quarter (a := a) (r := r) ha
  have hquad_nonneg : 0 ≤ 1 + r ^ 2 := by positivity
  have hBquad_nonneg : 0 ≤ (1 + 4 / a) * Real.exp ((a / 4) * r ^ 2) := by
    positivity
  have hquad_sq :
      (1 + r ^ 2) ^ 2 ≤
        ((1 + 4 / a) * Real.exp ((a / 4) * r ^ 2)) ^ 2 :=
    pow_le_pow_left₀ hquad_nonneg hquad 2
  have hexp_nonneg : 0 ≤ Real.exp (-a * r ^ 2) := (Real.exp_pos _).le
  calc
    (M + r) ^ m * Real.exp (-a * r ^ 2)
        ≤ (8 * (1 + M) ^ 3 * (1 + r ^ 2) ^ 3) *
            Real.exp (-a * r ^ 2) := by
          exact mul_le_mul_of_nonneg_right hpoly hexp_nonneg
    _ = (8 * (1 + M) ^ 3) *
          ((1 + r ^ 2) ^ 2 * ((1 + r ^ 2) * Real.exp (-a * r ^ 2))) := by
          ring
    _ ≤ (8 * (1 + M) ^ 3) *
          ((((1 + 4 / a) * Real.exp ((a / 4) * r ^ 2)) ^ 2) *
            ((1 + r ^ 2) * Real.exp (-a * r ^ 2))) := by
          refine mul_le_mul_of_nonneg_left ?_ ?_
          · exact mul_le_mul_of_nonneg_right hquad_sq
              (mul_nonneg hquad_nonneg hexp_nonneg)
          · positivity
    _ = (8 * (1 + M) ^ 3 * (1 + 4 / a) ^ 2) *
          ((1 + r ^ 2) * Real.exp (-(a / 2) * r ^ 2)) := by
          have hexp_sq :
              Real.exp ((a / 4) * r ^ 2) ^ 2 =
                Real.exp ((a / 2) * r ^ 2) := by
            rw [pow_two, ← Real.exp_add]
            congr 1
            ring
          have hexp_mul :
              Real.exp ((a / 2) * r ^ 2) * Real.exp (-a * r ^ 2) =
                Real.exp (-(a / 2) * r ^ 2) := by
            rw [← Real.exp_add]
            congr 1
            ring
          rw [show ((1 + 4 / a) * Real.exp ((a / 4) * r ^ 2)) ^ 2 =
              (1 + 4 / a) ^ 2 * Real.exp ((a / 4) * r ^ 2) ^ 2 by ring]
          rw [hexp_sq]
          calc
            8 * (1 + M) ^ 3 *
                ((1 + 4 / a) ^ 2 * Real.exp ((a / 2) * r ^ 2) *
                  ((1 + r ^ 2) * Real.exp (-a * r ^ 2)))
                =
              8 * (1 + M) ^ 3 * (1 + 4 / a) ^ 2 *
                ((1 + r ^ 2) *
                  (Real.exp ((a / 2) * r ^ 2) * Real.exp (-a * r ^ 2))) := by
                ring
            _ = 8 * (1 + M) ^ 3 * (1 + 4 / a) ^ 2 *
                ((1 + r ^ 2) * Real.exp (-(a / 2) * r ^ 2)) := by
                rw [hexp_mul]

omit [MeasurableSpace E] [BorelSpace E] in
/--
Closed-ball translate domination for heat kernels with a polynomial factor of
order at most three.
-/
theorem heatKernel_translate_polynomial_le_uniformEnvelope {t R : ℝ} (ht : 0 < t)
    (hR : 0 ≤ R) {x₀ x y : E} (hx : x ∈ Metric.closedBall x₀ R)
    {m : ℕ} (hm : m ≤ 3) :
    ‖x - y‖ ^ m * heatKernel (E := E) t (x - y) ≤
      heatKernelUniformTranslateEnvelope (E := E) t
        (heatKernelUniformTranslateConstant (E := E) t (‖x₀‖ + R)) y := by
  set M : ℝ := ‖x₀‖ + R
  set a : ℝ := 1 / (8 * t)
  have hM_nonneg : 0 ≤ M := by
    dsimp [M]
    positivity
  have ha : 0 < a := by
    dsimp [a]
    positivity
  have hx_norm : ‖x‖ ≤ M := by
    simpa [M] using norm_le_center_add_radius (E := E) hx
  have hx_sq : ‖x‖ ^ 2 ≤ M ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg x) hx_norm 2
  have hquad := half_norm_sq_sub_norm_sq_le_norm_sub_sq (E := E) x y
  have hquadM : (1 / 2 : ℝ) * ‖y‖ ^ 2 - M ^ 2 ≤ ‖x - y‖ ^ 2 := by
    nlinarith [hquad, hx_sq]
  have hden_pos : 0 < 4 * t := by positivity
  have h_exp_arg :
      -(‖x - y‖ ^ 2) / (4 * t) ≤ M ^ 2 / (4 * t) - a * ‖y‖ ^ 2 := by
    dsimp [a]
    field_simp [ht.ne']
    nlinarith [hquadM]
  have h_exp_le :
      Real.exp (-(‖x - y‖ ^ 2) / (4 * t)) ≤
        Real.exp (M ^ 2 / (4 * t)) * Real.exp (-a * ‖y‖ ^ 2) := by
    calc
      Real.exp (-(‖x - y‖ ^ 2) / (4 * t))
          ≤ Real.exp (M ^ 2 / (4 * t) - a * ‖y‖ ^ 2) :=
        Real.exp_le_exp.mpr h_exp_arg
      _ = Real.exp (M ^ 2 / (4 * t)) * Real.exp (-a * ‖y‖ ^ 2) := by
        rw [← Real.exp_add]
        ring_nf
  have hnorm_sub : ‖x - y‖ ≤ M + ‖y‖ := by
    calc
      ‖x - y‖ ≤ ‖x‖ + ‖y‖ := norm_sub_le x y
      _ ≤ M + ‖y‖ := by nlinarith [hx_norm]
  have hpoly :
      ‖x - y‖ ^ m ≤ (M + ‖y‖) ^ m :=
    pow_le_pow_left₀ (norm_nonneg _) hnorm_sub m
  have hpoly_exp :
      ‖x - y‖ ^ m * Real.exp (-a * ‖y‖ ^ 2) ≤
        (8 * (1 + M) ^ 3 * (1 + 4 / a) ^ 2) *
          ((1 + ‖y‖ ^ 2) * Real.exp (-(a / 2) * ‖y‖ ^ 2)) := by
    calc
      ‖x - y‖ ^ m * Real.exp (-a * ‖y‖ ^ 2)
          ≤ (M + ‖y‖) ^ m * Real.exp (-a * ‖y‖ ^ 2) := by
        exact mul_le_mul_of_nonneg_right hpoly (Real.exp_pos _).le
      _ ≤ (8 * (1 + M) ^ 3 * (1 + 4 / a) ^ 2) *
          ((1 + ‖y‖ ^ 2) * Real.exp (-(a / 2) * ‖y‖ ^ 2)) :=
        add_pow_le_cubic_absorbed_gaussian (a := a) (M := M) (r := ‖y‖)
          ha hM_nonneg (norm_nonneg y) hm
  have hpref_nonneg :
      0 ≤ (4 * Real.pi * t) ^ (-(Module.finrank ℝ E : ℝ) / 2) := by
    positivity
  have hMexp_nonneg : 0 ≤ Real.exp (M ^ 2 / (4 * t)) := (Real.exp_pos _).le
  unfold heatKernel heatKernelUniformTranslateEnvelope heatKernelUniformTranslateConstant
  calc
    ‖x - y‖ ^ m *
        ((4 * Real.pi * t) ^ (-(Module.finrank ℝ E : ℝ) / 2) *
          Real.exp (-(‖x - y‖ ^ 2) / (4 * t)))
        ≤ ‖x - y‖ ^ m *
            ((4 * Real.pi * t) ^ (-(Module.finrank ℝ E : ℝ) / 2) *
              (Real.exp (M ^ 2 / (4 * t)) * Real.exp (-a * ‖y‖ ^ 2))) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact mul_le_mul_of_nonneg_left h_exp_le hpref_nonneg
    _ = ((4 * Real.pi * t) ^ (-(Module.finrank ℝ E : ℝ) / 2) *
            Real.exp (M ^ 2 / (4 * t))) *
          (‖x - y‖ ^ m * Real.exp (-a * ‖y‖ ^ 2)) := by ring
    _ ≤ ((4 * Real.pi * t) ^ (-(Module.finrank ℝ E : ℝ) / 2) *
            Real.exp (M ^ 2 / (4 * t))) *
          ((8 * (1 + M) ^ 3 * (1 + 4 / a) ^ 2) *
            ((1 + ‖y‖ ^ 2) * Real.exp (-(a / 2) * ‖y‖ ^ 2))) := by
          exact mul_le_mul_of_nonneg_left hpoly_exp (mul_nonneg hpref_nonneg hMexp_nonneg)
    _ =
        ((4 * Real.pi * t) ^ (-(Module.finrank ℝ E : ℝ) / 2) *
            Real.exp (M ^ 2 / (4 * t)) *
              (8 * (1 + M) ^ 3 * (1 + 32 * t) ^ 2)) *
          ((1 + ‖y‖ ^ 2) * Real.exp (-(1 / (16 * t)) * ‖y‖ ^ 2)) := by
          dsimp [a]
          field_simp [ht.ne']
          ring_nf

omit [MeasurableSpace E] [BorelSpace E] in
/-- The order-one instance of the closed-ball translate envelope. -/
theorem heatKernel_translate_order_one_le_uniformEnvelope {t R : ℝ} (ht : 0 < t)
    (hR : 0 ≤ R) {x₀ x y : E} (hx : x ∈ Metric.closedBall x₀ R) :
    ‖x - y‖ * heatKernel (E := E) t (x - y) ≤
      heatKernelUniformTranslateEnvelope (E := E) t
        (heatKernelUniformTranslateConstant (E := E) t (‖x₀‖ + R)) y := by
  simpa using
    (heatKernel_translate_polynomial_le_uniformEnvelope (E := E) ht hR hx
      (m := 1) (by norm_num))

omit [MeasurableSpace E] [BorelSpace E] in
/-- The order-two instance of the closed-ball translate envelope. -/
theorem heatKernel_translate_order_two_le_uniformEnvelope {t R : ℝ} (ht : 0 < t)
    (hR : 0 ≤ R) {x₀ x y : E} (hx : x ∈ Metric.closedBall x₀ R) :
    ‖x - y‖ ^ 2 * heatKernel (E := E) t (x - y) ≤
      heatKernelUniformTranslateEnvelope (E := E) t
        (heatKernelUniformTranslateConstant (E := E) t (‖x₀‖ + R)) y := by
  simpa using
    (heatKernel_translate_polynomial_le_uniformEnvelope (E := E) ht hR hx
      (m := 2) (by norm_num))

omit [MeasurableSpace E] [BorelSpace E] in
/-- The order-three instance of the closed-ball translate envelope. -/
theorem heatKernel_translate_order_three_le_uniformEnvelope {t R : ℝ} (ht : 0 < t)
    (hR : 0 ≤ R) {x₀ x y : E} (hx : x ∈ Metric.closedBall x₀ R) :
    ‖x - y‖ ^ 3 * heatKernel (E := E) t (x - y) ≤
      heatKernelUniformTranslateEnvelope (E := E) t
        (heatKernelUniformTranslateConstant (E := E) t (‖x₀‖ + R)) y := by
  exact heatKernel_translate_polynomial_le_uniformEnvelope (E := E) ht hR hx
    (m := 3) (by norm_num)

omit [MeasurableSpace E] [BorelSpace E] in
/-- First spatial Fréchet derivative operator norm, reduced to the order-one kernel factor. -/
theorem fderiv_heatKernel_norm_le_order_one {t : ℝ} (ht : 0 < t) (u : E) :
    ‖fderiv ℝ (fun z : E => heatKernel (E := E) t z) u‖ ≤
      (1 / (2 * t)) * (‖u‖ * heatKernel (E := E) t u) := by
  have hbound_nonneg :
      0 ≤ (1 / (2 * t)) * (‖u‖ * heatKernel (E := E) t u) := by
    exact mul_nonneg (by positivity)
      (mul_nonneg (norm_nonneg u) (heatKernel_nonneg (E := E) ht u))
  have hf_eq :
      fderiv ℝ (fun z : E => heatKernel (E := E) t z) u =
        heatKernelSpatialFDerivIntegrand (E := E) t u 0 1 := by
    rw [(hasFDerivAt_heatKernel_spatial (E := E) ht.ne' u).fderiv]
    ext v
    simp [heatKernelSpatialFDerivIntegrand, heatKernel]
    ring
  rw [hf_eq]
  refine ContinuousLinearMap.opNorm_le_bound _ hbound_nonneg ?_
  intro v
  set hk : ℝ := heatKernel (E := E) t u
  have hk_nonneg : 0 ≤ hk := by
    simpa [hk] using heatKernel_nonneg (E := E) ht u
  have hinv_nonneg : 0 ≤ 1 / (2 * t) := by positivity
  have hcoeff : ‖(1 : ℝ) * hk * (-(1 / (2 * t)))‖ = hk * (1 / (2 * t)) := by
    rw [one_mul, norm_mul, norm_neg, Real.norm_of_nonneg hk_nonneg,
      Real.norm_of_nonneg hinv_nonneg]
  have hinner : ‖innerSL ℝ u v‖ ≤ ‖u‖ * ‖v‖ := by
    simpa only [innerSL_apply_apply, Real.norm_eq_abs] using abs_real_inner_le_norm u v
  calc
    ‖heatKernelSpatialFDerivIntegrand (E := E) t u 0 1 v‖ =
        ‖(1 : ℝ) * hk * (-(1 / (2 * t)))‖ * ‖innerSL ℝ u v‖ := by
          simp [heatKernelSpatialFDerivIntegrand, hk]
    _ ≤ (hk * (1 / (2 * t))) * (‖u‖ * ‖v‖) := by
      exact mul_le_mul (le_of_eq hcoeff) hinner (norm_nonneg _) (by positivity)
    _ = ((1 / (2 * t)) * (‖u‖ * heatKernel (E := E) t u)) * ‖v‖ := by
      simp [hk]
      ring

omit [MeasurableSpace E] [BorelSpace E] in
/--
Uniform closed-ball envelope for the first spatial Fréchet derivative operator
norm.
-/
theorem fderiv_heatKernel_norm_le_uniformTranslateEnvelope {t R : ℝ} (ht : 0 < t)
    (hR : 0 ≤ R) {x₀ x y : E} (hx : x ∈ Metric.closedBall x₀ R) :
    ‖fderiv ℝ (fun z : E => heatKernel (E := E) t z) (x - y)‖ ≤
      heatKernelUniformTranslateEnvelope (E := E) t
        ((1 / (2 * t)) *
          heatKernelUniformTranslateConstant (E := E) t (‖x₀‖ + R)) y := by
  have hfd := fderiv_heatKernel_norm_le_order_one (E := E) ht (x - y)
  have hpoly := heatKernel_translate_order_one_le_uniformEnvelope (E := E) ht hR
    (x₀ := x₀) (x := x) (y := y) hx
  have hcoeff_nonneg : 0 ≤ 1 / (2 * t) := by positivity
  calc
    ‖fderiv ℝ (fun z : E => heatKernel (E := E) t z) (x - y)‖
        ≤ (1 / (2 * t)) * (‖x - y‖ * heatKernel (E := E) t (x - y)) := hfd
    _ ≤ (1 / (2 * t)) *
        heatKernelUniformTranslateEnvelope (E := E) t
          (heatKernelUniformTranslateConstant (E := E) t (‖x₀‖ + R)) y := by
          exact mul_le_mul_of_nonneg_left hpoly hcoeff_nonneg
    _ = heatKernelUniformTranslateEnvelope (E := E) t
        ((1 / (2 * t)) *
          heatKernelUniformTranslateConstant (E := E) t (‖x₀‖ + R)) y := by
          simp [heatKernelUniformTranslateEnvelope]
          ring

end Measurable

end Poincare
