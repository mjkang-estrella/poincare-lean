import Poincare.Global.HeatKernelIntegral
import Poincare.Global.HeatSemigroupOperator

/-!
# Gaussian heat-kernel semigroup law

The product of two positive-time heat kernels is completed to a square.  Its
integral is therefore a translated unit-mass heat kernel, giving the scalar
convolution law with the exact normalization used by this repository.
-/

noncomputable section

open MeasureTheory
open scoped Topology InnerProductSpace BoundedContinuousFunction

namespace Poincare

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Completing the square for the two heat-kernel quadratic exponents. -/
private theorem heatKernel_completeSquare
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (x y : E) :
    -(‖x - y‖ ^ 2) / (4 * s) + -(‖y‖ ^ 2) / (4 * t) =
      -(‖x‖ ^ 2) / (4 * (s + t)) +
        -(‖y - (t / (s + t)) • x‖ ^ 2) /
          (4 * (s * t / (s + t))) := by
  have hst : s + t ≠ 0 := ne_of_gt (add_pos hs ht)
  rw [norm_sub_sq_real, norm_sub_sq_real, norm_smul, Real.norm_of_nonneg
    (div_nonneg ht.le (add_pos hs ht).le), inner_smul_right]
  rw [real_inner_comm y x]
  field_simp [hs.ne', ht.ne', hst]
  ring

/-- The heat-kernel normalizing constants multiply according to the harmonic
time `s*t/(s+t)` produced by completing the square. -/
private theorem heatKernel_normalization_mul
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    (4 * Real.pi * s) ^ (-(Module.finrank ℝ E : ℝ) / 2) *
        (4 * Real.pi * t) ^ (-(Module.finrank ℝ E : ℝ) / 2) =
      (4 * Real.pi * (s + t)) ^ (-(Module.finrank ℝ E : ℝ) / 2) *
        (4 * Real.pi * (s * t / (s + t))) ^
          (-(Module.finrank ℝ E : ℝ) / 2) := by
  have hsbase : 0 ≤ 4 * Real.pi * s := (mul_pos (mul_pos (by norm_num) Real.pi_pos) hs).le
  have htbase : 0 ≤ 4 * Real.pi * t := (mul_pos (mul_pos (by norm_num) Real.pi_pos) ht).le
  have haddbase : 0 ≤ 4 * Real.pi * (s + t) :=
    (mul_pos (mul_pos (by norm_num) Real.pi_pos) (add_pos hs ht)).le
  have hrbase : 0 ≤ 4 * Real.pi * (s * t / (s + t)) :=
    (mul_pos (mul_pos (by norm_num) Real.pi_pos)
      (div_pos (mul_pos hs ht) (add_pos hs ht))).le
  rw [← Real.mul_rpow hsbase htbase, ← Real.mul_rpow haddbase hrbase]
  congr 1
  field_simp [ne_of_gt (add_pos hs ht)]

/-- Pointwise product decomposition behind the heat-kernel semigroup law. -/
theorem heatKernel_mul_eq_completeSquare
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (x y : E) :
    heatKernel (E := E) s (x - y) * heatKernel (E := E) t y =
      heatKernel (E := E) (s + t) x *
        heatKernel (E := E) (s * t / (s + t))
          (y - (t / (s + t)) • x) := by
  unfold heatKernel
  rw [mul_mul_mul_comm]
  rw [heatKernel_normalization_mul (E := E) hs ht]
  rw [← Real.exp_add]
  rw [heatKernel_completeSquare hs ht]
  rw [Real.exp_add]
  ring

/-- Scalar Gaussian heat kernels form a convolution semigroup at positive
times. -/
theorem integral_heatKernel_mul_heatKernel_eq
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (x : E) :
    (∫ y : E,
      heatKernel (E := E) s (x - y) * heatKernel (E := E) t y) =
      heatKernel (E := E) (s + t) x := by
  let r : ℝ := s * t / (s + t)
  have hr : 0 < r := div_pos (mul_pos hs ht) (add_pos hs ht)
  have hfun :
      (fun y : E =>
        heatKernel (E := E) s (x - y) * heatKernel (E := E) t y) =
      fun y : E =>
        heatKernel (E := E) (s + t) x *
          heatKernel (E := E) r (y - (t / (s + t)) • x) := by
    funext y
    simpa [r] using heatKernel_mul_eq_completeSquare (E := E) hs ht x y
  rw [hfun, integral_const_mul]
  have hmass :
      (∫ y : E,
        heatKernel (E := E) r (y - (t / (s + t)) • x)) = 1 := by
    rw [integral_sub_right_eq_self]
    exact integral_heatKernel_eq_one (E := E) hr
  rw [hmass, mul_one]

/-- The product of the two translated positive-time kernels is integrable. -/
theorem integrable_heatKernel_mul_heatKernel
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (x : E) :
    Integrable (fun y : E =>
      heatKernel (E := E) s (x - y) * heatKernel (E := E) t y) := by
  let r : ℝ := s * t / (s + t)
  let c : E := (t / (s + t)) • x
  have hr : 0 < r := div_pos (mul_pos hs ht) (add_pos hs ht)
  have htranslated :
      Integrable (fun y : E => heatKernel (E := E) r (y - c)) :=
    (heatKernel_integrable (E := E) hr).comp_sub_right c
  have hrhs :
      Integrable (fun y : E =>
        heatKernel (E := E) (s + t) x * heatKernel (E := E) r (y - c)) :=
    htranslated.const_mul (heatKernel (E := E) (s + t) x)
  apply hrhs.congr
  exact Filter.Eventually.of_forall fun y => by
    simpa [r, c] using
      (heatKernel_mul_eq_completeSquare (E := E) hs ht x y).symm

section Vector

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]

/-- Positive-time vector heat convolution composes by addition of times on
bounded continuous fields. -/
theorem vectorHeatSolution_add_time
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (f : E →ᵇ F) (x : E) :
    vectorHeatSolution (E := E) s
        (vectorHeatSolution (E := E) t f) x =
      vectorHeatSolution (E := E) (s + t) f x := by
  let H : E × E → F := fun p =>
    heatKernel (E := E) s (x - p.1) •
      (heatKernel (E := E) t (p.1 - p.2) • f p.2)
  have hst : 0 < s + t := add_pos hs ht
  have hHcont : Continuous H := by
    apply Continuous.smul
    · exact (contDiff_heatKernel_spatial (E := E) s).continuous.comp
        (continuous_const.sub continuous_fst)
    · apply Continuous.smul
      · exact (contDiff_heatKernel_spatial (E := E) t).continuous.comp
          (continuous_fst.sub continuous_snd)
      · exact f.continuous.comp continuous_snd
  have hinner_integrable :
      ∀ z : E, Integrable (fun y : E => H (y, z)) := by
    intro z
    have hscalar := integrable_heatKernel_mul_heatKernel (E := E) hs ht (x - z)
    have hshift := hscalar.comp_sub_right z
    have hsmul := hshift.smul_const (f z)
    simpa [H, sub_sub_sub_cancel_right, smul_smul] using hsmul
  have hconv_shift : ∀ z : E,
      (∫ y : E,
        heatKernel (E := E) s (x - y) *
          heatKernel (E := E) t (y - z)) =
        heatKernel (E := E) (s + t) (x - z) := by
    intro z
    let q : E → ℝ := fun u =>
      heatKernel (E := E) s ((x - z) - u) * heatKernel (E := E) t u
    calc
      (∫ y : E,
          heatKernel (E := E) s (x - y) *
            heatKernel (E := E) t (y - z)) =
          ∫ y : E, q (y - z) := by
            apply integral_congr_ae
            exact Filter.Eventually.of_forall fun y => by
              dsimp [q]
              congr 2
              abel
      _ = ∫ u : E, q u := integral_sub_right_eq_self q z
      _ = heatKernel (E := E) (s + t) (x - z) := by
        exact integral_heatKernel_mul_heatKernel_eq (E := E) hs ht (x - z)
  have hnorm_integral : ∀ z : E,
      (∫ y : E, ‖H (y, z)‖) =
        ‖f z‖ * heatKernel (E := E) (s + t) (x - z) := by
    intro z
    have hsnonneg : ∀ y : E, 0 ≤ heatKernel (E := E) s (x - y) :=
      fun y => heatKernel_nonneg (E := E) hs (x - y)
    have htnonneg : ∀ y : E, 0 ≤ heatKernel (E := E) t (y - z) :=
      fun y => heatKernel_nonneg (E := E) ht (y - z)
    calc
      (∫ y : E, ‖H (y, z)‖) =
          ∫ y : E,
            (heatKernel (E := E) s (x - y) *
              heatKernel (E := E) t (y - z)) * ‖f z‖ := by
            apply integral_congr_ae
            exact Filter.Eventually.of_forall fun y => by
              simp [H, norm_smul, Real.norm_of_nonneg (hsnonneg y),
                Real.norm_of_nonneg (htnonneg y), mul_assoc]
      _ =
          (∫ y : E,
            heatKernel (E := E) s (x - y) *
              heatKernel (E := E) t (y - z)) * ‖f z‖ := by
            rw [integral_mul_const]
      _ = heatKernel (E := E) (s + t) (x - z) * ‖f z‖ := by
            rw [hconv_shift z]
      _ = ‖f z‖ * heatKernel (E := E) (s + t) (x - z) := mul_comm _ _
  have hout : Integrable
      (fun z : E => ‖f z‖ * heatKernel (E := E) (s + t) (x - z)) := by
    have h := integrable_heatKernel_smul_vectorData
      (E := E) (F := ℝ) (C := ‖f‖) hst
      f.continuous.norm.aestronglyMeasurable
      (fun z => by
        simpa using BoundedContinuousFunction.norm_coe_le_norm f z) x
    simpa [smul_eq_mul, mul_comm] using h
  have hHintegrable : Integrable H (volume.prod volume) := by
    apply (integrable_prod_iff' hHcont.aestronglyMeasurable).2
    constructor
    · exact Filter.Eventually.of_forall hinner_integrable
    · simpa only [hnorm_integral] using hout
  have hinner_value : ∀ z : E,
      (∫ y : E, H (y, z)) =
        heatKernel (E := E) (s + t) (x - z) • f z := by
    intro z
    calc
      (∫ y : E, H (y, z)) =
          (∫ y : E,
            heatKernel (E := E) s (x - y) *
              heatKernel (E := E) t (y - z)) • f z := by
            rw [← integral_smul_const]
            apply integral_congr_ae
            exact Filter.Eventually.of_forall fun y => by
              simp [H, smul_smul]
      _ = heatKernel (E := E) (s + t) (x - z) • f z := by
            rw [hconv_shift z]
  calc
    vectorHeatSolution (E := E) s
          (vectorHeatSolution (E := E) t f) x =
        ∫ y : E, ∫ z : E, H (y, z) := by
          rw [vectorHeatSolution]
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun y => by
            change
              heatKernel (E := E) s (x - y) •
                  (∫ z : E,
                    heatKernel (E := E) t (y - z) • f z) =
                ∫ z : E, H (y, z)
            rw [← integral_smul]
    _ = ∫ z : E, ∫ y : E, H (y, z) := integral_integral_swap hHintegrable
    _ = ∫ z : E,
        heatKernel (E := E) (s + t) (x - z) • f z := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall hinner_value
    _ = vectorHeatSolution (E := E) (s + t) f x := rfl

/-- The bounded continuous vector heat operators form a positive-time
semigroup. -/
theorem vectorHeatSemigroupCLM_comp
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    (vectorHeatSemigroupCLM (E := E) (F := F) hs).comp
        (vectorHeatSemigroupCLM (E := E) (F := F) ht) =
      vectorHeatSemigroupCLM (E := E) (F := F) (add_pos hs ht) := by
  ext f x
  exact vectorHeatSolution_add_time (E := E) hs ht f x

end Vector

end Poincare
