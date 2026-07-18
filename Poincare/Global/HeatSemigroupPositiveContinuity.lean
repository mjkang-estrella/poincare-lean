import Poincare.Global.HeatRegularizedPicard
import Poincare.Global.HeatCauchyFinal
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Positive-time continuity of the heat operator

The Gaussian kernels vary continuously in `L¹` on every positive-time
neighborhood.  This gives operator-norm continuity of the heat convolution on
bounded continuous, finite-dimensional vector-valued data and discharges the
positive-time continuity payload used by the Duhamel construction.
-/

noncomputable section

open MeasureTheory Filter Set Function
open scoped Topology InnerProductSpace BoundedContinuousFunction

namespace Poincare

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- The scalar heat kernel is continuous in `L¹` at every positive time. -/
theorem tendsto_integral_abs_heatKernel_sub_at_positive
    (t : {t : ℝ // 0 < t}) :
    Tendsto
      (fun p : {t : ℝ // 0 < t} ↦
        ∫ y : E, |heatKernel (E := E) p.1 y - heatKernel (E := E) t.1 y|)
      (𝓝 t) (𝓝 0) := by
  let R : ℝ := heatKernelTimeWindowGaussianRatio (E := E) t.1
  let bound : E → ℝ := fun y ↦ 2 * R * heatKernel (E := E) (2 * t.1) y
  have hwindow : ∀ᶠ p : {t : ℝ // 0 < t} in 𝓝 t,
      p.1 ∈ Set.Icc (t.1 / 2) (2 * t.1) := by
    have hnhds : Set.Ioo (t.1 / 2) (2 * t.1) ∈ 𝓝 t.1 := by
      apply Ioo_mem_nhds
      · linarith [t.property]
      · linarith [t.property]
    have hpull : ∀ᶠ p : {t : ℝ // 0 < t} in 𝓝 t,
        p.1 ∈ Set.Ioo (t.1 / 2) (2 * t.1) := continuousAt_subtype_val hnhds
    filter_upwards [hpull] with p hp
    exact ⟨hp.1.le, hp.2.le⟩
  have hR0 : 0 ≤ R := by
    unfold R heatKernelTimeWindowGaussianRatio
    have hlow : 0 ≤ 4 * Real.pi * (t.1 / 2) :=
      mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le)
        (div_nonneg t.property.le (by norm_num))
    have hhigh : 0 ≤ 4 * Real.pi * (2 * t.1) :=
      mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le)
        (mul_nonneg (by norm_num) t.property.le)
    exact div_nonneg (Real.rpow_nonneg hlow _) (Real.rpow_nonneg hhigh _)
  have hbound_int : Integrable bound volume := by
    exact (heatKernel_integrable (E := E) (mul_pos (by norm_num) t.property)).const_mul (2 * R)
  have hmeas : ∀ᶠ p : {t : ℝ // 0 < t} in 𝓝 t,
      AEStronglyMeasurable
        (fun y : E ↦ |heatKernel (E := E) p.1 y - heatKernel (E := E) t.1 y|)
        volume := by
    refine Filter.Eventually.of_forall ?_
    intro p
    exact (((contDiff_heatKernel_spatial (E := E) p.1).continuous.sub
      (contDiff_heatKernel_spatial (E := E) t.1).continuous).abs).aestronglyMeasurable
  have hdom : ∀ᶠ p : {t : ℝ // 0 < t} in 𝓝 t, ∀ᵐ y ∂(volume : Measure E),
      ‖|heatKernel (E := E) p.1 y - heatKernel (E := E) t.1 y|‖ ≤ bound y := by
    filter_upwards [hwindow] with p hp
    refine Filter.Eventually.of_forall ?_
    intro y
    have hp_le := heatKernel_time_window_gaussian_le (E := E) t.property hp y
    have htmem : t.1 ∈ Set.Icc (t.1 / 2) (2 * t.1) := by
      constructor <;> linarith [t.property]
    have ht_le := heatKernel_time_window_gaussian_le (E := E) t.property htmem y
    have hp0 := heatKernel_nonneg (E := E) p.property y
    have ht0 := heatKernel_nonneg (E := E) t.property y
    calc
      ‖|heatKernel (E := E) p.1 y - heatKernel (E := E) t.1 y|‖ =
          |heatKernel (E := E) p.1 y - heatKernel (E := E) t.1 y| :=
        Real.norm_of_nonneg (abs_nonneg _)
      _ ≤ heatKernel (E := E) p.1 y + heatKernel (E := E) t.1 y :=
        (abs_le.2 ⟨by linarith, by linarith⟩)
      _ ≤ R * heatKernel (E := E) (2 * t.1) y +
          R * heatKernel (E := E) (2 * t.1) y := add_le_add hp_le ht_le
      _ = bound y := by simp [bound]; ring
  have hpoint : ∀ᵐ y ∂(volume : Measure E),
      Tendsto
        (fun p : {t : ℝ // 0 < t} ↦
          |heatKernel (E := E) p.1 y - heatKernel (E := E) t.1 y|)
        (𝓝 t) (𝓝 0) := by
    refine Filter.Eventually.of_forall ?_
    intro y
    have hkcont : ContinuousAt (fun τ : ℝ ↦ heatKernel (E := E) τ y) t.1 :=
      (hasDerivAt_heatKernel_time (E := E) t.property y).continuousAt
    have hsub : Tendsto
        (fun p : {t : ℝ // 0 < t} ↦
          heatKernel (E := E) p.1 y - heatKernel (E := E) t.1 y)
        (𝓝 t) (𝓝 0) := by
      simpa using
        (hkcont.comp' continuousAt_subtype_val).sub_const
          (heatKernel (E := E) t.1 y)
    simpa using hsub.abs
  simpa using tendsto_integral_filter_of_dominated_convergence
    bound hmeas hdom hbound_int hpoint

/-- The difference of two positive-time heat operators is controlled by the
`L¹` distance between their scalar kernels. -/
theorem norm_vectorHeatSemigroupCLM_sub_le_integral_abs
    (s t : {t : ℝ // 0 < t}) :
    ‖vectorHeatSemigroupCLM (E := E) (F := F) s.property -
        vectorHeatSemigroupCLM (E := E) (F := F) t.property‖ ≤
      ∫ y : E, |heatKernel (E := E) s.1 y - heatKernel (E := E) t.1 y| := by
  let C : ℝ := ∫ y : E,
    |heatKernel (E := E) s.1 y - heatKernel (E := E) t.1 y|
  have hC0 : 0 ≤ C := integral_nonneg fun _ ↦ abs_nonneg _
  refine ContinuousLinearMap.opNorm_le_bound _ hC0 ?_
  intro f
  rw [BoundedContinuousFunction.norm_le (mul_nonneg hC0 (norm_nonneg f))]
  intro x
  change ‖vectorHeatSolution (E := E) s.1 f x -
      vectorHeatSolution (E := E) t.1 f x‖ ≤ C * ‖f‖
  rw [vectorHeatSolution, vectorHeatSolution]
  have hsint := integrable_heatKernel_smul_vectorData (E := E) s.property
    f.continuous.aestronglyMeasurable
    (fun y ↦ BoundedContinuousFunction.norm_coe_le_norm f y) x
  have htint := integrable_heatKernel_smul_vectorData (E := E) t.property
    f.continuous.aestronglyMeasurable
    (fun y ↦ BoundedContinuousFunction.norm_coe_le_norm f y) x
  rw [← integral_sub hsint htint]
  have hdiff_int : Integrable
      (fun y : E ↦ |heatKernel (E := E) s.1 (x - y) -
        heatKernel (E := E) t.1 (x - y)| * ‖f‖) volume := by
    have hsK := heatKernel_integrable_sub_left (E := E) s.property x
    have htK := heatKernel_integrable_sub_left (E := E) t.property x
    convert ((hsK.sub htK).abs).const_mul ‖f‖ using 1 with y
    simp [mul_comm]
  have hnorm := MeasureTheory.norm_integral_le_of_norm_le hdiff_int
    (Filter.Eventually.of_forall fun y ↦ by
      calc
        ‖heatKernel (E := E) s.1 (x - y) • f y -
            heatKernel (E := E) t.1 (x - y) • f y‖ =
            |heatKernel (E := E) s.1 (x - y) -
              heatKernel (E := E) t.1 (x - y)| * ‖f y‖ := by
          rw [← sub_smul, norm_smul, Real.norm_eq_abs]
        _ ≤ |heatKernel (E := E) s.1 (x - y) -
              heatKernel (E := E) t.1 (x - y)| * ‖f‖ :=
          mul_le_mul_of_nonneg_left
            (BoundedContinuousFunction.norm_coe_le_norm f y) (abs_nonneg _))
  calc
    ‖∫ y : E, heatKernel (E := E) s.1 (x - y) • f y -
        heatKernel (E := E) t.1 (x - y) • f y‖
        ≤ ∫ y : E, |heatKernel (E := E) s.1 (x - y) -
            heatKernel (E := E) t.1 (x - y)| * ‖f‖ := hnorm
    _ = C * ‖f‖ := by
      rw [show (fun y : E ↦ |heatKernel (E := E) s.1 (x - y) -
          heatKernel (E := E) t.1 (x - y)| * ‖f‖) =
          fun y : E ↦ ‖f‖ * |heatKernel (E := E) s.1 (x - y) -
            heatKernel (E := E) t.1 (x - y)| by
        funext y
        ring]
      rw [integral_const_mul]
      rw [integral_sub_left_eq_self
        (fun y : E ↦ |heatKernel (E := E) s.1 y -
          heatKernel (E := E) t.1 y|) volume x]
      simp [C, mul_comm]

/-- Positive-time heat convolution is continuous in operator norm. -/
theorem continuous_vectorHeatSemigroupCLM_positive :
    Continuous (fun p : {t : ℝ // 0 < t} ↦
      vectorHeatSemigroupCLM (E := E) (F := F) p.property) := by
  rw [continuous_iff_continuousAt]
  intro t
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  apply squeeze_zero (fun p ↦ norm_nonneg _)
    (fun p ↦ norm_vectorHeatSemigroupCLM_sub_le_integral_abs
      (E := E) (F := F) p t)
  exact tendsto_integral_abs_heatKernel_sub_at_positive (E := E) t

/-- The positive-time continuity payload used by the Duhamel boundary is
fully discharged. -/
theorem heatSemigroupStrongContinuityOnPositiveTimes :
    HeatSemigroupStrongContinuityOnPositiveTimes (E := E) (F := F) :=
  continuous_vectorHeatSemigroupCLM_positive (E := E) (F := F)

end Poincare
