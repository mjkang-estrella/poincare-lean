import Poincare.Global.DeTurckBUCGeneratorLaplacian

/-!
# Zero-time consistency of the classical heat Laplacian

The positive-time heat theory differentiates the Gaussian kernel.  To identify
the resulting Laplacian at time zero with the classical Laplacian of the
initial coefficient, one also needs a classical core on which derivatives may
instead be passed through the translated-data formula

`H_t f(x) = ∫ K_t(y) f(x - y) dy`.

This file supplies that core.  A globally `C²` scalar coefficient with bounded
first and second Frechet derivatives satisfies

`Delta (H_t f) = H_t (Delta f)`

at every positive time.  If `Delta f` is represented by a `BUC` coefficient,
strong continuity of the `BUC` heat semigroup then gives the desired
pointwise zero-time limit.  Applied to a coordinate of a tensor coefficient,
this discharges the remaining consistency premise in
`DeTurckBUCGeneratorLaplacian.lean` without introducing another generator
graph witness.
-/

noncomputable section

open MeasureTheory Filter Set Function
open scoped Topology InnerProductSpace Laplacian ContDiff
  BoundedContinuousFunction

namespace Poincare

section ScalarClassicalCore

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- First differentiation of the translated-data heat formula.  Boundedness
of the datum makes the original integral convergent, while boundedness of its
first derivative is the exact domination used for differentiation. -/
private theorem heatSolution_hasFDerivAt_of_bounded_fderiv
    {t C₀ C₁ : ℝ} (ht : 0 < t) {f : E → ℝ}
    (hf : ContDiff ℝ 2 f)
    (hC₀ : ∀ x, ‖f x‖ ≤ C₀)
    (hC₁ : ∀ x, ‖fderiv ℝ f x‖ ≤ C₁)
    (x : E) :
    HasFDerivAt (heatSolution (E := E) t f)
      (∫ y : E, heatKernel (E := E) t y • fderiv ℝ f (x - y)) x := by
  let s : Set E := Metric.closedBall x 1
  let bound : E → ℝ := fun y ↦ C₁ * heatKernel (E := E) t y
  have hC₁_nonneg : 0 ≤ C₁ := (norm_nonneg (fderiv ℝ f 0)).trans (hC₁ 0)
  have hs : s ∈ nhds x := Metric.closedBall_mem_nhds x (by norm_num)
  have hfd_cont : Continuous (fderiv ℝ f) :=
    (hf.fderiv_right (m := 0) (by norm_num)).continuous
  have hF_meas : ∀ᶠ z in nhds x,
      AEStronglyMeasurable
        (fun y : E ↦ heatKernel (E := E) t y * f (z - y)) volume := by
    refine Filter.Eventually.of_forall ?_
    intro z
    exact (contDiff_heatKernel_spatial (E := E) t).continuous.aestronglyMeasurable.mul
      (hf.continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  have hF_int : Integrable
      (fun y : E ↦ heatKernel (E := E) t y * f (x - y)) volume := by
    have hmeas : AEStronglyMeasurable
        (fun y : E ↦ heatKernel (E := E) t y * f (x - y)) volume :=
      (contDiff_heatKernel_spatial (E := E) t).continuous.aestronglyMeasurable.mul
        (hf.continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
    refine ((heatKernel_integrable (E := E) ht).const_mul C₀).mono' hmeas ?_
    refine Filter.Eventually.of_forall ?_
    intro y
    have hk := heatKernel_nonneg (E := E) ht y
    calc
      ‖heatKernel (E := E) t y * f (x - y)‖ =
          heatKernel (E := E) t y * ‖f (x - y)‖ := by
            rw [norm_mul, Real.norm_of_nonneg hk]
      _ ≤ heatKernel (E := E) t y * C₀ :=
        mul_le_mul_of_nonneg_left (hC₀ (x - y)) hk
      _ = C₀ * heatKernel (E := E) t y := by ring
  have hF'_meas : AEStronglyMeasurable
      (fun y : E ↦ heatKernel (E := E) t y • fderiv ℝ f (x - y)) volume :=
    (contDiff_heatKernel_spatial (E := E) t).continuous.aestronglyMeasurable.smul
      (hfd_cont.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  have hbound_int : Integrable bound volume := by
    simpa [bound] using (heatKernel_integrable (E := E) ht).const_mul C₁
  have h_bound : ∀ᵐ y ∂(volume : Measure E), ∀ z ∈ s,
      ‖heatKernel (E := E) t y • fderiv ℝ f (z - y)‖ ≤ bound y := by
    refine Filter.Eventually.of_forall ?_
    intro y z _hz
    have hk := heatKernel_nonneg (E := E) ht y
    calc
      ‖heatKernel (E := E) t y • fderiv ℝ f (z - y)‖ =
          heatKernel (E := E) t y * ‖fderiv ℝ f (z - y)‖ := by
            rw [norm_smul, Real.norm_of_nonneg hk]
      _ ≤ heatKernel (E := E) t y * C₁ :=
        mul_le_mul_of_nonneg_left (hC₁ (z - y)) hk
      _ = bound y := by simp [bound, mul_comm]
  have h_diff : ∀ᵐ y ∂(volume : Measure E), ∀ z ∈ s,
      HasFDerivAt
        (fun z : E ↦ heatKernel (E := E) t y * f (z - y))
        (heatKernel (E := E) t y • fderiv ℝ f (z - y)) z := by
    refine Filter.Eventually.of_forall ?_
    intro y z _hz
    have hbase : HasFDerivAt f (fderiv ℝ f (z - y)) (z - y) :=
      (hf.differentiable (by norm_num) (z - y)).hasFDerivAt
    have hsub : HasFDerivAt (fun q : E ↦ q - y)
        (ContinuousLinearMap.id ℝ E) z := by
      simpa only [id_eq] using (hasFDerivAt_id (x := z)).sub_const y
    simpa using (hbase.comp z hsub).const_mul (heatKernel (E := E) t y)
  have hraw := hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun z y ↦ heatKernel (E := E) t y * f (z - y))
    (F' := fun z y ↦ heatKernel (E := E) t y • fderiv ℝ f (z - y))
    (x₀ := x) (s := s) (bound := bound)
    hs hF_meas hF_int hF'_meas h_bound hbound_int h_diff
  convert hraw using 1

/-- The data Hessian times the heat kernel is integrable after scalarizing one
Hessian direction.  This avoids asking for a Bochner topology on the nested
continuous-linear-map space. -/
private theorem integrable_heatKernel_smul_fderiv_fderiv_flip
    {t C₀ C₁ C₂ : ℝ} (ht : 0 < t) {f : E → ℝ}
    (hf : ContDiff ℝ 2 f)
    (_hC₀ : ∀ x, ‖f x‖ ≤ C₀)
    (_hC₁ : ∀ x, ‖fderiv ℝ f x‖ ≤ C₁)
    (hC₂ : ∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ C₂)
    (x v : E) :
    Integrable (fun y : E ↦
      (heatKernel (E := E) t y •
        fderiv ℝ (fderiv ℝ f) (x - y)).flip v) volume := by
  let bound : E → ℝ := fun y ↦
    (C₂ * ‖v‖) * heatKernel (E := E) t y
  have hC₂_nonneg : 0 ≤ C₂ :=
    (norm_nonneg (fderiv ℝ (fderiv ℝ f) 0)).trans (hC₂ 0)
  have hfd : ContDiff ℝ 1 (fderiv ℝ f) :=
    hf.fderiv_right (m := 1) (by norm_num)
  have hfdd_cont : Continuous (fderiv ℝ (fderiv ℝ f)) :=
    (hfd.fderiv_right (m := 0) (by norm_num)).continuous
  have hflip : Continuous
      (fun H : E →L[ℝ] E →L[ℝ] ℝ ↦ H.flip v) := by
    have h₁ : Continuous
        (fun H : E →L[ℝ] E →L[ℝ] ℝ ↦ H.flip) :=
      (ContinuousLinearMap.flipₗᵢ ℝ E E ℝ).continuous
    exact ((ContinuousLinearMap.apply ℝ (E →L[ℝ] ℝ)) v).continuous.comp h₁
  have hmeas : AEStronglyMeasurable (fun y : E ↦
      (heatKernel (E := E) t y •
        fderiv ℝ (fderiv ℝ f) (x - y)).flip v) volume := by
    apply hflip.comp_aestronglyMeasurable
    exact (contDiff_heatKernel_spatial (E := E) t).continuous.aestronglyMeasurable.smul
      (hfdd_cont.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  have hbound_int : Integrable bound volume := by
    simpa [bound, mul_assoc] using
      (heatKernel_integrable (E := E) ht).const_mul (C₂ * ‖v‖)
  refine hbound_int.mono' hmeas ?_
  refine Filter.Eventually.of_forall ?_
  intro y
  have hk := heatKernel_nonneg (E := E) ht y
  have hsmul := norm_real_smul_continuousLinearMap_two_le
    (E := E) (heatKernel (E := E) t y)
      (fderiv ℝ (fderiv ℝ f) (x - y))
  calc
    ‖(heatKernel (E := E) t y •
        fderiv ℝ (fderiv ℝ f) (x - y)).flip v‖
        ≤ ‖(heatKernel (E := E) t y •
            fderiv ℝ (fderiv ℝ f) (x - y)).flip‖ * ‖v‖ :=
          ContinuousLinearMap.le_opNorm _ v
    _ = ‖heatKernel (E := E) t y •
          fderiv ℝ (fderiv ℝ f) (x - y)‖ * ‖v‖ := by
        rw [ContinuousLinearMap.opNorm_flip]
    _ ≤ (‖heatKernel (E := E) t y‖ *
          ‖fderiv ℝ (fderiv ℝ f) (x - y)‖) * ‖v‖ :=
        mul_le_mul_of_nonneg_right hsmul (norm_nonneg v)
    _ ≤ (heatKernel (E := E) t y * C₂) * ‖v‖ := by
        rw [Real.norm_of_nonneg hk]
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hC₂ (x - y)) hk) (norm_nonneg v)
    _ = bound y := by simp [bound]; ring

/-- Second differentiation of the translated-data heat formula after fixing
one first-derivative direction. -/
private theorem heatSolution_fderiv_apply_hasFDerivAt_of_bounded_second_fderiv
    {t C₀ C₁ C₂ : ℝ} (ht : 0 < t) {f : E → ℝ}
    (hf : ContDiff ℝ 2 f)
    (hC₀ : ∀ x, ‖f x‖ ≤ C₀)
    (hC₁ : ∀ x, ‖fderiv ℝ f x‖ ≤ C₁)
    (hC₂ : ∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ C₂)
    (x v : E) :
    HasFDerivAt
      (fun z : E ↦ fderiv ℝ (heatSolution (E := E) t f) z v)
      (∫ y : E, (heatKernel (E := E) t y •
        fderiv ℝ (fderiv ℝ f) (x - y)).flip v) x := by
  let s : Set E := Metric.closedBall x 1
  let bound : E → ℝ := fun y ↦
    (C₂ * ‖v‖) * heatKernel (E := E) t y
  have hC₁_nonneg : 0 ≤ C₁ := (norm_nonneg (fderiv ℝ f 0)).trans (hC₁ 0)
  have hC₂_nonneg : 0 ≤ C₂ :=
    (norm_nonneg (fderiv ℝ (fderiv ℝ f) 0)).trans (hC₂ 0)
  have hs : s ∈ nhds x := Metric.closedBall_mem_nhds x (by norm_num)
  have hfd : ContDiff ℝ 1 (fderiv ℝ f) :=
    hf.fderiv_right (m := 1) (by norm_num)
  have hfd_cont : Continuous (fderiv ℝ f) := hfd.continuous
  have hfdd_cont : Continuous (fderiv ℝ (fderiv ℝ f)) :=
    (hfd.fderiv_right (m := 0) (by norm_num)).continuous
  have hF_meas : ∀ᶠ z in nhds x,
      AEStronglyMeasurable
        (fun y : E ↦ heatKernel (E := E) t y *
          fderiv ℝ f (z - y) v) volume := by
    refine Filter.Eventually.of_forall ?_
    intro z
    have heval : Continuous (fun L : E →L[ℝ] ℝ ↦ L v) :=
      ((ContinuousLinearMap.apply ℝ ℝ) v).continuous
    exact (contDiff_heatKernel_spatial (E := E) t).continuous.aestronglyMeasurable.mul
      (heval.comp (hfd_cont.comp
        (continuous_const.sub continuous_id))).aestronglyMeasurable
  have hF_int : Integrable
      (fun y : E ↦ heatKernel (E := E) t y *
        fderiv ℝ f (x - y) v) volume := by
    have hmeas : AEStronglyMeasurable
        (fun y : E ↦ heatKernel (E := E) t y *
          fderiv ℝ f (x - y) v) volume := by
      have heval : Continuous (fun L : E →L[ℝ] ℝ ↦ L v) :=
        ((ContinuousLinearMap.apply ℝ ℝ) v).continuous
      exact (contDiff_heatKernel_spatial (E := E) t).continuous.aestronglyMeasurable.mul
        (heval.comp (hfd_cont.comp
          (continuous_const.sub continuous_id))).aestronglyMeasurable
    refine ((heatKernel_integrable (E := E) ht).const_mul (C₁ * ‖v‖)).mono' hmeas ?_
    refine Filter.Eventually.of_forall ?_
    intro y
    have hk := heatKernel_nonneg (E := E) ht y
    have happ := ContinuousLinearMap.le_opNorm (fderiv ℝ f (x - y)) v
    calc
      ‖heatKernel (E := E) t y * fderiv ℝ f (x - y) v‖ =
          heatKernel (E := E) t y * ‖fderiv ℝ f (x - y) v‖ := by
            rw [norm_mul, Real.norm_of_nonneg hk]
      _ ≤ heatKernel (E := E) t y *
          (‖fderiv ℝ f (x - y)‖ * ‖v‖) :=
        mul_le_mul_of_nonneg_left happ hk
      _ ≤ heatKernel (E := E) t y * (C₁ * ‖v‖) := by
        gcongr
        exact hC₁ (x - y)
      _ = (C₁ * ‖v‖) * heatKernel (E := E) t y := by ring
  have hF'_meas : AEStronglyMeasurable
      (fun y : E ↦ (heatKernel (E := E) t y •
        fderiv ℝ (fderiv ℝ f) (x - y)).flip v) volume := by
    have hflip : Continuous
        (fun H : E →L[ℝ] E →L[ℝ] ℝ ↦ H.flip v) := by
      have h₁ : Continuous
          (fun H : E →L[ℝ] E →L[ℝ] ℝ ↦ H.flip) :=
        (ContinuousLinearMap.flipₗᵢ ℝ E E ℝ).continuous
      exact ((ContinuousLinearMap.apply ℝ (E →L[ℝ] ℝ)) v).continuous.comp h₁
    apply hflip.comp_aestronglyMeasurable
    exact (contDiff_heatKernel_spatial (E := E) t).continuous.aestronglyMeasurable.smul
      (hfdd_cont.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  have hbound_int : Integrable bound volume := by
    simpa [bound, mul_assoc] using
      (heatKernel_integrable (E := E) ht).const_mul (C₂ * ‖v‖)
  have h_bound : ∀ᵐ y ∂(volume : Measure E), ∀ z ∈ s,
      ‖(heatKernel (E := E) t y •
        fderiv ℝ (fderiv ℝ f) (z - y)).flip v‖ ≤ bound y := by
    refine Filter.Eventually.of_forall ?_
    intro y z _hz
    have hk := heatKernel_nonneg (E := E) ht y
    have hsmul := norm_real_smul_continuousLinearMap_two_le
      (E := E) (heatKernel (E := E) t y)
        (fderiv ℝ (fderiv ℝ f) (z - y))
    calc
      ‖(heatKernel (E := E) t y •
          fderiv ℝ (fderiv ℝ f) (z - y)).flip v‖
          ≤ ‖(heatKernel (E := E) t y •
              fderiv ℝ (fderiv ℝ f) (z - y)).flip‖ * ‖v‖ :=
            ContinuousLinearMap.le_opNorm _ v
      _ = ‖heatKernel (E := E) t y •
            fderiv ℝ (fderiv ℝ f) (z - y)‖ * ‖v‖ := by
          rw [ContinuousLinearMap.opNorm_flip]
      _ ≤ (‖heatKernel (E := E) t y‖ *
            ‖fderiv ℝ (fderiv ℝ f) (z - y)‖) * ‖v‖ :=
          mul_le_mul_of_nonneg_right hsmul (norm_nonneg v)
      _ ≤ (heatKernel (E := E) t y * C₂) * ‖v‖ := by
          rw [Real.norm_of_nonneg hk]
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (hC₂ (z - y)) hk) (norm_nonneg v)
      _ = bound y := by simp [bound]; ring
  have h_diff : ∀ᵐ y ∂(volume : Measure E), ∀ z ∈ s,
      HasFDerivAt
        (fun z : E ↦ heatKernel (E := E) t y * fderiv ℝ f (z - y) v)
        ((heatKernel (E := E) t y •
          fderiv ℝ (fderiv ℝ f) (z - y)).flip v) z := by
    refine Filter.Eventually.of_forall ?_
    intro y z _hz
    have hbase : HasFDerivAt (fderiv ℝ f)
        (fderiv ℝ (fderiv ℝ f) (z - y)) (z - y) :=
      (hfd.differentiable (by norm_num) (z - y)).hasFDerivAt
    have heval : HasFDerivAt (fun q : E ↦ fderiv ℝ f q v)
        ((fderiv ℝ (fderiv ℝ f) (z - y)).flip v) (z - y) := by
      have h := hbase.clm_apply (hasFDerivAt_const v (z - y))
      simpa using h
    have hsub : HasFDerivAt (fun q : E ↦ q - y)
        (ContinuousLinearMap.id ℝ E) z := by
      simpa only [id_eq] using (hasFDerivAt_id (x := z)).sub_const y
    simpa using (heval.comp z hsub).const_mul (heatKernel (E := E) t y)
  have hraw := hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun z y ↦ heatKernel (E := E) t y * fderiv ℝ f (z - y) v)
    (F' := fun z y ↦ (heatKernel (E := E) t y •
      fderiv ℝ (fderiv ℝ f) (z - y)).flip v)
    (x₀ := x) (s := s) (bound := bound)
    hs hF_meas hF_int hF'_meas h_bound hbound_int h_diff
  have hfirst : (fun z : E ↦
      fderiv ℝ (heatSolution (E := E) t f) z v) =
      fun z : E ↦ ∫ y : E,
        heatKernel (E := E) t y * fderiv ℝ f (z - y) v := by
    funext z
    have hderiv := (heatSolution_hasFDerivAt_of_bounded_fderiv
      (E := E) ht hf hC₀ hC₁ z).fderiv
    have hint : Integrable (fun y : E ↦
        heatKernel (E := E) t y • fderiv ℝ f (z - y)) volume := by
      have hmeas : AEStronglyMeasurable (fun y : E ↦
          heatKernel (E := E) t y • fderiv ℝ f (z - y)) volume :=
        (contDiff_heatKernel_spatial (E := E) t).continuous.aestronglyMeasurable.smul
          (hfd_cont.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
      refine ((heatKernel_integrable (E := E) ht).const_mul C₁).mono' hmeas ?_
      refine Filter.Eventually.of_forall ?_
      intro y
      have hk := heatKernel_nonneg (E := E) ht y
      calc
        ‖heatKernel (E := E) t y • fderiv ℝ f (z - y)‖ =
            heatKernel (E := E) t y * ‖fderiv ℝ f (z - y)‖ := by
              rw [norm_smul, Real.norm_of_nonneg hk]
        _ ≤ heatKernel (E := E) t y * C₁ :=
          mul_le_mul_of_nonneg_left (hC₁ (z - y)) hk
        _ = C₁ * heatKernel (E := E) t y := by ring
    rw [hderiv, ContinuousLinearMap.integral_apply hint v]
    apply integral_congr_ae
    refine Filter.Eventually.of_forall ?_
    intro y
    simp
  rw [hfirst]
  exact hraw

/-- Diagonal Hessian components of the heat solution are heat averages of the
corresponding diagonal Hessian components of the classical datum. -/
private theorem iteratedFDeriv_two_heatSolution_apply_diagonal_of_bounded_derivatives
    {t C₀ C₁ C₂ : ℝ} (ht : 0 < t) {f : E → ℝ}
    (hf : ContDiff ℝ 2 f)
    (hC₀ : ∀ x, ‖f x‖ ≤ C₀)
    (hC₁ : ∀ x, ‖fderiv ℝ f x‖ ≤ C₁)
    (hC₂ : ∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ C₂)
    (x v : E) :
    iteratedFDeriv ℝ 2 (heatSolution (E := E) t f) x ![v, v] =
      ∫ y : E, heatKernel (E := E) t y *
        iteratedFDeriv ℝ 2 f (x - y) ![v, v] := by
  let U : E → ℝ := heatSolution (E := E) t f
  let H : E →L[ℝ] E →L[ℝ] ℝ := fderiv ℝ (fderiv ℝ U) x
  have hUtwo : ContDiff ℝ 2 U := by
    exact contDiff_two_heatSolution_of_bounded_measurable
      (E := E) ht hf.continuous.aestronglyMeasurable hC₀
  have hD : HasFDerivAt (fderiv ℝ U) H x := by
    have hDone : ContDiff ℝ 1 (fderiv ℝ U) :=
      hUtwo.fderiv_right (m := 1) (by norm_num)
    exact (hDone.differentiable (by norm_num) x).hasFDerivAt
  have hcalc : HasFDerivAt (fun z : E ↦ fderiv ℝ U z v) (H.flip v) x := by
    have h := hD.clm_apply (hasFDerivAt_const v x)
    simpa [H] using h
  have hgiven : HasFDerivAt (fun z : E ↦ fderiv ℝ U z v)
      (∫ y : E, (heatKernel (E := E) t y •
        fderiv ℝ (fderiv ℝ f) (x - y)).flip v) x := by
    simpa [U] using
      heatSolution_fderiv_apply_hasFDerivAt_of_bounded_second_fderiv
        (E := E) ht hf hC₀ hC₁ hC₂ x v
  have heq : H.flip v =
      ∫ y : E, (heatKernel (E := E) t y •
        fderiv ℝ (fderiv ℝ f) (x - y)).flip v :=
    hcalc.unique hgiven
  have hint := integrable_heatKernel_smul_fderiv_fderiv_flip
    (E := E) ht hf hC₀ hC₁ hC₂ x v
  rw [iteratedFDeriv_two_apply]
  change H v v = _
  calc
    H v v = H.flip v v := rfl
    _ = (∫ y : E, (heatKernel (E := E) t y •
          fderiv ℝ (fderiv ℝ f) (x - y)).flip v) v := by
      rw [heq]
    _ = ∫ y : E, (heatKernel (E := E) t y •
          fderiv ℝ (fderiv ℝ f) (x - y)).flip v v :=
      ContinuousLinearMap.integral_apply hint v
    _ = ∫ y : E, heatKernel (E := E) t y *
          iteratedFDeriv ℝ 2 f (x - y) ![v, v] := by
      apply integral_congr_ae
      refine Filter.Eventually.of_forall ?_
      intro y
      simp [iteratedFDeriv_two_apply]

/-- On the bounded classical `C²` core, the Laplacian commutes with
positive-time heat convolution. -/
theorem laplacian_heatSolution_eq_heatSolution_laplacian_of_bounded_derivatives
    {t C₀ C₁ C₂ : ℝ} (ht : 0 < t) {f : E → ℝ}
    (hf : ContDiff ℝ 2 f)
    (hC₀ : ∀ x, ‖f x‖ ≤ C₀)
    (hC₁ : ∀ x, ‖fderiv ℝ f x‖ ≤ C₁)
    (hC₂ : ∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ C₂)
    (x : E) :
    (Δ (heatSolution (E := E) t f)) x =
      heatSolution (E := E) t (fun y ↦ (Δ f) y) x := by
  let b := stdOrthonormalBasis ℝ E
  have hdiag (i : Fin (Module.finrank ℝ E)) :
      iteratedFDeriv ℝ 2 (heatSolution (E := E) t f) x ![b i, b i] =
        ∫ y : E, heatKernel (E := E) t y *
          iteratedFDeriv ℝ 2 f (x - y) ![b i, b i] :=
    iteratedFDeriv_two_heatSolution_apply_diagonal_of_bounded_derivatives
      (E := E) ht hf hC₀ hC₁ hC₂ x (b i)
  have hscalar_int (i : Fin (Module.finrank ℝ E)) :
      Integrable (fun y : E ↦ heatKernel (E := E) t y *
        iteratedFDeriv ℝ 2 f (x - y) ![b i, b i]) volume := by
    have hraw := (integrable_heatKernel_smul_fderiv_fderiv_flip
      (E := E) ht hf hC₀ hC₁ hC₂ x (b i)).apply_continuousLinearMap (b i)
    convert hraw using 1 with y
    simp [iteratedFDeriv_two_apply]
  have hlhs : (Δ (heatSolution (E := E) t f)) x =
      ∑ i, iteratedFDeriv ℝ 2 (heatSolution (E := E) t f) x ![b i, b i] := by
    simpa [b] using congrFun
      (InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis
        (f := heatSolution (E := E) t f)) x
  have hrhs : heatSolution (E := E) t (fun y : E ↦ (Δ f) y) x =
      ∫ y : E, heatKernel (E := E) t y * (Δ f) (x - y) :=
    heatSolution_apply (E := E) t (fun y : E ↦ (Δ f) y) x
  calc
    (Δ (heatSolution (E := E) t f)) x =
        ∑ i, iteratedFDeriv ℝ 2 (heatSolution (E := E) t f) x ![b i, b i] :=
      hlhs
    _ =
        ∑ i, ∫ y : E, heatKernel (E := E) t y *
          iteratedFDeriv ℝ 2 f (x - y) ![b i, b i] :=
      Finset.sum_congr rfl fun i _hi ↦ hdiag i
    _ = ∫ y : E, ∑ i, heatKernel (E := E) t y *
        iteratedFDeriv ℝ 2 f (x - y) ![b i, b i] := by
      symm
      exact integral_finsetSum Finset.univ fun i _hi ↦ hscalar_int i
    _ = ∫ y : E, heatKernel (E := E) t y * (Δ f) (x - y) := by
      apply integral_congr_ae
      refine Filter.Eventually.of_forall ?_
      intro y
      rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
      simp only [b]
      rw [Finset.mul_sum]
    _ = heatSolution (E := E) t (fun y : E ↦ (Δ f) y) x := hrhs.symm

end ScalarClassicalCore

section CoordinateClassicalCore

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- Classical positive-time commutation for one scalar coordinate of a
tensor-valued `BUC` coefficient.  The second coefficient represents only the
classical Laplacian; it is not required to lie in the generator graph. -/
theorem coordinateMetricLaplacianValue_heatSemigroup_eq_of_bounded_derivatives
    (u lapu : CoordinateBUCTensor E) (v w : E)
    (hf : ContDiff ℝ 2 (fun y : E ↦ coordinateMetricValue u y v w))
    {C₁ C₂ : ℝ}
    (hC₁ : ∀ y, ‖fderiv ℝ (fun x : E ↦
      coordinateMetricValue u x v w) y‖ ≤ C₁)
    (hC₂ : ∀ y, ‖fderiv ℝ (fderiv ℝ (fun x : E ↦
      coordinateMetricValue u x v w)) y‖ ≤ C₂)
    (hlapu : ∀ y, coordinateMetricValue lapu y v w =
      coordinateMetricLaplacianValue u y v w)
    {t : ℝ} (ht : 0 < t) (z : E) :
    coordinateMetricLaplacianValue
        (vectorHeatSemigroupBUCExtended
          (E := E) (F := CoordinateTwoTensor E) t u) z v w =
      coordinateMetricValue
        (vectorHeatSemigroupBUCExtended
          (E := E) (F := CoordinateTwoTensor E) t lapu) z v w := by
  let f : E → ℝ := fun y ↦ coordinateMetricValue u y v w
  let C₀ : ℝ := ‖u‖ * ‖v‖ * ‖w‖
  have hC₀ : ∀ y, ‖f y‖ ≤ C₀ := by
    intro y
    change |coordinateMetricValue u y v w| ≤ ‖u‖ * ‖v‖ * ‖w‖
    exact abs_coordinateMetricValue_le (E := E) u y v w
  have hcommute :=
    laplacian_heatSolution_eq_heatSolution_laplacian_of_bounded_derivatives
      (E := E) ht hf hC₀ hC₁ hC₂ z
  have huheat :
      (fun y : E ↦ coordinateMetricValue
        (vectorHeatSemigroupBUCExtended
          (E := E) (F := CoordinateTwoTensor E) t u) y v w) =
        heatSolution (E := E) t f := by
    funext y
    exact coordinateMetricValue_vectorHeatSemigroupBUCExtended_eq_heatSolution
      u ht y v w
  have hlapfun : (fun y : E ↦ (Δ f) y) =
      fun y : E ↦ coordinateMetricValue lapu y v w := by
    funext y
    exact (hlapu y).symm
  change (Δ fun y : E ↦ coordinateMetricValue
    (vectorHeatSemigroupBUCExtended
      (E := E) (F := CoordinateTwoTensor E) t u) y v w) z = _
  rw [huheat, hcommute, hlapfun]
  exact (coordinateMetricValue_vectorHeatSemigroupBUCExtended_eq_heatSolution
    lapu ht z v w).symm

/-- A `BUC` representative of the classical coordinate Laplacian, together
with bounded classical first and second derivatives of the initial
coordinate, gives the missing pointwise zero-time Laplacian consistency. -/
theorem tendsto_coordinateMetricLaplacianValue_heatSemigroup_zero_of_bounded_derivatives
    (u lapu : CoordinateBUCTensor E) (z v w : E)
    (hf : ContDiff ℝ 2 (fun y : E ↦ coordinateMetricValue u y v w))
    {C₁ C₂ : ℝ}
    (hC₁ : ∀ y, ‖fderiv ℝ (fun x : E ↦
      coordinateMetricValue u x v w) y‖ ≤ C₁)
    (hC₂ : ∀ y, ‖fderiv ℝ (fderiv ℝ (fun x : E ↦
      coordinateMetricValue u x v w)) y‖ ≤ C₂)
    (hlapu : ∀ y, coordinateMetricValue lapu y v w =
      coordinateMetricLaplacianValue u y v w) :
    Tendsto
      (fun t : ℝ ↦ coordinateMetricLaplacianValue
        (vectorHeatSemigroupBUCExtended
          (E := E) (F := CoordinateTwoTensor E) t u) z v w)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (coordinateMetricLaplacianValue u z v w)) := by
  let L := coordinateMetricEvaluationCLM z v w
  have htend : Tendsto
      (fun t : ℝ ↦ coordinateMetricValue
        (vectorHeatSemigroupBUCExtended
          (E := E) (F := CoordinateTwoTensor E) t lapu) z v w)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (coordinateMetricValue lapu z v w)) := by
    simpa [L] using
      L.continuous.continuousAt.tendsto.comp
        (tendsto_vectorHeatSemigroupBUCExtended_apply_zero
          (E := E) (F := CoordinateTwoTensor E) lapu)
  have heventually :
      (fun t : ℝ ↦ coordinateMetricLaplacianValue
        (vectorHeatSemigroupBUCExtended
          (E := E) (F := CoordinateTwoTensor E) t u) z v w) =ᶠ[
        nhdsWithin 0 (Set.Ioi 0)]
      (fun t : ℝ ↦ coordinateMetricValue
        (vectorHeatSemigroupBUCExtended
          (E := E) (F := CoordinateTwoTensor E) t lapu) z v w) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact coordinateMetricLaplacianValue_heatSemigroup_eq_of_bounded_derivatives
      u lapu v w hf hC₁ hC₂ hlapu (Set.mem_Ioi.mp ht) z
  have h := htend.congr' heventually.symm
  simpa [hlapu z] using h

/-- The preceding classical core closes the generator-identification theorem
without any second strong-generator graph witness. -/
theorem coordinateMetricValue_generator_eq_laplacian_of_bounded_derivatives
    (u Au lapu : CoordinateBUCTensor E)
    (hu : IsInBUCHeatGeneratorDomain
      (F := CoordinateTwoTensor E) u Au)
    (z v w : E)
    (hf : ContDiff ℝ 2 (fun y : E ↦ coordinateMetricValue u y v w))
    {C₁ C₂ : ℝ}
    (hC₁ : ∀ y, ‖fderiv ℝ (fun x : E ↦
      coordinateMetricValue u x v w) y‖ ≤ C₁)
    (hC₂ : ∀ y, ‖fderiv ℝ (fderiv ℝ (fun x : E ↦
      coordinateMetricValue u x v w)) y‖ ≤ C₂)
    (hlapu : ∀ y, coordinateMetricValue lapu y v w =
      coordinateMetricLaplacianValue u y v w) :
    coordinateMetricValue Au z v w =
      coordinateMetricLaplacianValue u z v w := by
  apply coordinateMetricValue_generator_eq_laplacian_of_tendsto
    u Au hu z v w
  exact tendsto_coordinateMetricLaplacianValue_heatSemigroup_zero_of_bounded_derivatives
    u lapu z v w hf hC₁ hC₂ hlapu

end CoordinateClassicalCore

end Poincare
