import Poincare.Global.HeatDuhamelHessianTimeHolder
import Poincare.Global.HeatDuhamelHessianSpatialHolder
import Poincare.Global.ParabolicHolderSpace

set_option autoImplicit false

noncomputable section

open Set MeasureTheory
open scoped Interval

namespace Poincare.DuhamelParabolicHolderSeminorm

local notation "E" => Poincare.ClosedSmoothModel 3

/-- Spatial and temporal Hessian estimates give the parabolic Hölder bound. -/
theorem duhamel_hessian_parabolic_holder :
  ∀ α : ℝ, 0 < α → α < 1 →
  ∃ C : ℝ, 0 < C ∧ ∀ (T : ℝ), 0 < T → T ≤ 1 →
  ∀ (f : ℝ × E → ℝ) (M K : ℝ), 0 ≤ M → 0 ≤ K →
  ContinuousOn f (Icc 0 T ×ˢ univ) →
  (∀ t ∈ Icc 0 T, ∀ x : E, |f (t,x)| ≤ M) →
  (∀ t ∈ Icc 0 T, ∀ x y : E, |f (t,x) - f (t,y)| ≤ K * ‖x-y‖ ^ α) →
  let u : ℝ → E → ℝ := fun t x =>
    ∫ s in (0 : ℝ)..t, Poincare.heatSolution (t-s) (fun y => f (s,y)) x
  ∀ p ∈ ParabolicHolder.cylinder («E» := E) T, ∀ q ∈ ParabolicHolder.cylinder («E» := E) T,
    ‖fderiv ℝ (fderiv ℝ (u p.1)) p.2 - fderiv ℝ (fderiv ℝ (u q.1)) q.2‖
      ≤ C * K * ParabolicHolder.parabolicDist p q ^ α := by
  intro α hα hα1
  obtain ⟨C₁, hC₁, hspace⟩ :=
    HeatDuhamelHessianSpatialHolder.duhamel_hessian_spatial_holder α hα hα1
  obtain ⟨C₂, hC₂, htime⟩ :=
    HeatDuhamelHessianTimeHolder.duhamel_hessian_time_holder α hα hα1
  refine ⟨C₁ + C₂, add_pos hC₁ hC₂, ?_⟩
  intro T hT hT1 f M K hM hK hf hfM hfK
  dsimp only
  intro p hp q hq
  let u : ℝ → E → ℝ := fun t x =>
    ∫ s in (0 : ℝ)..t, Poincare.heatSolution (t-s) (fun y => f (s,y)) x
  have hs := hspace T hT hT1 f M K hM hK hf hfM hfK p.1 hp.1 p.2 q.2
  have ht := htime T hT hT1 f M K hM hK hf hfM hfK p.1 hp.1 q.1 hq.1 q.2
  have hspow : ‖p.2 - q.2‖ ^ α ≤ ParabolicHolder.parabolicDist p q ^ α :=
    Real.rpow_le_rpow (norm_nonneg _)
      (le_add_of_nonneg_right (Real.sqrt_nonneg _)) hα.le
  have htpow : |p.1 - q.1| ^ (α / 2) ≤ ParabolicHolder.parabolicDist p q ^ α := by
    calc
      |p.1 - q.1| ^ (α / 2) = (Real.sqrt |p.1 - q.1|) ^ α := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (abs_nonneg _)]
        congr 1
        ring
      _ ≤ ParabolicHolder.parabolicDist p q ^ α :=
        Real.rpow_le_rpow (Real.sqrt_nonneg _)
          (le_add_of_nonneg_left (norm_nonneg _)) hα.le
  calc
    ‖fderiv ℝ (fderiv ℝ (u p.1)) p.2 - fderiv ℝ (fderiv ℝ (u q.1)) q.2‖ ≤
        ‖fderiv ℝ (fderiv ℝ (u p.1)) p.2 - fderiv ℝ (fderiv ℝ (u p.1)) q.2‖ +
        ‖fderiv ℝ (fderiv ℝ (u p.1)) q.2 - fderiv ℝ (fderiv ℝ (u q.1)) q.2‖ := by
      simpa only [sub_add_sub_cancel] using norm_add_le
        (fderiv ℝ (fderiv ℝ (u p.1)) p.2 - fderiv ℝ (fderiv ℝ (u p.1)) q.2)
        (fderiv ℝ (fderiv ℝ (u p.1)) q.2 - fderiv ℝ (fderiv ℝ (u q.1)) q.2)
    _ ≤ C₁ * K * ‖p.2 - q.2‖ ^ α + C₂ * K * |p.1 - q.1| ^ (α / 2) :=
      add_le_add hs ht
    _ ≤ C₁ * K * ParabolicHolder.parabolicDist p q ^ α +
        C₂ * K * ParabolicHolder.parabolicDist p q ^ α :=
      add_le_add (mul_le_mul_of_nonneg_left hspow (mul_nonneg hC₁.le hK))
        (mul_le_mul_of_nonneg_left htpow (mul_nonneg hC₂.le hK))
    _ = (C₁ + C₂) * K * ParabolicHolder.parabolicDist p q ^ α := by ring

end Poincare.DuhamelParabolicHolderSeminorm
