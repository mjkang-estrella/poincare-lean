import Poincare.Global.BoundedUniformContinuousHeat

/-!
# Strong continuity of heat convolution on `BUC`

The first Gaussian moment controls the far part of a uniformly continuous
modulus.  This upgrades the Lipschitz zero-time estimate to every bounded
uniformly continuous datum, so `BUC(E,F)` is an honest strong-continuity space
for the heat semigroup.
-/

noncomputable section

open MeasureTheory Filter Set Function
open scoped Topology InnerProductSpace BoundedContinuousFunction

namespace Poincare

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- The norm-weighted positive-time heat kernel is integrable. -/
theorem integrable_norm_mul_heatKernel {t : ℝ} (ht : 0 < t) :
    Integrable (fun y : E ↦ ‖y‖ * heatKernel (E := E) t y) volume := by
  have henv := integrable_one_add_norm_sq_mul_heatKernel_sub_left
    (E := E) ht 0
  have hmeas : AEStronglyMeasurable
      (fun y : E ↦ ‖y‖ * heatKernel (E := E) t y) volume :=
    (continuous_norm.mul
      (contDiff_heatKernel_spatial (E := E) t).continuous).aestronglyMeasurable
  refine henv.mono' hmeas (Filter.Eventually.of_forall fun y ↦ ?_)
  have hk := heatKernel_nonneg (E := E) ht y
  have hkeven : heatKernel (E := E) t (-y) = heatKernel (E := E) t y := by
    simp [heatKernel]
  rw [zero_sub, hkeven]
  calc
    ‖‖y‖ * heatKernel (E := E) t y‖ = ‖y‖ * heatKernel (E := E) t y := by
      rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg y) hk)]
    _ ≤ (1 + ‖y‖ ^ 2) * heatKernel (E := E) t y := by
      gcongr
      nlinarith [sq_nonneg (‖y‖ - 1)]

/-- A single uniform-continuity modulus gives a heat approximation estimate;
the first moment pays for translations outside the modulus radius. -/
theorem norm_vectorHeatSemigroup_sub_le_of_modulus
    {t ε δ : ℝ} (ht : 0 < t) (hε : 0 ≤ ε) (hδ : 0 < δ)
    (f : E →ᵇ F)
    (hmod : ∀ x y : E, dist x y < δ → dist (f x) (f y) ≤ ε) :
    ‖vectorHeatSolutionBCF (E := E) ht f - f‖ ≤
      ε + (2 * ‖f‖ / δ) * heatKernelFirstMoment (E := E) t := by
  let C : ℝ := 2 * ‖f‖ / δ
  have hC : 0 ≤ C := div_nonneg (mul_nonneg (by norm_num) (norm_nonneg f)) hδ.le
  have hmoment := integrable_norm_mul_heatKernel (E := E) ht
  let bound : E → ℝ := fun y ↦
    ε * heatKernel (E := E) t y + C * (‖y‖ * heatKernel (E := E) t y)
  have hbound : Integrable bound volume :=
    ((heatKernel_integrable (E := E) ht).const_mul ε).add
      (hmoment.const_mul C)
  apply (BoundedContinuousFunction.norm_le
    (f := vectorHeatSolutionBCF (E := E) ht f - f)
    (add_nonneg hε (mul_nonneg hC (integral_nonneg fun y ↦
      mul_nonneg (norm_nonneg y) (heatKernel_nonneg (E := E) ht y))))).mpr
  intro x
  rw [BoundedContinuousFunction.sub_apply, vectorHeatSolutionBCF_apply,
    vectorHeatSolution_apply_data_translate]
  have hmass := integral_heatKernel_eq_one (E := E) ht
  have hfconst : Integrable (fun y : E ↦ heatKernel (E := E) t y • f x) :=
    (heatKernel_integrable (E := E) ht).smul_const (f x)
  have hfx : f x = ∫ y : E, heatKernel (E := E) t y • f x := by
    rw [integral_smul_const, hmass, one_smul]
  rw [hfx]
  have hmain := integrable_heatKernel_smul_bcf_translate (E := E) ht f x
  rw [← integral_sub hmain hfconst]
  have hnorm := MeasureTheory.norm_integral_le_of_norm_le hbound
    (Filter.Eventually.of_forall fun y ↦ by
      have hk := heatKernel_nonneg (E := E) ht y
      have htranslate : ‖f (x - y) - f x‖ ≤ ε + C * ‖y‖ := by
        by_cases hy : ‖y‖ < δ
        · have hm : ‖f (x - y) - f x‖ ≤ ε := by
            rw [← dist_eq_norm]
            apply hmod
            simpa [dist_eq_norm] using hy
          exact hm.trans (le_add_of_nonneg_right (mul_nonneg hC (norm_nonneg y)))
        · have hglobal : ‖f (x - y) - f x‖ ≤ 2 * ‖f‖ := by
            calc
              ‖f (x - y) - f x‖ ≤ ‖f (x - y)‖ + ‖f x‖ := norm_sub_le _ _
              _ ≤ ‖f‖ + ‖f‖ := add_le_add
                (BoundedContinuousFunction.norm_coe_le_norm f _)
                (BoundedContinuousFunction.norm_coe_le_norm f _)
              _ = 2 * ‖f‖ := by ring
          have hfar : 2 * ‖f‖ ≤ C * ‖y‖ := by
            have hyδ : δ ≤ ‖y‖ := le_of_not_gt hy
            calc
              2 * ‖f‖ = C * δ := by
                dsimp [C]
                exact (div_mul_cancel₀ (2 * ‖f‖) hδ.ne').symm
              _ ≤ C * ‖y‖ := mul_le_mul_of_nonneg_left hyδ hC
          exact hglobal.trans (hfar.trans (le_add_of_nonneg_left hε))
      calc
        ‖heatKernel (E := E) t y • f (x - y) -
            heatKernel (E := E) t y • f x‖ =
            heatKernel (E := E) t y * ‖f (x - y) - f x‖ := by
          rw [← smul_sub, norm_smul, Real.norm_of_nonneg hk]
        _ ≤ heatKernel (E := E) t y * (ε + C * ‖y‖) :=
          mul_le_mul_of_nonneg_left htranslate hk
        _ = bound y := by simp [bound]; ring)
  calc
    ‖∫ y : E, heatKernel (E := E) t y • f (x - y) -
        heatKernel (E := E) t y • f x‖ ≤ ∫ y : E, bound y := hnorm
    _ = ε + C * heatKernelFirstMoment (E := E) t := by
      rw [integral_add ((heatKernel_integrable (E := E) ht).const_mul ε)
        (hmoment.const_mul C)]
      simp [heatKernelFirstMoment, integral_const_mul, hmass]
    _ = ε + (2 * ‖f‖ / δ) * heatKernelFirstMoment (E := E) t := rfl

/-- Every bounded uniformly continuous datum converges uniformly to its
initial value as positive heat time tends to zero. -/
theorem tendsto_norm_vectorHeatSemigroup_sub_of_uniformContinuous
    (f : E →ᵇ F) (hf : UniformContinuous (f : E → F)) :
    Tendsto
      (fun t : ℝ ↦ if ht : 0 < t then
        ‖vectorHeatSemigroupCLM (E := E) (F := F) ht f - f‖ else 0)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro η hη
  rcases Metric.uniformContinuous_iff.mp hf (η / 4) (by positivity) with
    ⟨δ, hδ, hmod⟩
  let C : ℝ := 2 * ‖f‖ / δ
  have hC : 0 ≤ C := div_nonneg (mul_nonneg (by norm_num) (norm_nonneg f)) hδ.le
  have hmoment := heatKernelFirstMoment_tendsto_zero (E := E)
  rw [HeatKernelFirstMomentTendsToZero, Metric.tendsto_nhdsWithin_nhds] at hmoment
  let ζ : ℝ := η / (4 * (C + 1))
  have hζ : 0 < ζ := div_pos hη (by positivity)
  rcases hmoment ζ hζ with ⟨r, hr, hclose⟩
  refine ⟨r, hr, ?_⟩
  intro t htI htclose
  have ht : 0 < t := Set.mem_Ioi.mp htI
  rw [dif_pos ht, Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)]
  have hfirst : heatKernelFirstMoment (E := E) t < ζ := by
    have := hclose htI htclose
    have hm0 : 0 ≤ heatKernelFirstMoment (E := E) t :=
      integral_nonneg fun y ↦ mul_nonneg (norm_nonneg y)
        (heatKernel_nonneg (E := E) ht y)
    simpa [Real.dist_eq, abs_of_nonneg hm0] using this
  have hbound := norm_vectorHeatSemigroup_sub_le_of_modulus
    (E := E) (F := F) ht (show 0 ≤ η / 4 by positivity) hδ f
    (fun x y hxy ↦ (hmod hxy).le)
  calc
    ‖vectorHeatSemigroupCLM (E := E) (F := F) ht f - f‖
        ≤ η / 4 + C * heatKernelFirstMoment (E := E) t := hbound
    _ ≤ η / 4 + C * ζ :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hfirst.le hC)
    _ < η := by
      have hC1 : 0 < C + 1 := by linarith
      have hCζ : C * ζ < η / 4 := by
        calc
          C * ζ < (C + 1) * ζ :=
            mul_lt_mul_of_pos_right (lt_add_one C) hζ
          _ = η / 4 := by
            dsimp [ζ]
            field_simp [hC1.ne']
      linarith

/-- The zero-time strong-continuity frontier is discharged for nonlinearities
whose values are bounded uniformly continuous. -/
theorem heatSemigroupStrongContinuityAtZeroOn_of_uniformContinuous
    (N : (E →ᵇ F) → (E →ᵇ F))
    (hN : ∀ z : E →ᵇ F, UniformContinuous (N z : E → F)) :
    HeatSemigroupStrongContinuityAtZeroOn (E := E) (F := F) N := by
  intro z η hη
  have htend := tendsto_norm_vectorHeatSemigroup_sub_of_uniformContinuous
    (E := E) (F := F) (N z) (hN z)
  rw [Metric.tendsto_nhdsWithin_nhds] at htend
  rcases htend η hη with ⟨δ, hδ, hclose⟩
  refine ⟨δ, hδ, ?_⟩
  intro t ht htδ
  have h := hclose (Set.mem_Ioi.mpr ht) (by
    simpa [Real.dist_eq, abs_of_pos ht] using htδ)
  simpa [dif_pos ht, Real.dist_eq] using h

end Poincare
