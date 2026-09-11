import Poincare.Global.HeatDuhamelHeatEquation
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped Topology Interval

namespace Poincare.MovingLimitLeibniz

/-- Integrable bounds on secants permit differentiation within an arbitrary real set. -/
theorem hasDerivWithinAt_integral_of_dominated_secants
    {G : ℝ → ℝ → ℝ} {D B : ℝ → ℝ} {μ : Measure ℝ} {S : Set ℝ} {t : ℝ}
    (hG : ∀ᶠ r in 𝓝[S] t, Integrable (G r) μ)
    (hGt : Integrable (G t) μ) (hB : Integrable B μ)
    (hbound : ∀ᶠ r in 𝓝[S] t, ∀ᵐ s ∂μ,
      ‖G r s - G t s‖ ≤ B s * ‖r - t‖)
    (hD : ∀ᵐ s ∂μ, HasDerivWithinAt (fun r => G r s) (D s) S t) :
    HasDerivWithinAt (fun r => ∫ s, G r s ∂μ) (∫ s, D s ∂μ) S t := by
  rw [hasDerivWithinAt_iff_tendsto_slope]
  have hle : 𝓝[S \ {t}] t ≤ 𝓝[S] t := nhdsWithin_mono _ diff_subset
  have hi := tendsto_integral_filter_of_dominated_convergence B
    (by
      filter_upwards [hG.filter_mono hle] with r hr
      exact (hr.aestronglyMeasurable.sub hGt.aestronglyMeasurable).const_mul (r-t)⁻¹)
    (by
      filter_upwards [hbound.filter_mono hle, self_mem_nhdsWithin] with r hr hrt
      have hn : r - t ≠ 0 := sub_ne_zero.mpr (by simpa using hrt.2)
      filter_upwards [hr] with s hs
      rw [norm_mul, norm_inv]
      calc
        ‖r - t‖⁻¹ * ‖G r s - G t s‖ ≤ ‖r - t‖⁻¹ * (B s * ‖r - t‖) :=
          mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr (norm_nonneg _))
        _ = B s := by rw [mul_left_comm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hn), mul_one])
    hB (by
      filter_upwards [hD] with s hs
      simpa only [slope, smul_eq_mul] using
        (hasDerivWithinAt_iff_tendsto_slope.mp hs))
  apply hi.congr'
  filter_upwards [hG.filter_mono hle] with r hr
  simp only [slope, smul_eq_mul, Pi.sub_apply, vsub_eq_sub,
    integral_const_mul, integral_sub hr hGt]

end Poincare.MovingLimitLeibniz
