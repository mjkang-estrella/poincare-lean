import Poincare.Global.LinearizedFamilyExport

/-!
# Rescaling the hosted linearized family

This module turns the hosted Picard-Lindelöf closed-ball family into a
linearized solution family for every endpoint direction by normalizing each
direction into the PL ball and scaling the corresponding linear solution back.
-/

noncomputable section

open Bundle Metric Set
open scoped Manifold ContDiff Topology RealInnerProductSpace NNReal

namespace Poincare
namespace LinearizedRescale

universe u

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M]
variable [ChartedSpace E M]
variable [IsManifold I ∞ M]

/--
All-direction hosted linearized solutions by rescaling the PL-ball family.

The closed-ball export supplies solutions only for directions whose initial
state lies in the PL radius.  With a positive PL radius, each direction `w` is
normalized into that ball, solved there, and then scaled back.  The linearity of
`linearizedGeodesicFlowFieldAlong` gives the ODE for the scaled curve.
-/
theorem exists_hosted_rescaled_linearized_solution_family
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M)
    {γ : ℝ → E × E} {ε T : ℝ} (hε : 0 < ε)
    {a r L K : ℝ≥0} (hr : 0 < (r : ℝ))
    (hpl : IsPicardLindelof
      (fun t : ℝ => fun ψ : E × E =>
        linearizedGeodesicFlowOperator
          (GeodesicTransport.chartChristoffelField g x₀) (γ t) ψ)
      (tmin := -ε) (tmax := ε)
      ⟨(0 : ℝ), by constructor <;> linarith⟩
      ((0 : E), (0 : E)) a r L K) :
    ∃ Ψ : E → ℝ → E × E,
      (∀ w : E, Ψ w 0 = ((0 : E), T⁻¹ • w)) ∧
        ∀ w : E, ∀ t ∈ Icc (-ε) ε,
          HasDerivWithinAt (Ψ w)
            (linearizedGeodesicFlowFieldAlong
              (GeodesicTransport.chartChristoffelField g x₀)
              γ t (Ψ w t))
            (Icc (-ε) ε) t := by
  rcases
    LinearizedFamilyExport.exists_hosted_linearized_solution_family_on_pl_closedBall
      (g := g) (x₀ := x₀) (γ := γ) (ε := ε) (T := T)
      hε hpl with
    ⟨Ψ₀, hΨ₀⟩
  let scale : E → ℝ :=
    fun w => max 1 ((2 * ‖T⁻¹ • w‖) / (r : ℝ))
  let base : E → E := fun w => (scale w)⁻¹ • w
  have hscale_pos : ∀ w : E, 0 < scale w := by
    intro w
    exact lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hbase_mem :
      ∀ w : E, ((0 : E), T⁻¹ • base w) ∈
        closedBall ((0 : E), (0 : E)) r := by
    intro w
    have hscale_ge :
        (2 * ‖T⁻¹ • w‖) / (r : ℝ) ≤ scale w :=
      le_max_right _ _
    have hhalf_nonneg : 0 ≤ (r : ℝ) / 2 := by linarith
    have hnorm_le_half :
        ‖T⁻¹ • base w‖ ≤ (r : ℝ) / 2 := by
      have hmul_le :
          ((r : ℝ) / 2) * ((2 * ‖T⁻¹ • w‖) / (r : ℝ)) ≤
            ((r : ℝ) / 2) * scale w :=
        mul_le_mul_of_nonneg_left hscale_ge hhalf_nonneg
      have hleft :
          ((r : ℝ) / 2) * ((2 * ‖T⁻¹ • w‖) / (r : ℝ)) =
            ‖T⁻¹ • w‖ := by
        field_simp [ne_of_gt hr]
      have hnorm_div :
          ‖T⁻¹ • base w‖ = ‖T⁻¹ • w‖ / scale w := by
        have hcomm :
            T⁻¹ • base w = (scale w)⁻¹ • (T⁻¹ • w) := by
          simp [base, smul_smul, mul_comm]
        have hscale_abs : |(scale w)⁻¹| = (scale w)⁻¹ := by
          rw [abs_of_pos]
          exact inv_pos.mpr (hscale_pos w)
        rw [hcomm, norm_smul, Real.norm_eq_abs, hscale_abs, div_eq_inv_mul]
      rw [hnorm_div, div_le_iff₀ (hscale_pos w)]
      calc
        ‖T⁻¹ • w‖ = ((r : ℝ) / 2) * ((2 * ‖T⁻¹ • w‖) / (r : ℝ)) :=
          hleft.symm
        _ ≤ ((r : ℝ) / 2) * scale w := hmul_le
    rw [Metric.mem_closedBall, dist_eq_norm]
    have hnorm_pair :
        ‖((0 : E), T⁻¹ • base w) - ((0 : E), (0 : E))‖ ≤ (r : ℝ) := by
      simpa [Prod.norm_def] using hnorm_le_half.trans (by linarith : (r : ℝ) / 2 ≤ r)
    exact hnorm_pair
  refine ⟨fun w t => scale w • Ψ₀ (base w) t, ?_, ?_⟩
  · intro w
    have hlocal := (hΨ₀ (base w) (hbase_mem w)).1
    have hsne : scale w ≠ 0 := ne_of_gt (hscale_pos w)
    calc
      scale w • Ψ₀ (base w) 0 =
          scale w • ((0 : E), T⁻¹ • base w) := by rw [hlocal]
      _ = ((0 : E), T⁻¹ • w) := by
        have hscalar : scale w * (T⁻¹ * (scale w)⁻¹) = T⁻¹ := by
          field_simp [hsne]
        have hvec : scale w • (T⁻¹ • base w) = T⁻¹ • w := by
          ext i
          simp [base, smul_smul, hscalar]
        exact Prod.ext (by simp) hvec
  · intro w t ht
    have hlocal := (hΨ₀ (base w) (hbase_mem w)).2.1 t ht
    simpa [linearizedGeodesicFlowFieldAlong_smul] using
      hlocal.const_smul (scale w)

end LinearizedRescale
end Poincare
