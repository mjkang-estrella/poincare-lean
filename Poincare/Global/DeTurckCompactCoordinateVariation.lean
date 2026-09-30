import Poincare.Global.DeTurckChartLiftDefinitions
import Poincare.Global.CompactCoefficientEllipticity
import Mathlib.Analysis.Normed.Group.Bounded

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 100
open Set
open scoped Manifold ContDiff Topology
universe u

namespace Poincare.DeTurckChartLift

local instance coordinateVariationBilinBoundedSMul : IsBoundedSMul ℝ Bilin :=
  .of_norm_smul_le (fun c A => ContinuousLinearMap.opNorm_smul_le c A)

variable {M : Type u} [TopologicalSpace M] [T2Space M] [ChartedSpace E M]
  [IsManifold I ∞ M]

omit [T2Space M] in
/-- The actual initial metric is smooth as a bilinear field on the chart target. -/
theorem initial_chartMetric_contDiffOn
    (g0 : ClosedSmoothRiemannianMetric 3 M) (anchor : M) :
    ContDiffOn ℝ ∞ (_root_.CovariantDerivative.chartMetric g0.inner anchor)
      (extChartAt I anchor).target := by
  apply contDiffOn_clm_apply.mpr
  intro v
  apply contDiffOn_clm_apply.mpr
  intro w
  exact (_root_.CovariantDerivative.contMDiffOn_chartMetric_pairing
    g0.inner anchor (m := ∞) (by simp) g0.contMDiff_inner v w).contDiffOn

omit [T2Space M] in
/-- The actual initial metric is positive on the whole genuine chart target. -/
theorem initial_chartMetric_pos
    (g0 : ClosedSmoothRiemannianMetric 3 M) (anchor : M) {z : E}
    (hz : z ∈ (extChartAt I anchor).target) {v : E} (hv : v ≠ 0) :
    0 < (_root_.CovariantDerivative.chartMetric g0.inner anchor z) v v := by
  exact _root_.CovariantDerivative.chartMetric_posDef g0.inner
    (fun x a ha => g0.inner_pos x ha) anchor
    (isInvertible_mfderivWithin_extChartAt_symm hz) hv

/-- A compact coordinate perturbation has one positive radius for both parameter signs. -/
theorem exists_coordinate_variation_radius
    (g0 : ClosedSmoothRiemannianMetric 3 M) (anchor : M) (F : E → Bilin)
    (hF : ContDiff ℝ ∞ F) (hcompact : HasCompactSupport F)
    (hsupport : tsupport F ⊆ (extChartAt I anchor).target) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ s : ℝ, |s| < ε →
      ∀ z ∈ (extChartAt I anchor).target, ∀ v : E, v ≠ 0 →
      0 < (_root_.CovariantDerivative.chartMetric g0.inner anchor z + s • F z) v v := by
  letI : CompactSpace (tsupport F) := isCompact_iff_compactSpace.mp hcompact
  have hcontinuous : Continuous
      (fun z : tsupport F => _root_.CovariantDerivative.chartMetric g0.inner anchor z) :=
    ((initial_chartMetric_contDiffOn g0 anchor).continuousOn.mono hsupport).restrict
  obtain ⟨c, hc, hcoercive⟩ := CompactCoefficientEllipticity.exists_uniform_coercivity
    (fun z : tsupport F => _root_.CovariantDerivative.chartMetric g0.inner anchor z)
    hcontinuous (fun z v hv => initial_chartMetric_pos g0 anchor (hsupport z.property) hv)
  obtain ⟨C, hC⟩ := hcompact.exists_bound_of_continuous hF.continuous
  let B : ℝ := max C 0
  have hB : 0 ≤ B := le_max_right C 0
  have hbound (z : E) : ‖F z‖ ≤ B := (hC z).trans (le_max_left C 0)
  have hden : 0 < B + 1 := by linarith
  refine ⟨c / (B + 1), div_pos hc hden, ?_⟩
  intro s hs z hz v hv
  by_cases hzs : z ∈ tsupport F
  · have habs : |s| * B < c := calc
      |s| * B ≤ |s| * (B + 1) :=
        mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg s)
      _ < c := (lt_div_iff₀ hden).mp hs
    have hquadratic : |F z v v| ≤ B * ‖v‖ ^ 2 := by
      calc
        |F z v v| = ‖F z v v‖ := (Real.norm_eq_abs _).symm
        _ ≤ ‖F z v‖ * ‖v‖ := (F z v).le_opNorm v
        _ ≤ (‖F z‖ * ‖v‖) * ‖v‖ :=
          mul_le_mul_of_nonneg_right ((F z).le_opNorm v) (norm_nonneg v)
        _ ≤ (B * ‖v‖) * ‖v‖ := by gcongr; exact hbound z
        _ = B * ‖v‖ ^ 2 := by ring
    have hperturbation : -(|s| * B * ‖v‖ ^ 2) ≤ s * F z v v := by
      have hnorm : |s * F z v v| ≤ |s| * B * ‖v‖ ^ 2 := by
        rw [abs_mul]
        calc
          |s| * |F z v v| ≤ |s| * (B * ‖v‖ ^ 2) :=
            mul_le_mul_of_nonneg_left hquadratic (abs_nonneg s)
          _ = |s| * B * ‖v‖ ^ 2 := by ring
      have hlower := neg_abs_le (s * F z v v)
      linarith
    have hbase := hcoercive ⟨z, hzs⟩ v
    have hnormpos : 0 < ‖v‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hv)
    have hmargin : 0 < (c - |s| * B) * ‖v‖ ^ 2 :=
      mul_pos (sub_pos.mpr habs) hnormpos
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    nlinarith
  · rw [image_eq_zero_of_notMem_tsupport hzs]
    simpa using initial_chartMetric_pos g0 anchor hz hv

end Poincare.DeTurckChartLift
