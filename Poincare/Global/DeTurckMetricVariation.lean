import Poincare.Global.DeTurckChartLiftSmoothness
import Poincare.Global.DeTurckCompactCoordinateVariation
import Poincare.Global.SmoothInitialMetricPositiveCone
import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 100
open Bundle FiberBundle Set
open scoped Manifold ContDiff Topology
universe u

namespace Poincare.DeTurckChartLift

variable {M : Type u} [TopologicalSpace M] [T2Space M] [ChartedSpace E M]
  [IsManifold I ∞ M]

omit [T2Space M] in
/-- Coordinate positivity transfers through the injective forward chart differential. -/
theorem affine_chartLift_pos
    (g0 : ClosedSmoothRiemannianMetric 3 M) (anchor : M) (F : E → Bilin)
    (s : ℝ)
    (hpositive : ∀ z ∈ (extChartAt I anchor).target, ∀ v : E, v ≠ 0 →
      0 < (_root_.CovariantDerivative.chartMetric g0.inner anchor z + s • F z) v v)
    (x : M) (v : TangentSpace I x) (hv : v ≠ 0) :
    0 < (g0.inner x + s • chartLift anchor F x) v v := by
  classical
  by_cases hx : x ∈ (extChartAt I anchor).source
  · have hAv : mfderiv I 𝓘(ℝ, E) (extChartAt I anchor) x v ≠ 0 := by
      intro hzero
      apply hv
      have hc := congrArg (fun L => L v)
        (mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt'
          (I := I) (x := anchor) hx)
      simp only [ContinuousLinearMap.comp_apply] at hc
      rw [hzero, map_zero] at hc
      exact hc.symm
    have h := hpositive (extChartAt I anchor x) ((extChartAt I anchor).map_source hx)
      (mfderiv I 𝓘(ℝ, E) (extChartAt I anchor) x v) hAv
    simpa only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      smul_eq_mul, _root_.CovariantDerivative.chartMetric_apply_chart g0.inner anchor hx,
      chartLift_eq_localPullback anchor F hx, localPullback_apply] using h
  · simpa only [chartLift, if_neg hx, smul_zero, add_zero] using g0.inner_pos x hv

/-- Adding a fixed multiple of the actual lift preserves smooth bundle sections. -/
theorem affine_chartLift_contMDiff
    (g0 : ClosedSmoothRiemannianMetric 3 M) (anchor : M) (F : E → Bilin)
    (hF : ContDiff ℝ ∞ F) (hcompact : HasCompactSupport F)
    (hsupport : tsupport F ⊆ (extChartAt I anchor).target) (s : ℝ) :
    ContMDiff I (I.prod 𝓘(ℝ, Bilin)) ∞
      (fun x : M => TotalSpace.mk' Bilin x (g0.inner x + s • chartLift anchor F x)) := by
  exact g0.contMDiff_inner.add_section
    ((chartLift_contMDiff M anchor F hF hcompact hsupport).const_smul_section (a := s))

omit [T2Space M] in
/-- The finite-dimensional tangent topology bounds every positive quadratic unit ball. -/
theorem affine_chartLift_unitBall
    (g0 : ClosedSmoothRiemannianMetric 3 M) (anchor : M) (F : E → Bilin)
    (s : ℝ) (x : M)
    (hpositive : ∀ v : TangentSpace I x, v ≠ 0 →
      0 < (g0.inner x + s • chartLift anchor F x) v v) :
    Bornology.IsVonNBounded ℝ
      {v : TangentSpace I x | (g0.inner x + s • chartLift anchor F x) v v < 1} := by
  -- These canonical model instances have the original fiber topology and scalar operations.
  letI metricVariationFiberNormedAddCommGroup : NormedAddCommGroup (TangentSpace I x) :=
    inferInstanceAs (NormedAddCommGroup E)
  letI metricVariationFiberNormedSpace : NormedSpace ℝ (TangentSpace I x) :=
    inferInstanceAs (NormedSpace ℝ E)
  letI metricVariationFiberDualTopology : TopologicalSpace (TangentSpace I x →L[ℝ] ℝ) :=
    ContinuousLinearMap.topologicalSpace
  letI metricVariationFiberFiniteDimensional : FiniteDimensional ℝ (TangentSpace I x) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  exact SmoothInitialMetricPositiveCone.isVonNBounded_bilinear_unitBall
    (g0.inner x + s • chartLift anchor F x) hpositive

/-- A compact smooth symmetric tensor gives genuine metrics on one signed interval. -/
theorem exists_actual_metric_variation
    (M : Type u) [TopologicalSpace M] [T2Space M] [ChartedSpace E M]
    [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
    (g0 : ClosedSmoothRiemannianMetric 3 M) (anchor : M) (F : E → Bilin)
    (hF : ContDiff ℝ ∞ F) (hcompact : HasCompactSupport F)
    (hsupport : tsupport F ⊆ (extChartAt I anchor).target)
    (hsymm : ∀ z v w : E, F z v w = F z w v) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ gt : ℝ → ClosedSmoothRiemannianMetric 3 M,
      gt 0 = g0 ∧
      (∀ s : ℝ, |s| < ε → ∀ x : M,
        (gt s).inner x = g0.inner x + s • chartLift anchor F x) ∧
      ∀ s : ℝ, |s| < ε → ∀ z ∈ (extChartAt I anchor).target,
        _root_.CovariantDerivative.chartMetric (I := I) (gt s).inner anchor z =
          _root_.CovariantDerivative.chartMetric (I := I) g0.inner anchor z + s • F z := by
  classical
  obtain ⟨ε, hε, hpositive⟩ :=
    exists_coordinate_variation_radius g0 anchor F hF hcompact hsupport
  let metric (s : ℝ) (hs : |s| < ε) : ClosedSmoothRiemannianMetric 3 M := {
    inner := fun x => g0.inner x + s • chartLift anchor F x
    symm := by
      intro x v w
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
        g0.inner_symm x v w, chartLift_symmetric anchor F hsymm x v w]
    pos := affine_chartLift_pos g0 anchor F s (hpositive s hs)
    isVonNBounded := fun x => affine_chartLift_unitBall g0 anchor F s x
      (affine_chartLift_pos g0 anchor F s (hpositive s hs) x)
    contMDiff := affine_chartLift_contMDiff g0 anchor F hF hcompact hsupport s }
  let gt (s : ℝ) : ClosedSmoothRiemannianMetric 3 M :=
    if s = 0 then g0 else if hs : |s| < ε then metric s hs else g0
  have hinner (s : ℝ) (hs : |s| < ε) (x : M) :
      (gt s).inner x = g0.inner x + s • chartLift anchor F x := by
    by_cases hs0 : s = 0
    · simp [gt, hs0]
    · simp only [gt, if_neg hs0, dif_pos hs, metric]
  refine ⟨ε, hε, gt, by simp [gt], hinner, ?_⟩
  intro s hs z hz
  ext v w
  rw [_root_.CovariantDerivative.chartMetric_apply, hinner s hs]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply]
  rw [← _root_.CovariantDerivative.chartMetric_apply,
    ← _root_.CovariantDerivative.chartMetric_apply,
    chartMetric_chartLift anchor F z hz]

end Poincare.DeTurckChartLift
