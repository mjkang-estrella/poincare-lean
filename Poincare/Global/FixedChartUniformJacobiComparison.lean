import Poincare.Global.FixedChartUniformDifferentialPullback

/-!
# Variations along retained fixed-chart geodesics

The derivative identification includes the retained endpoint time and keeps
both the moving initial position and the inverse-time velocity normalization.
-/

noncomputable section
open Filter Metric Set
open scoped Manifold ContDiff Topology NNReal unitInterval
namespace Poincare
universe u
local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3
variable {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold I ∞ M]
variable {g : ClosedSmoothRiemannianMetric 3 M}

namespace FixedChartUniformJacobiComparison
open CartanSuppliedDifferentialSuccessor FixedChartLocalSuccessorExistence
open FixedChartUniformDifferentialPullback

/-- A fundamental solution for the retained flow identifies its full state
 derivative, including both endpoints of the closed time interval. -/
theorem flow_hasFDerivAt_of_fundamentalSolution {x₀ : M} {U : Set E}
    (C : FixedChartUniformSourceNormal.Patch g x₀ U)
    {q : E × E} (hq : q ∈ ball (extChartAt I x₀ x₀, 0) (C.r : ℝ))
    {Φ : ℝ → (E × E) →L[ℝ] (E × E)}
    (hΦ0 : Φ 0 = ContinuousLinearMap.id ℝ (E × E))
    (hΦ : ∀ t ∈ Icc (-C.T) C.T, HasDerivWithinAt Φ
      ((linearizedGeodesicFlowOperator (GeodesicTransport.chartChristoffelField g x₀)
        (C.α q t)).comp (Φ t)) (Icc (-C.T) C.T) t)
    {t : ℝ} (ht : t ∈ Icc (-C.T) C.T) :
    HasFDerivAt (fun y => C.α y t) (Φ t) q := by
  have hF := GeodesicTransport.geodesicFlowField_chartChristoffelField_contDiff_two g x₀
  obtain ⟨G, hG, a, hGa⟩ :=
    GeodesicFlowJointDerivative.exists_smoothField_near_uniformFlow
      (U := Set.univ) isOpen_univ (fun _ _ => hF.contDiffAt)
      C.continuous_flow (fun _ _ _ _ => Set.mem_univ _)
  have hαG : ∀ y ∈ ball (extChartAt I x₀ x₀, 0) (C.r : ℝ),
      C.α y 0 = y ∧
      (∀ s ∈ Icc (-C.T) C.T, HasDerivWithinAt (C.α y)
        (G (C.α y s)) (Icc (-C.T) C.T) s) ∧
      ∀ s ∈ Icc (-C.T) C.T, C.α y s ∈ closedBall (extChartAt I x₀ x₀, 0) a := by
    intro y hy
    have hyc := ball_subset_closedBall hy
    refine ⟨(C.flow_law y hyc).1, ?_, fun s hs => (hGa y hyc s hs).1⟩
    intro s hs
    rw [(hGa y hyc s hs).2.eq_of_nhds]
    exact (C.flow_law y hyc).2 s hs
  apply GeodesicFlowJointDerivative.flow_hasFDerivAt_initialState
    (hG.of_le (by norm_num)) C.T_pos hq hαG hΦ0 ?_ ht
  intro s hs
  simpa only [(hGa q (ball_subset_closedBall hq) s hs).2.fderiv_eq] using hΦ s hs

/-- The actual coordinate exponential differentiates to the position component
of the full retained endpoint derivative, with the required inverse-time input. -/
theorem coordinateEndpoint_fderiv {x₀ : M} {U : Set E}
    (C : FixedChartUniformSourceNormal.Patch g x₀ U)
    (x : M) (v a : E) (hv : v ∈ (C.endpoint x).source) :
    fderiv ℝ ((C.endpoint x).trans (chartAt E x₀)) v a =
      (fderiv ℝ (fun q => C.α q C.T)
        (extChartAt I x₀ x, C.T⁻¹ • v) (0, C.T⁻¹ • a)).1 := by
  have hq := C.P_source_subset hv.1.2
  have hfull := (C.endpoint_C1.contDiffAt (isOpen_ball.mem_nhds hq)).differentiableAt
    (by norm_num)
  have hs := hfull.hasFDerivAt.fst.comp v
    ((hasFDerivAt_const (extChartAt I x₀ x) v).prodMk C.timeRescaling.hasFDerivAt)
  have he : HasFDerivAt ((C.endpoint x).trans (chartAt E x₀))
      (((ContinuousLinearMap.fst ℝ E E).comp
        (fderiv ℝ (fun q => C.α q C.T) (extChartAt I x₀ x, C.T⁻¹ • v))).comp
        ((0 : E →L[ℝ] E).prod (C.timeRescaling : E →L[ℝ] E))) v := by
    apply hs.congr_of_eventuallyEq
    filter_upwards [(C.endpoint x).open_source.mem_nhds hv] with w hw
    exact coordinateEndpoint_eq_normalizedEndpoint C x w hw
  rw [he.fderiv]
  rfl

end FixedChartUniformJacobiComparison
end Poincare
