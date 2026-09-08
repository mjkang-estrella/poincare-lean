import Poincare.Global.FixedChartUniformJacobiComparison

/-!
# Metric invariants along retained moving-position geodesics

The initial state ranges over the original patch ball. Time is never shrunk.
-/

noncomputable section
set_option maxHeartbeats 1200000
open Filter Metric Set
open scoped Manifold ContDiff Topology NNReal
namespace Poincare
universe u
local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3
variable {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold I ∞ M]
variable {g : ClosedSmoothRiemannianMetric 3 M}

namespace FixedChartMovingPositionJacobi
open GeodesicTransport
open FixedChartUniformJacobiComparison

/-- Every retained position lies in the chart target and has cutoff one on a
neighborhood, including at both endpoint times. -/
theorem flow_mem_target_cutoffOne {x₀ : M} {U : Set E}
    (C : FixedChartUniformSourceNormal.Patch g x₀ U)
    (hU : U ⊆ IsometryInstantiate.cutoffOneLocus x₀)
    {q : E × E} (hq : q ∈ closedBall (extChartAt I x₀ x₀, 0) (C.r : ℝ))
    {t : ℝ} (ht : t ∈ Icc (-C.T) C.T) :
    (C.α q t).1 ∈ (extChartAt I x₀).target ∧
      (∀ᶠ z in 𝓝 (C.α q t).1, cutoff (n := 3) x₀ z = 1) := by
  have hcut := hU (C.position_mem q hq t ht)
  refine ⟨?_, hcut⟩
  exact cutoff_tsupport x₀ (subset_tsupport _
    (Function.mem_support.mpr (by rw [hcut.self_of_nhds]; exact one_ne_zero)))

/-- Speed preservation on the entire retained interval, at arbitrary initial
position and velocity in the original closed state ball. -/
theorem flow_speed_eq_initial {x₀ : M} {U : Set E}
    (C : FixedChartUniformSourceNormal.Patch g x₀ U)
    {q : E × E} (hq : q ∈ closedBall (extChartAt I x₀ x₀, 0) (C.r : ℝ))
    {t : ℝ} (ht : t ∈ Icc (-C.T) C.T) :
    chartGeodesicMetric g x₀ (C.α q t).1 (C.α q t).2 (C.α q t).2 =
      chartGeodesicMetric g x₀ q.1 q.2 q.2 := by
  have hder := (C.flow_law q hq).2
  have hcont := HasDerivWithinAt.continuousOn hder
  have hmetric : Continuous (chartGeodesicMetric g x₀) :=
    continuous_iff_continuousAt.mpr (fun z =>
      (IsometryComplete.chartGeodesicMetric_differentiableAt g x₀ z).continuousAt)
  have heq : EqOn
      (fun t => chartGeodesicMetric g x₀ (C.α q t).1 (C.α q t).2 (C.α q t).2)
      (fun _ => chartGeodesicMetric g x₀ q.1 q.2 q.2) (Ioo (-C.T) C.T) := by
    intro s hs
    have h := chart_geodesic_speed_constantOn_Ioo g x₀
      (fun τ hτ => (hder τ (Ioo_subset_Icc_self hτ)).hasDerivAt
        (Icc_mem_nhds hτ.1 hτ.2)) hs
      (show (0 : ℝ) ∈ Ioo (-C.T) C.T from ⟨by linarith [C.T_pos], C.T_pos⟩)
    simpa only [(C.flow_law q hq).1] using h
  exact heq.of_subset_closure
    (((hmetric.comp_continuousOn hcont.fst).clm_apply hcont.snd).clm_apply hcont.snd)
    continuousOn_const Ioo_subset_Icc_self
    (by rw [closure_Ioo (show -C.T ≠ C.T by linarith [C.T_pos])]) ht

/-- On a cutoff-one patch the same invariant is the actual chart metric,
measured at the moving initial position. -/
theorem flow_chartMetric_speed_eq_initial {x₀ : M} {U : Set E}
    (C : FixedChartUniformSourceNormal.Patch g x₀ U)
    (hU : U ⊆ IsometryInstantiate.cutoffOneLocus x₀)
    {q : E × E} (hq : q ∈ closedBall (extChartAt I x₀ x₀, 0) (C.r : ℝ))
    {t : ℝ} (ht : t ∈ Icc (-C.T) C.T) :
    CovariantDerivative.chartMetric g.inner x₀ (C.α q t).1 (C.α q t).2 (C.α q t).2 =
      CovariantDerivative.chartMetric g.inner x₀ q.1 q.2 q.2 := by
  have h0 : (0 : ℝ) ∈ Icc (-C.T) C.T := ⟨by linarith [C.T_pos], C.T_pos.le⟩
  have hc0 := (flow_mem_target_cutoffOne C hU hq h0).2.self_of_nhds
  rw [(C.flow_law q hq).1] at hc0
  have h := flow_speed_eq_initial C hq ht
  dsimp only [chartGeodesicMetric] at h
  rw [blendedChartMetric_eq_chartMetric_of_cutoff_eq_one
    (g := g) (x₀ := x₀) (flow_mem_target_cutoffOne C hU hq ht).2.self_of_nhds,
    blendedChartMetric_eq_chartMetric_of_cutoff_eq_one (g := g) (x₀ := x₀) hc0] at h
  exact h

/-- Nearby initial-velocity variations preserve speed with their own moving
initial velocity. This is the eventual equality required by the Gauss lemma. -/
theorem perturbed_flow_speed_eq_initial {x₀ : M} {U : Set E}
    (C : FixedChartUniformSourceNormal.Patch g x₀ U)
    {z v : E} (hq : (z, v) ∈ ball (extChartAt I x₀ x₀, 0) (C.r : ℝ))
    (w : E) {t : ℝ} (ht : t ∈ Icc (-C.T) C.T) :
    (fun s : ℝ => chartGeodesicMetric g x₀ (C.α (z, v + s • w) t).1
      (C.α (z, v + s • w) t).2 (C.α (z, v + s • w) t).2) =ᶠ[𝓝 0]
    (fun s : ℝ => chartGeodesicMetric g x₀ z (v + s • w) (v + s • w)) := by
  have hc : ContinuousAt (fun s : ℝ => (z, v + s • w)) 0 :=
    continuousAt_const.prodMk (continuousAt_const.add (continuousAt_id.smul continuousAt_const))
  have he : ∀ᶠ s : ℝ in 𝓝 0,
      (z, v + s • w) ∈ ball (extChartAt I x₀ x₀, 0) (C.r : ℝ) :=
    hc.eventually (isOpen_ball.mem_nhds (by simpa using hq))
  filter_upwards [he] with s hs
  exact flow_speed_eq_initial C (ball_subset_closedBall hs) ht

/-- The arbitrary fundamental solution differentiates an actual velocity
variation of the retained flow at every retained time. -/
theorem velocityVariation_hasDerivAt {x₀ : M} {U : Set E}
    (C : FixedChartUniformSourceNormal.Patch g x₀ U)
    {z v : E} (hq : (z, v) ∈ ball (extChartAt I x₀ x₀, 0) (C.r : ℝ))
    {Φ : ℝ → (E × E) →L[ℝ] (E × E)}
    (hΦ0 : Φ 0 = ContinuousLinearMap.id ℝ (E × E))
    (hΦ : ∀ t ∈ Icc (-C.T) C.T, HasDerivWithinAt Φ
      ((linearizedGeodesicFlowOperator (chartChristoffelField g x₀)
        (C.α (z, v) t)).comp (Φ t)) (Icc (-C.T) C.T) t)
    (w : E) {t : ℝ} (ht : t ∈ Icc (-C.T) C.T) :
    HasDerivAt (fun s : ℝ => C.α (z, v + s • w) t) (Φ t (0, w)) 0 := by
  have hs : HasDerivAt (fun s : ℝ => (z, v + s • w)) (0, w) 0 := by
    simpa using (hasDerivAt_const (0 : ℝ) z).prodMk
      ((hasDerivAt_const (0 : ℝ) v).add ((hasDerivAt_id (0 : ℝ)).smul_const w))
  have hf := flow_hasFDerivAt_of_fundamentalSolution C hq hΦ0 hΦ ht
  have hf' : HasFDerivAt (fun y => C.α y t) (Φ t) (z, v + (0 : ℝ) • w) := by
    simpa only [zero_smul, add_zero] using hf
  exact hf'.comp_hasDerivAt 0 hs

/-- Initial transverse vectors remain orthogonal to the velocity through the
closed endpoints. All flow-variation and speed premises are discharged. -/
theorem transverse_orthogonal {x₀ : M} {U : Set E}
    (C : FixedChartUniformSourceNormal.Patch g x₀ U)
    (hU : U ⊆ IsometryInstantiate.cutoffOneLocus x₀)
    {z v : E} (hq : (z, v) ∈ ball (extChartAt I x₀ x₀, 0) (C.r : ℝ))
    {Φ : ℝ → (E × E) →L[ℝ] (E × E)}
    (hΦ0 : Φ 0 = ContinuousLinearMap.id ℝ (E × E))
    (hΦ : ∀ t ∈ Icc (-C.T) C.T, HasDerivWithinAt Φ
      ((linearizedGeodesicFlowOperator (chartChristoffelField g x₀)
        (C.α (z, v) t)).comp (Φ t)) (Icc (-C.T) C.T) t)
    (w : E) (horth : CovariantDerivative.chartMetric g.inner x₀ z v w = 0)
    {t : ℝ} (ht : t ∈ Icc (-C.T) C.T) :
    CovariantDerivative.chartMetric g.inner x₀ (C.α (z, v) t).1
      (Φ t (0, w)).1 (C.α (z, v) t).2 = 0 := by
  have hqc := ball_subset_closedBall hq
  have h0 : (0 : ℝ) ∈ Ioo (-C.T) C.T := ⟨by linarith [C.T_pos], C.T_pos⟩
  have hc0 := (flow_mem_target_cutoffOne C hU hqc (Ioo_subset_Icc_self h0)).2.self_of_nhds
  rw [(C.flow_law _ hqc).1] at hc0
  have horth' : chartGeodesicMetric g x₀ z v w = 0 := by
    dsimp only [chartGeodesicMetric]
    rw [blendedChartMetric_eq_chartMetric_of_cutoff_eq_one (g := g) (x₀ := x₀) hc0]
    exact horth
  have hΨ : ∀ s ∈ Icc (-C.T) C.T, HasDerivWithinAt (fun s => Φ s (0, w))
      (linearizedGeodesicFlowFieldAlong (chartChristoffelField g x₀)
        (C.α (z, v)) s (Φ s (0, w))) (Icc (-C.T) C.T) s := by
    intro s hs
    simpa using (hΦ s hs).clm_apply (hasDerivWithinAt_const s (Icc (-C.T) C.T) (0, w))
  have heq : EqOn
      (fun s => chartGeodesicMetric g x₀ (C.α (z, v) s).1
        (Φ s (0, w)).1 (C.α (z, v) s).2) (fun _ => 0) (Ioo (-C.T) C.T) := by
    intro s hs
    exact chart_initialVelocity_integrated_transverse_gauss_orthogonal g x₀
      (α := C.α) (z₀ := z) (v := v) (w := w) (Ψ := fun τ => Φ τ (0, w))
      (a := -C.T) (b := C.T) (t := s)
      (fun τ hτ => ((C.flow_law _ hqc).2 τ (Ioo_subset_Icc_self hτ)).hasDerivAt
        (Icc_mem_nhds hτ.1 hτ.2))
      (fun τ hτ => (hΨ τ (Ioo_subset_Icc_self hτ)).hasDerivAt (Icc_mem_nhds hτ.1 hτ.2))
      (fun τ hτ => velocityVariation_hasDerivAt C hq hΦ0 hΦ w (Ioo_subset_Icc_self hτ))
      (fun τ hτ => perturbed_flow_speed_eq_initial C hq w (Ioo_subset_Icc_self hτ))
      (fun τ _ => IsometryComplete.chartGeodesicMetric_differentiableAt g x₀ _)
      (IsometryComplete.chartGeodesicMetric_differentiableAt g x₀ z)
      (C.flow_law _ hqc).1 (by simp [hΦ0]) h0 horth' hs
  have hc := HasDerivWithinAt.continuousOn (C.flow_law _ hqc).2
  have hm : Continuous (chartGeodesicMetric g x₀) :=
    continuous_iff_continuousAt.mpr (fun z =>
      (IsometryComplete.chartGeodesicMetric_differentiableAt g x₀ z).continuousAt)
  have hall := heq.of_subset_closure
    (((hm.comp_continuousOn hc.fst).clm_apply
      (HasDerivWithinAt.continuousOn hΨ).fst).clm_apply hc.snd)
    continuousOn_const Ioo_subset_Icc_self
    (by rw [closure_Ioo (show -C.T ≠ C.T by linarith [C.T_pos])]) ht
  dsimp only [chartGeodesicMetric] at hall
  rw [blendedChartMetric_eq_chartMetric_of_cutoff_eq_one (g := g) (x₀ := x₀)
    (flow_mem_target_cutoffOne C hU hqc ht).2.self_of_nhds] at hall
  exact hall

end FixedChartMovingPositionJacobi
end Poincare
