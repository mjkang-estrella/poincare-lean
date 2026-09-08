import Poincare.Global.FixedChartPatchSecondVariation

/-!
# Full-interval regularity of the retained operator-augmented flow

Linear continuation and Gronwall identification preserve the supplied time.
Local compact neighborhoods cover the entire retained open state ball.
-/

noncomputable section
set_option maxHeartbeats 1200000
set_option maxRecDepth 4000
open Filter Function Metric Set
open scoped Manifold ContDiff Topology NNReal

namespace Poincare.FixedChartAugmentedSystemRegularity

open FixedChartPatchSecondVariation GeodesicFlowJointDerivative

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Linear continuation supplies a C1 flow on the whole prescribed interval
when the given trajectories lie in one compact state tube. -/
theorem exists_flow_initialState_C1_full_interval [ProperSpace X] [CompleteSpace X]
    {F : X → X} (hF : ContDiff ℝ 2 F)
    {α : X → ℝ → X} {p : X} {r a T : ℝ} (hT : 0 < T)
    (hα : ∀ q ∈ ball p r, α q 0 = q ∧
      (∀ s ∈ Icc (-T) T, HasDerivWithinAt (α q) (F (α q s)) (Icc (-T) T) s) ∧
      ∀ s ∈ Icc (-T) T, α q s ∈ closedBall p a) :
    ∃ Φ : X → ℝ → X →L[ℝ] X,
      (∀ q ∈ ball p r, Φ q 0 = ContinuousLinearMap.id ℝ X) ∧
      (∀ q ∈ ball p r, ∀ t ∈ Icc (-T) T, HasDerivWithinAt (Φ q)
        ((fderiv ℝ F (α q t)).comp (Φ q t)) (Icc (-T) T) t) ∧
      (∀ q ∈ ball p r, ∀ t ∈ Icc (-T) T,
        HasFDerivAt (fun y => α y t) (Φ q t) q) ∧
      ContinuousOn (fun qt : X × ℝ => Φ qt.1 qt.2) (ball p r ×ˢ Icc (-T) T) ∧
      ∀ t ∈ Icc (-T) T, ContDiffOn ℝ 1 (fun q => α q t) (ball p r) := by
  classical
  have hF1 : ContDiff ℝ 1 F := hF.of_le (by norm_num)
  have hex : ∀ q : X, ∃ Φ : ℝ → X →L[ℝ] X, q ∈ ball p r →
      Φ 0 = ContinuousLinearMap.id ℝ X ∧
      ∀ s ∈ Icc (-T) T, HasDerivWithinAt Φ
        ((fderiv ℝ F (α q s)).comp (Φ s)) (Icc (-T) T) s := by
    intro q
    by_cases hq : q ∈ ball p r
    · have hc : ContinuousOn (fun s => fderiv ℝ F (α q s)) (Icc (-T) T) :=
        (hF1.continuous_fderiv (by norm_num)).comp_continuousOn
          (HasDerivWithinAt.continuousOn (hα q hq).2.1)
      obtain ⟨Φ, h0, hd⟩ :=
        FixedChartUniformJacobiComparison.exists_fundamentalSolution_on_Icc hT.le hc
      exact ⟨Φ, fun _ => ⟨h0, hd⟩⟩
    · exact ⟨fun _ => ContinuousLinearMap.id ℝ X, fun h => (hq h).elim⟩
  choose Φ hΦ using hex
  have h0 := fun q hq => (hΦ q hq).1
  have hd := fun q hq => (hΦ q hq).2
  have hder : ∀ q ∈ ball p r, ∀ t ∈ Icc (-T) T,
      HasFDerivAt (fun y => α y t) (Φ q t) q :=
    fun q hq t ht => flow_hasFDerivAt_initialState hF1 hT hq hα (h0 q hq) (hd q hq) ht
  have hc := continuousOn_fundamentalSolution hF hT.le hα h0 hd
  refine ⟨Φ, h0, hd, hder, hc, ?_⟩
  intro t ht q hq
  apply ContDiffAt.contDiffWithinAt
  apply contDiffAt_one_iff.mpr
  refine ⟨fun y => Φ y t, ball p r, isOpen_ball.mem_nhds hq, ?_, fun y hy => hder y hy t ht⟩
  exact hc.comp (continuous_id.prodMk continuous_const).continuousOn (fun y hy => ⟨hy, ht⟩)


end Poincare.FixedChartAugmentedSystemRegularity
