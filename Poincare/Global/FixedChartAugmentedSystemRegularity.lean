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


/-- Joint continuity on an open set of initial states supplies local compact
trajectory tubes. C1 dependence holds everywhere on that same open set. -/
theorem flow_contDiffOn_one_full_interval [ProperSpace X] [CompleteSpace X]
    {F : X → X} (hF : ContDiff ℝ 2 F)
    {α : X → ℝ → X} {S : Set X} (hS : IsOpen S)
    {T : ℝ} (hT : 0 < T)
    (hc : ContinuousOn (Function.uncurry α) (S ×ˢ Icc (-T) T))
    (hα : ∀ q ∈ S, α q 0 = q ∧
      ∀ t ∈ Icc (-T) T, HasDerivWithinAt (α q) (F (α q t)) (Icc (-T) T) t) :
    ∀ t ∈ Icc (-T) T, ContDiffOn ℝ 1 (fun q => α q t) S := by
  intro t ht q hq
  obtain ⟨r, hr, hsub⟩ : ∃ r > 0, closedBall q r ⊆ S :=
    Metric.nhds_basis_closedBall.mem_iff.mp (hS.mem_nhds hq)
  have hcompact := ((isCompact_closedBall q r).prod isCompact_Icc).image_of_continuousOn
    (hc.mono (Set.prod_mono hsub Subset.rfl))
  obtain ⟨a, ha⟩ := hcompact.isBounded.subset_closedBall q
  obtain ⟨Φ, _, _, _, _, hC1⟩ := exists_flow_initialState_C1_full_interval
    (α := α) (p := q) (r := r) (a := a) hF hT (by
      intro y hy
      have hyc := ball_subset_closedBall hy
      exact ⟨(hα y (hsub hyc)).1, (hα y (hsub hyc)).2,
        fun s hs => ha ⟨(y, s), ⟨hyc, hs⟩, rfl⟩⟩)
  exact ((hC1 t ht).contDiffAt (isOpen_ball.mem_nhds (mem_ball_self hr))).contDiffWithinAt

universe u
local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3
variable {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold I ∞ M]
variable {g : ClosedSmoothRiemannianMetric 3 M}

/-- The retained fundamental solution lifts the patch to an actual flow for
all initial operators, jointly continuous throughout the full retained time. -/
theorem exists_patch_operatorAugmentedFlow
    {x₀ : M} {U : Set E} (C : FixedChartUniformSourceNormal.Patch g x₀ U) :
    ∃ Φ : (E × E) → ℝ → (E × E) →L[ℝ] (E × E),
      let β := fun (y : (E × E) × ((E × E) →L[ℝ] (E × E))) (t : ℝ) =>
        (C.α y.1 t, (Φ y.1 t).comp y.2)
      let S := ball (extChartAt I x₀ x₀, (0 : E)) (C.r : ℝ) ×ˢ
        (Set.univ : Set ((E × E) →L[ℝ] (E × E)))
      (∀ y ∈ S, β y 0 = y ∧ ∀ t ∈ Icc (-C.T) C.T,
        HasDerivWithinAt (β y)
          (operatorAugmentedField
            (geodesicFlowField (GeodesicTransport.chartChristoffelField g x₀))
            (β y t)) (Icc (-C.T) C.T) t) ∧
      ContinuousOn (Function.uncurry β) (S ×ˢ Icc (-C.T) C.T) := by
  obtain ⟨Φ, h0, hd, _, hc⟩ :=
    FixedChartUniformJacobiComparison.exists_patch_fundamentalSolution C
  refine ⟨Φ, ?_, ?_⟩
  · intro y hy
    refine ⟨?_, ?_⟩
    · simp [(C.flow_law y.1 (ball_subset_closedBall hy.1)).1, h0 y.1 hy.1]
    · intro t ht
      exact operatorAugmentedFlow_hasDerivWithinAt
        ((C.flow_law y.1 (ball_subset_closedBall hy.1)).2 t ht)
        (hd y.1 hy.1 t ht) y.2
  · have hm : Continuous (fun yt :
        (((E × E) × ((E × E) →L[ℝ] (E × E))) × ℝ) => (yt.1.1, yt.2)) :=
      continuous_fst.fst.prodMk continuous_snd
    let S := ball (extChartAt I x₀ x₀, (0 : E)) (C.r : ℝ) ×ˢ
      (Set.univ : Set ((E × E) →L[ℝ] (E × E)))
    have hcα := C.continuous_flow.comp
      (hm.continuousOn (s := S ×ˢ Icc (-C.T) C.T))
      (fun yt hyt => ⟨ball_subset_closedBall hyt.1.1, hyt.2⟩)
    have hcΦ := hc.comp (hm.continuousOn (s := S ×ˢ Icc (-C.T) C.T))
      (fun yt hyt => ⟨hyt.1.1, hyt.2⟩)
    exact hcα.prodMk (hcΦ.clm_comp continuous_fst.snd.continuousOn)

end Poincare.FixedChartAugmentedSystemRegularity
