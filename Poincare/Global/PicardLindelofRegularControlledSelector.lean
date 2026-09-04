import Poincare.Global.PointFlowVariationalSelectorTower
import Poincare.Global.LocalUniformTaylorRemainder

/-!
# Picard--Lindelof selectors retaining local regularity

The residual proof needs more than existence and joint continuity: it needs
a uniform Taylor remainder on a tube and a strict inner/outer tube margin.
Both facts are already present in the standard local `C¹` construction, but
are lost if only the final selected curves are retained.  This file repeats
the small quantitative construction and records those facts explicitly.
-/

noncomputable section

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000

open Filter Function Metric Set
open scoped ContDiff NNReal Topology

namespace Poincare

section RegularSelector

variable {X : Type*}
variable [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- A controlled selector together with the local `C¹` and strict tube data
needed by the Taylor/residual argument. -/
structure LocalRegularControlledContinuousAutonomousSelector
    (F : X → X) (x₀ : X)
    extends LocalControlledContinuousAutonomousSelector F x₀ where
  initialRadius_lt_tubeRadius : initialRadius < tubeRadius
  field_norm_le : ∀ x ∈ closedBall x₀ (tubeRadius : ℝ),
    ‖F x‖ ≤ speedBound
  speed_time_le_margin :
    (speedBound : ℝ) * epsilon ≤
      (tubeRadius : ℝ) - (initialRadius : ℝ)
  field_contDiffAt_one : ∀ x ∈ closedBall x₀ (tubeRadius : ℝ),
    ContDiffAt ℝ 1 F x

namespace LocalRegularControlledContinuousAutonomousSelector

variable {F : X → X} {x₀ : X}

/-- Radius of the protected inner tube used after halving the time interval. -/
def protectedInnerRadius
    (H : LocalRegularControlledContinuousAutonomousSelector F x₀) : ℝ :=
  ((H.tubeRadius : ℝ) + (H.initialRadius : ℝ)) / 2

/-- The protected radius is strictly smaller than the regularity tube. -/
theorem protectedInnerRadius_lt_tubeRadius
    (H : LocalRegularControlledContinuousAutonomousSelector F x₀) :
    H.protectedInnerRadius < (H.tubeRadius : ℝ) := by
  have hlt : (H.initialRadius : ℝ) < (H.tubeRadius : ℝ) := by
    exact_mod_cast H.initialRadius_lt_tubeRadius
  simp only [protectedInnerRadius]
  linarith

/-- The full regularity tube is a neighborhood of every point in the
protected inner tube. -/
theorem tube_mem_nhds_of_mem_protectedInnerBall
    (H : LocalRegularControlledContinuousAutonomousSelector F x₀)
    {x : X}
    (hx : x ∈ closedBall x₀ H.protectedInnerRadius) :
    closedBall x₀ (H.tubeRadius : ℝ) ∈ nhds x := by
  apply closedBall_mem_nhds_of_mem
  rw [Metric.mem_ball]
  exact (mem_closedBall.mp hx).trans_lt H.protectedInnerRadius_lt_tubeRadius

/-- Halving the selected time interval leaves every trajectory from the
retained initial ball inside the protected inner tube. -/
theorem selector_mem_protectedInnerBall
    (H : LocalRegularControlledContinuousAutonomousSelector F x₀)
    {x : X} (hx : x ∈ closedBall x₀ (H.initialRadius : ℝ))
    {t : ℝ}
    (ht : t ∈ Icc (-(H.epsilon / 2)) (H.epsilon / 2)) :
    H.selector x t ∈ closedBall x₀ H.protectedInnerRadius := by
  have hhalf_subset :
      Icc (-(H.epsilon / 2)) (H.epsilon / 2) ⊆
        Icc (-H.epsilon) H.epsilon := by
    have hepsilon := H.epsilon_pos
    intro s hs
    have hhalf : H.epsilon / 2 ≤ H.epsilon := half_le_self hepsilon.le
    exact ⟨(neg_le_neg hhalf).trans hs.1, hs.2.trans hhalf⟩
  have hdata := H.selector_data x hx
  have hder : ∀ s ∈ Icc (-(H.epsilon / 2)) (H.epsilon / 2),
      HasDerivWithinAt (H.selector x) (F (H.selector x s))
        (Icc (-(H.epsilon / 2)) (H.epsilon / 2)) s := by
    intro s hs
    exact (hdata.2.1 s (hhalf_subset hs)).mono hhalf_subset
  have hbound : ∀ s ∈ Icc (-(H.epsilon / 2)) (H.epsilon / 2),
      ‖F (H.selector x s)‖ ≤ (H.speedBound : ℝ) := by
    intro s hs
    exact H.field_norm_le _ (hdata.2.2 s (hhalf_subset hs))
  have hzero : (0 : ℝ) ∈
      Icc (-(H.epsilon / 2)) (H.epsilon / 2) := by
    have hepsilon := H.epsilon_pos
    constructor <;> linarith
  have hmvt :
      ‖H.selector x t - H.selector x 0‖ ≤
        (H.speedBound : ℝ) * ‖t - 0‖ := by
    exact Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := H.selector x) (f' := fun s ↦ F (H.selector x s))
      (s := Icc (-(H.epsilon / 2)) (H.epsilon / 2))
      (x := 0) (y := t) hder hbound
      (convex_Icc (-(H.epsilon / 2)) (H.epsilon / 2)) hzero ht
  have htimeNorm : ‖t‖ ≤ H.epsilon / 2 := by
    rw [Real.norm_eq_abs]
    exact abs_le.mpr ht
  have hdisplacement :
      dist (H.selector x t) x ≤
        (H.speedBound : ℝ) * (H.epsilon / 2) := by
    calc
      dist (H.selector x t) x = ‖H.selector x t - H.selector x 0‖ := by
        rw [hdata.1, dist_eq_norm]
      _ ≤ (H.speedBound : ℝ) * ‖t - 0‖ := hmvt
      _ ≤ (H.speedBound : ℝ) * (H.epsilon / 2) := by
        simpa using mul_le_mul_of_nonneg_left htimeNorm H.speedBound.2
  rw [Metric.mem_closedBall]
  have hxdist : dist x x₀ ≤ (H.initialRadius : ℝ) :=
    mem_closedBall.mp hx
  have hspeedMargin := H.speed_time_le_margin
  calc
    dist (H.selector x t) x₀ ≤
        dist (H.selector x t) x + dist x x₀ := dist_triangle _ _ _
    _ ≤ (H.speedBound : ℝ) * (H.epsilon / 2) +
        (H.initialRadius : ℝ) := add_le_add hdisplacement hxdist
    _ ≤ H.protectedInnerRadius := by
      simp only [protectedInnerRadius]
      linarith

/-- Pointwise local `C¹` regularity on the retained tube gives the exact
compact-uniform Taylor estimate consumed by the residual theorem. -/
theorem uniform_taylor_remainder_on_tube
    [ProperSpace X]
    (H : LocalRegularControlledContinuousAutonomousSelector F x₀) :
    ∀ epsilon > (0 : ℝ), ∃ delta > (0 : ℝ),
      ∀ x ∈ closedBall x₀ (H.tubeRadius : ℝ),
        ∀ y ∈ closedBall x₀ (H.tubeRadius : ℝ),
          ‖y - x‖ ≤ delta →
            ‖F y - F x - fderiv ℝ F x (y - x)‖ ≤
              epsilon * ‖y - x‖ := by
  exact uniform_taylor_remainder_norm_le_on_compact_convex_of_contDiffAt
    H.field_contDiffAt_one
    (isCompact_closedBall x₀ (H.tubeRadius : ℝ))
    (convex_closedBall x₀ (H.tubeRadius : ℝ))

end LocalRegularControlledContinuousAutonomousSelector

variable [CompleteSpace X]

/-- Every local `C¹` field has a regular controlled selector whose protected
inner ball lies in any prescribed neighborhood of the initial state. -/
theorem exists_localRegularControlledContinuousAutonomousSelector_of_contDiffAt_one_with_protectedInnerBall_subset
    (F : X → X) (x₀ : X) (hF : ContDiffAt ℝ 1 F x₀)
    {U : Set X} (hU : U ∈ nhds x₀) :
    ∃ H : LocalRegularControlledContinuousAutonomousSelector F x₀,
      closedBall x₀ H.protectedInnerRadius ⊆ U := by
  obtain ⟨K, s, hs, hLipS⟩ := hF.exists_lipschitzOnWith
  have hregular : {x : X | ContDiffAt ℝ 1 F x} ∈ nhds x₀ :=
    hF.eventually (by norm_num)
  have hgood : (s ∩ {x : X | ContDiffAt ℝ 1 F x}) ∩ U ∈ nhds x₀ :=
    inter_mem (inter_mem hs hregular) hU
  obtain ⟨R, hR, hRsub⟩ := Metric.mem_nhds_iff.mp hgood
  let speed : ℝ := (K : ℝ) * R + ‖F x₀‖ + 1
  have hspeed : 0 < speed := by
    dsimp only [speed]
    positivity
  let tube : ℝ≥0 := ⟨R / 2, (half_pos hR).le⟩
  let initial : ℝ≥0 := tube / 2
  let speedNN : ℝ≥0 := ⟨speed, hspeed.le⟩
  let epsilon : ℝ := R / speed / 2 / 2
  have hepsilon : 0 < epsilon := by
    dsimp only [epsilon]
    positivity
  have hinitial : 0 < initial := by
    have htube : 0 < tube := by
      dsimp only [tube]
      exact_mod_cast half_pos hR
    dsimp only [initial]
    exact half_pos htube
  have hinitial_lt : initial < tube := by
    dsimp only [initial]
    exact half_lt_self (by
      dsimp only [tube]
      exact_mod_cast half_pos hR)
  have htube_to_good :
      closedBall x₀ (tube : ℝ) ⊆
        (s ∩ {x : X | ContDiffAt ℝ 1 F x}) ∩ U := by
    apply subset_trans _ hRsub
    change closedBall x₀ (R / 2) ⊆ ball x₀ R
    exact closedBall_subset_ball (half_lt_self hR)
  have hLip : LipschitzOnWith K F (closedBall x₀ (tube : ℝ)) :=
    hLipS.mono (fun x hx ↦ (htube_to_good hx).1.1)
  have hnorm : ∀ x ∈ closedBall x₀ (tube : ℝ), ‖F x‖ ≤ speedNN := by
    intro x hx
    change ‖F x‖ ≤ speed
    dsimp only [speed]
    calc
      ‖F x‖ ≤ ‖F x - F x₀‖ + ‖F x₀‖ := norm_le_norm_sub_add _ _
      _ ≤ (K : ℝ) * ‖x - x₀‖ + ‖F x₀‖ := by
        gcongr
        simpa [dist_eq_norm] using
          hLip.dist_le_mul x hx x₀ (mem_closedBall_self (by positivity))
      _ ≤ (K : ℝ) * R + ‖F x₀‖ := by
        gcongr
        have hxR : ‖x - x₀‖ ≤ R / 2 := by
          have hxdist := mem_closedBall.mp hx
          change dist x x₀ ≤ R / 2 at hxdist
          simpa only [dist_eq_norm] using hxdist
        linarith
      _ ≤ (K : ℝ) * R + ‖F x₀‖ + 1 := le_add_of_nonneg_right zero_le_one
  have hpl : IsPicardLindelof (fun _ : ℝ ↦ F)
      (tmin := -epsilon) (tmax := epsilon)
      ⟨0, by simp [hepsilon.le]⟩ x₀ tube initial speedNN K := by
    apply IsPicardLindelof.of_time_independent hnorm hLip
    simp only [sub_zero, zero_sub, neg_neg, max_self]
    change speed * epsilon ≤ R / 2 - (R / 2) / 2
    apply le_of_eq
    dsimp only [epsilon]
    field_simp [ne_of_gt hspeed]
    ring
  rcases hpl.exists_controlled_continuous_selector with
    ⟨alpha, halpha, hcontinuous⟩
  let H : LocalRegularControlledContinuousAutonomousSelector F x₀ :=
    { epsilon := epsilon
      epsilon_pos := hepsilon
      tubeRadius := tube
      initialRadius := initial
      speedBound := speedNN
      lipschitzConstant := K
      initialRadius_pos := hinitial
      selector := alpha
      field_lipschitzOn := hLip
      selector_data := by
        intro x hx
        simpa only [zero_sub, zero_add] using halpha x hx
      selector_continuousOn := by
        simpa only [zero_sub, zero_add] using hcontinuous
      initialRadius_lt_tubeRadius := hinitial_lt
      field_norm_le := hnorm
      speed_time_le_margin := by
        simpa only [sub_zero, zero_sub, neg_neg, max_self] using hpl.mul_max_le
      field_contDiffAt_one := fun x hx ↦ (htube_to_good hx).1.2 }
  refine ⟨H, ?_⟩
  intro x hx
  exact (htube_to_good ((mem_closedBall.mp hx).trans
    H.protectedInnerRadius_lt_tubeRadius.le)).2

/-- Every local `C¹` field has a selector whose invariant tube remains
inside one neighborhood of `C¹` regularity and whose initial ball has a
strict positive margin inside that tube. -/
theorem exists_localRegularControlledContinuousAutonomousSelector_of_contDiffAt_one
    (F : X → X) (x₀ : X) (hF : ContDiffAt ℝ 1 F x₀) :
    Nonempty (LocalRegularControlledContinuousAutonomousSelector F x₀) := by
  obtain ⟨H, -⟩ :=
    exists_localRegularControlledContinuousAutonomousSelector_of_contDiffAt_one_with_protectedInnerBall_subset
      F x₀ hF (U := Set.univ) univ_mem
  exact ⟨H⟩

end RegularSelector

end Poincare
