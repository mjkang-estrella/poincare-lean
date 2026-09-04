import Poincare.Global.CartanFixedChartGenericInverseEndpointODEPositiveTimeOverlapReduction

/-!
# Automatic initial overlap and the remaining positive-time tail

After fixed-cutoff subordination, the selector starts in the combined open
chart/cutoff good locus.  Its ODE derivative makes the selector position
continuous at time zero.  Therefore one positive initial interval remains in
that good locus automatically.

This file first chooses such an interval, bounded above by the fixed package
time, and isolates the four honest overlap residuals on the complementary
tail.  It then proves a connected ODE-continuation theorem: fixed source-chart
protection and the preferred trajectory's retained domains force the moving
chart and cutoff residuals automatically.  No endpoint equality is assumed.
-/

noncomputable section

set_option maxHeartbeats 1400000
set_option synthInstance.maxHeartbeats 200000

open Filter Function Metric Set
open scoped Manifold ContDiff Topology RealInnerProductSpace NNReal

namespace Poincare
namespace CartanSourceExponentialLocalFamilyTransport
namespace FixedChartAnchorEndpointPackage

universe u

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace E M]
variable [IsManifold I ∞ M]

variable {g : ClosedSmoothRiemannianMetric 3 M} {x₀ : M}

open CartanSourceExponential
open CartanGenericSuccessorDataMovingPersistenceReduction

/-! ## Domain data independent of path overlap -/

/-- The three genuine selector/public-flow domain conditions, separated from
all chart and cutoff path-retention conditions. -/
structure GenericInverseEndpointODEAdmissibilityData
    (C : FixedChartAnchorEndpointPackage g x₀)
    (x : M) (w : E)
    (P : GeodesicTransport.PreferredChartExpAtTrajectoryPackage g x) : Prop where
  selectorInitial_mem :
    (extChartAt I x₀ x, C.time⁻¹ • w) ∈
      closedBall (extChartAt I x₀ x₀, (0 : E))
        (C.selector.projectFirstVariational.initialRadius : ℝ)
  preferredTime_le : C.time ≤ P.time
  preferredVelocity_small :
    ‖C.time⁻¹ • fixedToAnchorVelocity x₀ (x, w)‖ <
      P.velocityRadius

namespace GenericInverseEndpointODEAdmissibilityData

/-- The source selector starts at the requested normalized state. -/
theorem selectorInitial
    {C : FixedChartAnchorEndpointPackage g x₀}
    {x : M} {w : E}
    {P : GeodesicTransport.PreferredChartExpAtTrajectoryPackage g x}
    (data : C.GenericInverseEndpointODEAdmissibilityData x w P) :
    C.normalizedSelectorTrajectory x w 0 =
      (extChartAt I x₀ x, C.time⁻¹ • w) := by
  simpa [normalizedSelectorTrajectory] using
    (C.selector.projectFirstVariational.selector_data
      (extChartAt I x₀ x, C.time⁻¹ • w)
      data.selectorInitial_mem).1

/-- The selector position is continuous at zero using only its retained
initial-domain membership. -/
theorem normalizedSelectorPosition_continuousAt_zero
    {C : FixedChartAnchorEndpointPackage g x₀}
    {x : M} {w : E}
    {P : GeodesicTransport.PreferredChartExpAtTrajectoryPackage g x}
    (data : C.GenericInverseEndpointODEAdmissibilityData x w P) :
    ContinuousAt
      (fun t : ℝ => (C.normalizedSelectorTrajectory x w t).1) 0 := by
  let B := C.selector.projectFirstVariational
  have hselector := B.selector_data
    (extChartAt I x₀ x, C.time⁻¹ • w) data.selectorInitial_mem
  have hzero : (0 : ℝ) ∈ Icc (-B.epsilon) B.epsilon := by
    constructor <;> linarith [B.epsilon_pos]
  have hinterior : Icc (-B.epsilon) B.epsilon ∈ nhds (0 : ℝ) :=
    Icc_mem_nhds (by linarith [B.epsilon_pos]) B.epsilon_pos
  have hstate : ContinuousAt (C.normalizedSelectorTrajectory x w) 0 := by
    simpa [normalizedSelectorTrajectory] using
      ((hselector.2.1 0 hzero).hasDerivAt hinterior).continuousAt
  exact hstate.fst

end GenericInverseEndpointODEAdmissibilityData

/-- Reparameterizing a preferred package to the fixed comparison time makes
the time inequality tautological.  The remaining preferred-flow condition is
the invariant product of its original time and velocity radii. -/
theorem nonempty_reparameterized_admissibility_of_velocity_budget
    (C : FixedChartAnchorEndpointPackage g x₀)
    (x : M) (w : E)
    (P : GeodesicTransport.PreferredChartExpAtTrajectoryPackage g x)
    (hselector :
      (extChartAt I x₀ x, C.time⁻¹ • w) ∈
        closedBall (extChartAt I x₀ x₀, (0 : E))
          (C.selector.projectFirstVariational.initialRadius : ℝ))
    (hbudget :
      ‖fixedToAnchorVelocity x₀ (x, w)‖ <
        P.time * P.velocityRadius) :
    ∃ Q : GeodesicTransport.PreferredChartExpAtTrajectoryPackage g x,
      Q.time = C.time ∧
        Nonempty (GenericInverseEndpointODEAdmissibilityData C x w Q) := by
  let Q := P.reparameterize C.time C.time_pos
  refine ⟨Q, rfl, ⟨{
    selectorInitial_mem := hselector
    preferredTime_le := le_rfl
    preferredVelocity_small := ?_ }⟩⟩
  change
    ‖C.time⁻¹ • fixedToAnchorVelocity x₀ (x, w)‖ <
      (P.time / C.time) * P.velocityRadius
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr C.time_pos)]
  calc
    C.time⁻¹ * ‖fixedToAnchorVelocity x₀ (x, w)‖
        < C.time⁻¹ * (P.time * P.velocityRadius) :=
      mul_lt_mul_of_pos_left hbudget (inv_pos.mpr C.time_pos)
    _ = (P.time / C.time) * P.velocityRadius := by
      field_simp [ne_of_gt C.time_pos]

/-! ## Automatic initial good interval -/

/-- At time zero the cutoff-subordinated selector lies in the full combined
chart/cutoff good locus. -/
theorem normalizedSelectorPosition_zero_mem_goodLocus
    (C : FixedChartAnchorEndpointPackage g x₀)
    {x : M} {w : E}
    {P : GeodesicTransport.PreferredChartExpAtTrajectoryPackage g x}
    (hx : x ∈ C.restrictToFixedAnchorCutoffOne.rawLocalFamily.anchors)
    (data : GenericInverseEndpointODEAdmissibilityData
      C.restrictToFixedAnchorCutoffOne x w P) :
    (C.restrictToFixedAnchorCutoffOne.normalizedSelectorTrajectory x w 0).1 ∈
      chartTransitionCutoffGoodLocus x₀ x := by
  have hzero := data.selectorInitial
  have hsource : extChartAt I x₀ x ∈ (extChartAt I x₀).target :=
    (extChartAt I x₀).map_source hx.1
  have htarget : (extChartAt I x₀).symm (extChartAt I x₀ x) ∈
      (extChartAt I x).source := by
    rw [(extChartAt I x₀).left_inv hx.1]
    exact mem_extChartAt_source x
  have hsourceCut : extChartAt I x₀ x ∈
      IsometryInstantiate.cutoffOneLocus x₀ :=
    C.restrictToFixedAnchorCutoffOne_anchor_mem_cutoffOneLocus hx
  have htargetCut : GeodesicTransport.chartTransition x₀ x
      (extChartAt I x₀ x) ∈
      IsometryInstantiate.cutoffOneLocus x := by
    have hanchor : extChartAt I x x ∈
        IsometryInstantiate.cutoffOneLocus x :=
      mem_of_mem_nhds
        (IsometryInstantiate.cutoffOneLocus_mem_nhds_anchor x)
    change extChartAt I x
        ((extChartAt I x₀).symm (extChartAt I x₀ x)) ∈
      IsometryInstantiate.cutoffOneLocus x
    rw [(extChartAt I x₀).left_inv hx.1]
    exact hanchor
  rw [hzero]
  exact ⟨⟨⟨hsource, htarget⟩, hsourceCut⟩, htargetCut⟩

/-- Continuity and openness provide a positive initial interval in the full
good locus.  Taking a minimum with `C.time` makes coverage compatible with
the complete comparison interval even when the continuity radius is larger. -/
theorem exists_initialOverlapTime
    (C : FixedChartAnchorEndpointPackage g x₀)
    {x : M} {w : E}
    {P : GeodesicTransport.PreferredChartExpAtTrajectoryPackage g x}
    (hx : x ∈ C.restrictToFixedAnchorCutoffOne.rawLocalFamily.anchors)
    (data : GenericInverseEndpointODEAdmissibilityData
      C.restrictToFixedAnchorCutoffOne x w P) :
    ∃ δ > (0 : ℝ), δ ≤ C.time ∧
      ∀ t ∈ Icc (0 : ℝ) δ,
        (C.restrictToFixedAnchorCutoffOne.normalizedSelectorTrajectory x w t).1 ∈
          chartTransitionCutoffGoodLocus x₀ x := by
  let γ : ℝ → E := fun t =>
    (C.restrictToFixedAnchorCutoffOne.normalizedSelectorTrajectory x w t).1
  have hcontinuous : ContinuousAt γ 0 := by
    simpa [γ] using data.normalizedSelectorPosition_continuousAt_zero
  have hzero : γ 0 ∈ chartTransitionCutoffGoodLocus x₀ x := by
    simpa [γ] using C.normalizedSelectorPosition_zero_mem_goodLocus hx data
  have hpreimage : γ ⁻¹' chartTransitionCutoffGoodLocus x₀ x ∈ nhds 0 :=
    hcontinuous.preimage_mem_nhds
      ((isOpen_chartTransitionCutoffGoodLocus x₀ x).mem_nhds hzero)
  rcases Metric.mem_nhds_iff.mp hpreimage with ⟨r, hr, hrsub⟩
  let δ : ℝ := min C.time (r / 2)
  have hδ : 0 < δ := by
    dsimp [δ]
    exact lt_min C.time_pos (half_pos hr)
  have hδtime : δ ≤ C.time := by
    dsimp [δ]
    exact min_le_left _ _
  refine ⟨δ, hδ, hδtime, ?_⟩
  intro t ht
  apply hrsub
  rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg ht.1]
  have htHalf : t ≤ r / 2 :=
    ht.2.trans (by dsimp [δ]; exact min_le_right _ _)
  exact htHalf.trans_lt (half_lt_self hr)

/-- A canonical positive initial overlap time selected from the existence
theorem. -/
noncomputable def initialOverlapTime
    (C : FixedChartAnchorEndpointPackage g x₀)
    {x : M} {w : E}
    {P : GeodesicTransport.PreferredChartExpAtTrajectoryPackage g x}
    (hx : x ∈ C.restrictToFixedAnchorCutoffOne.rawLocalFamily.anchors)
    (data : GenericInverseEndpointODEAdmissibilityData
      C.restrictToFixedAnchorCutoffOne x w P) : ℝ :=
  Classical.choose (C.exists_initialOverlapTime hx data)

theorem initialOverlapTime_pos
    (C : FixedChartAnchorEndpointPackage g x₀)
    {x : M} {w : E}
    {P : GeodesicTransport.PreferredChartExpAtTrajectoryPackage g x}
    (hx : x ∈ C.restrictToFixedAnchorCutoffOne.rawLocalFamily.anchors)
    (data : GenericInverseEndpointODEAdmissibilityData
      C.restrictToFixedAnchorCutoffOne x w P) :
    0 < C.initialOverlapTime hx data :=
  (Classical.choose_spec (C.exists_initialOverlapTime hx data)).1

theorem initialOverlapTime_le_time
    (C : FixedChartAnchorEndpointPackage g x₀)
    {x : M} {w : E}
    {P : GeodesicTransport.PreferredChartExpAtTrajectoryPackage g x}
    (hx : x ∈ C.restrictToFixedAnchorCutoffOne.rawLocalFamily.anchors)
    (data : GenericInverseEndpointODEAdmissibilityData
      C.restrictToFixedAnchorCutoffOne x w P) :
    C.initialOverlapTime hx data ≤ C.time :=
  (Classical.choose_spec (C.exists_initialOverlapTime hx data)).2.1

theorem initialOverlapTime_mem_goodLocus
    (C : FixedChartAnchorEndpointPackage g x₀)
    {x : M} {w : E}
    {P : GeodesicTransport.PreferredChartExpAtTrajectoryPackage g x}
    (hx : x ∈ C.restrictToFixedAnchorCutoffOne.rawLocalFamily.anchors)
    (data : GenericInverseEndpointODEAdmissibilityData
      C.restrictToFixedAnchorCutoffOne x w P) :
    ∀ t ∈ Icc (0 : ℝ) (C.initialOverlapTime hx data),
      (C.restrictToFixedAnchorCutoffOne.normalizedSelectorTrajectory x w t).1 ∈
        chartTransitionCutoffGoodLocus x₀ x :=
  (Classical.choose_spec (C.exists_initialOverlapTime hx data)).2.2

/-- On the remaining tail, the complete selector state stays in the protected
inner ball supplied by the regular controlled selector.  This is the strongest
range control available from admissibility alone; no chart or cutoff
membership is used. -/
theorem normalizedSelectorTrajectory_mem_protectedInnerBall_on_tail
    (C : FixedChartAnchorEndpointPackage g x₀)
    {x : M} {w : E}
    {P : GeodesicTransport.PreferredChartExpAtTrajectoryPackage g x}
    (hx : x ∈ C.restrictToFixedAnchorCutoffOne.rawLocalFamily.anchors)
    (data : GenericInverseEndpointODEAdmissibilityData
      C.restrictToFixedAnchorCutoffOne x w P) :
    ∀ t ∈ Ioc (C.initialOverlapTime hx data) C.time,
      C.restrictToFixedAnchorCutoffOne.normalizedSelectorTrajectory x w t ∈
        closedBall (extChartAt I x₀ x₀, (0 : E))
          C.restrictToFixedAnchorCutoffOne.selector.projectFirstVariational.protectedInnerRadius := by
  intro t ht
  let B := C.restrictToFixedAnchorCutoffOne.selector.projectFirstVariational
  have hhalf : t ∈ Icc (-(B.epsilon / 2)) (B.epsilon / 2) := by
    have hneg : -(B.epsilon / 2) ≤ 0 := by
      linarith [B.epsilon_pos]
    have hzero : 0 ≤ t :=
      (C.initialOverlapTime_pos hx data).le.trans ht.1.le
    have hupper : C.time < B.epsilon / 2 := by
      simpa [B] using C.time_protected.2
    exact ⟨hneg.trans hzero, ht.2.trans hupper.le⟩
  simpa [B, normalizedSelectorTrajectory] using
    B.selector_mem_protectedInnerBall data.selectorInitial_mem hhalf

/-- The protected selector ball contains the complete nonnegative comparison
interval, not only the residual tail. -/
theorem normalizedSelectorTrajectory_mem_protectedInnerBall_on_Icc
    (C : FixedChartAnchorEndpointPackage g x₀)
    {x : M} {w : E}
    {P : GeodesicTransport.PreferredChartExpAtTrajectoryPackage g x}
    (data : GenericInverseEndpointODEAdmissibilityData
      C.restrictToFixedAnchorCutoffOne x w P) :
    ∀ t ∈ Icc (0 : ℝ) C.time,
      C.restrictToFixedAnchorCutoffOne.normalizedSelectorTrajectory x w t ∈
        closedBall (extChartAt I x₀ x₀, (0 : E))
          C.selector.projectFirstVariational.protectedInnerRadius := by
  intro t ht
  let B := C.restrictToFixedAnchorCutoffOne.selector.projectFirstVariational
  have hhalf : t ∈ Icc (-(B.epsilon / 2)) (B.epsilon / 2) := by
    have hneg : -(B.epsilon / 2) ≤ 0 := by
      linarith [B.epsilon_pos]
    have hupper : C.time < B.epsilon / 2 := by
      simpa [B] using C.time_protected.2
    exact ⟨hneg.trans ht.1, ht.2.trans hupper.le⟩
  simpa [B, normalizedSelectorTrajectory] using
    B.selector_mem_protectedInnerBall data.selectorInitial_mem hhalf

/-- One static containment of the selector's protected inner ball replaces
pointwise chart and cutoff membership throughout the positive-time tail. -/
theorem normalizedSelectorPosition_mem_goodLocus_on_tail
    (C : FixedChartAnchorEndpointPackage g x₀)
    {x : M} {w : E}
    {P : GeodesicTransport.PreferredChartExpAtTrajectoryPackage g x}
    (hx : x ∈ C.restrictToFixedAnchorCutoffOne.rawLocalFamily.anchors)
    (data : GenericInverseEndpointODEAdmissibilityData
      C.restrictToFixedAnchorCutoffOne x w P)
    (hprotectedInnerBall :
      ∀ q ∈ closedBall (extChartAt I x₀ x₀, (0 : E))
          C.restrictToFixedAnchorCutoffOne.selector.projectFirstVariational.protectedInnerRadius,
        q.1 ∈ chartTransitionCutoffGoodLocus x₀ x) :
    ∀ t ∈ Ioc (C.initialOverlapTime hx data) C.time,
      (C.restrictToFixedAnchorCutoffOne.normalizedSelectorTrajectory x w t).1 ∈
        chartTransitionCutoffGoodLocus x₀ x := by
  intro t ht
  exact hprotectedInnerBall _
    (C.normalizedSelectorTrajectory_mem_protectedInnerBall_on_tail
      hx data t ht)

/-! ## Exact remaining tail residual -/

/-- After the automatic initial interval, retain the same four path
membership residuals only on the remaining tail. -/
structure GenericInverseEndpointODETailOverlapData
    (C : FixedChartAnchorEndpointPackage g x₀)
    (x : M) (w : E)
    (P : GeodesicTransport.PreferredChartExpAtTrajectoryPackage g x)
    (hx : x ∈ C.restrictToFixedAnchorCutoffOne.rawLocalFamily.anchors) : Prop where
  admissibility : GenericInverseEndpointODEAdmissibilityData
    C.restrictToFixedAnchorCutoffOne x w P
  sourceChart_mem :
    ∀ t ∈ Ioc (C.initialOverlapTime hx admissibility) C.time,
      (C.restrictToFixedAnchorCutoffOne.normalizedSelectorTrajectory x w t).1 ∈
        (extChartAt I x₀).target
  targetChart_mem :
    ∀ t ∈ Ioc (C.initialOverlapTime hx admissibility) C.time,
      (extChartAt I x₀).symm
          (C.restrictToFixedAnchorCutoffOne.normalizedSelectorTrajectory x w t).1 ∈
        (extChartAt I x).source
  sourceCutoffOne_mem :
    ∀ t ∈ Ioc (C.initialOverlapTime hx admissibility) C.time,
      (C.restrictToFixedAnchorCutoffOne.normalizedSelectorTrajectory x w t).1 ∈
        IsometryInstantiate.cutoffOneLocus x₀
  targetCutoffOne_mem :
    ∀ t ∈ Ioc (C.initialOverlapTime hx admissibility) C.time,
      GeodesicTransport.chartTransition x₀ x
          (C.restrictToFixedAnchorCutoffOne.normalizedSelectorTrajectory x w t).1 ∈
        IsometryInstantiate.cutoffOneLocus x

/-- Admissibility and one geometric containment of the protected selector ball
produce the complete tail-overlap package.  The four dynamic residuals are
obtained by projecting the four conjuncts of the combined good locus. -/
theorem nonempty_genericInverseEndpointODETailOverlapData_of_protectedInnerBall
    (C : FixedChartAnchorEndpointPackage g x₀)
    {x : M} {w : E}
    {P : GeodesicTransport.PreferredChartExpAtTrajectoryPackage g x}
    (hx : x ∈ C.restrictToFixedAnchorCutoffOne.rawLocalFamily.anchors)
    (data : GenericInverseEndpointODEAdmissibilityData
      C.restrictToFixedAnchorCutoffOne x w P)
    (hprotectedInnerBall :
      ∀ q ∈ closedBall (extChartAt I x₀ x₀, (0 : E))
          C.restrictToFixedAnchorCutoffOne.selector.projectFirstVariational.protectedInnerRadius,
        q.1 ∈ chartTransitionCutoffGoodLocus x₀ x) :
    Nonempty (C.GenericInverseEndpointODETailOverlapData x w P hx) := by
  have hgood := C.normalizedSelectorPosition_mem_goodLocus_on_tail
    hx data hprotectedInnerBall
  exact ⟨{
    admissibility := data
    sourceChart_mem := by
      intro t ht
      exact (hgood t ht).1.1.1
    targetChart_mem := by
      intro t ht
      exact (hgood t ht).1.1.2
    sourceCutoffOne_mem := by
      intro t ht
      exact (hgood t ht).1.2
    targetCutoffOne_mem := by
      intro t ht
      exact (hgood t ht).2 }⟩

/-- Fixed source-chart and source-cutoff retention in the protected selector
ball discharges those two tail fields.  Only the moving target chart and cutoff
conditions remain as path-dependent premises. -/
theorem nonempty_genericInverseEndpointODETailOverlapData_of_fixedSourceChartCutoff_protectedInnerBall
    (C : FixedChartAnchorEndpointPackage g x₀)
    {x : M} {w : E}
    {P : GeodesicTransport.PreferredChartExpAtTrajectoryPackage g x}
    (hx : x ∈ C.restrictToFixedAnchorCutoffOne.rawLocalFamily.anchors)
    (data : GenericInverseEndpointODEAdmissibilityData
      C.restrictToFixedAnchorCutoffOne x w P)
    (hprotectedFixed :
      ∀ q ∈ closedBall (extChartAt I x₀ x₀, (0 : E))
          C.selector.projectFirstVariational.protectedInnerRadius,
        q.1 ∈ (extChartAt I x₀).target ∧
          q.1 ∈ IsometryInstantiate.cutoffOneLocus x₀)
    (htargetChart :
      ∀ t ∈ Ioc (C.initialOverlapTime hx data) C.time,
        (extChartAt I x₀).symm
            (C.restrictToFixedAnchorCutoffOne.normalizedSelectorTrajectory
              x w t).1 ∈
          (extChartAt I x).source)
    (htargetCutoffOne :
      ∀ t ∈ Ioc (C.initialOverlapTime hx data) C.time,
        GeodesicTransport.chartTransition x₀ x
            (C.restrictToFixedAnchorCutoffOne.normalizedSelectorTrajectory
              x w t).1 ∈
          IsometryInstantiate.cutoffOneLocus x) :
    Nonempty (C.GenericInverseEndpointODETailOverlapData x w P hx) := by
  have hfixed : ∀ t ∈ Ioc (C.initialOverlapTime hx data) C.time,
      (C.restrictToFixedAnchorCutoffOne.normalizedSelectorTrajectory x w t).1 ∈
          (extChartAt I x₀).target ∧
        (C.restrictToFixedAnchorCutoffOne.normalizedSelectorTrajectory x w t).1 ∈
          IsometryInstantiate.cutoffOneLocus x₀ := by
    intro t ht
    apply hprotectedFixed
    simpa only [restrictToFixedAnchorCutoffOne_selector] using
      C.normalizedSelectorTrajectory_mem_protectedInnerBall_on_tail
        hx data t ht
  exact ⟨{
    admissibility := data
    sourceChart_mem := fun t ht => (hfixed t ht).1
    targetChart_mem := htargetChart
    sourceCutoffOne_mem := fun t ht => (hfixed t ht).2
    targetCutoffOne_mem := htargetCutoffOne }⟩

/-! ## Continuation across the moving chart -/

/-- Equality of the two manifold readings recovers the moving-chart
membership, the coordinate transition identity, and the moving cutoff fact
from the preferred trajectory's retained domains. -/
theorem moving_memberships_of_pulledback_position_eq
    {x₀ x : M} {q z : E}
    (hzTarget : z ∈ (extChartAt I x).target)
    (hzCutoff : z ∈ IsometryInstantiate.cutoffOneLocus x)
    (hpullback : (extChartAt I x₀).symm q = (extChartAt I x).symm z) :
    (extChartAt I x₀).symm q ∈ (extChartAt I x).source ∧
      GeodesicTransport.chartTransition x₀ x q = z ∧
      GeodesicTransport.chartTransition x₀ x q ∈
        IsometryInstantiate.cutoffOneLocus x := by
  have hsource : (extChartAt I x).symm z ∈ (extChartAt I x).source :=
    (extChartAt I x).map_target hzTarget
  have htransition : GeodesicTransport.chartTransition x₀ x q = z := by
    rw [GeodesicTransport.chartTransition_apply, hpullback]
    exact (extChartAt I x).right_inv hzTarget
  exact ⟨hpullback ▸ hsource, htransition, htransition ▸ hzCutoff⟩

/-- At a point of the combined chart/cutoff good locus, the transported fixed
selector is continuous.  This local fact is what closes the continuation
locus after manifold-position equality recovers the moving memberships. -/
theorem preferredTransportedSelectorTrajectory_continuousAt_of_good
    (C : FixedChartAnchorEndpointPackage g x₀)
    {x : M} {w : E}
    {P : GeodesicTransport.PreferredChartExpAtTrajectoryPackage g x}
    (data : GenericInverseEndpointODEAdmissibilityData C x w P)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) C.time)
    (hgood : (C.normalizedSelectorTrajectory x w t).1 ∈
      chartTransitionCutoffGoodLocus x₀ x) :
    ContinuousAt (C.preferredTransportedSelectorTrajectory x w) t := by
  let B := C.selector.projectFirstVariational
  have hselector := B.selector_data
    (extChartAt I x₀ x, C.time⁻¹ • w) data.selectorInitial_mem
  have htInterior : t ∈ Ioo (-B.epsilon) B.epsilon := by
    have htimeProtected : C.time < B.epsilon / 2 := by
      simpa [B] using C.time_protected.2
    constructor
    · linarith [B.epsilon_pos, ht.1]
    · linarith [ht.2, htimeProtected, B.epsilon_pos]
  have hsource : HasDerivAt (C.normalizedSelectorTrajectory x w)
      (geodesicFlowField
        (GeodesicTransport.chartChristoffelField g x₀)
        (C.normalizedSelectorTrajectory x w t)) t := by
    simpa [normalizedSelectorTrajectory,
      CartanSourceExponentialLocalChartSelector.fixedChartGeodesicField] using
        (hselector.2.1 t (Ioo_subset_Icc_self htInterior)).hasDerivAt
          (Icc_mem_nhds htInterior.1 htInterior.2)
  have hsourceN :=
    (isOpen_extChartAt_target x₀).mem_nhds hgood.1.1.1
  have htargetN :
      {r : E | (extChartAt I x₀).symm r ∈
        (extChartAt I x).source} ∈
        nhds (C.normalizedSelectorTrajectory x w t).1 :=
    (continuousAt_extChartAt_symm'' hgood.1.1.1).preimage_mem_nhds
      ((isOpen_extChartAt_source x).mem_nhds hgood.1.1.2)
  have hsourceCut :=
    IsometryInstantiate.cutoff_eventuallyEq_one_of_mem_cutoffOneLocus
      hgood.1.2
  have htransition :=
    GeodesicTransport.chartTransition_hasFDerivAt_chartTransitionMFDeriv
      x₀ x hgood.1.1.1 hgood.1.1.2
  have htargetCut := htransition.continuousAt.preimage_mem_nhds
    (IsometryInstantiate.cutoff_eventuallyEq_one_of_mem_cutoffOneLocus hgood.2)
  have htransported :
      HasDerivAt (C.preferredTransportedSelectorTrajectory x w)
        (geodesicFlowField
          (GeodesicTransport.chartChristoffelField g x)
          (C.preferredTransportedSelectorTrajectory x w t)) t := by
    simpa [preferredTransportedSelectorTrajectory] using
      GeodesicTransport.chartTransitionState_hasDerivAt_of_cutoff_eq_one_nhds
        g x₀ x hsource hsourceN htargetN hsourceCut htargetCut
  exact htransported.continuousAt

/-- At a strict pre-endpoint time, membership in the combined good set and
state equality propagate equality of the transported fixed selector and the
preferred trajectory to a full neighborhood. -/
theorem preferredTransportedSelectorTrajectory_eventuallyEq_of_good_and_eq
    (C : FixedChartAnchorEndpointPackage g x₀)
    {x : M} {w : E}
    {P : GeodesicTransport.PreferredChartExpAtTrajectoryPackage g x}
    (data : GenericInverseEndpointODEAdmissibilityData C x w P)
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) C.time)
    (hgood : ∀ᶠ s in nhds t,
      (C.normalizedSelectorTrajectory x w s).1 ∈
        chartTransitionCutoffGoodLocus x₀ x)
    (heq : C.preferredTransportedSelectorTrajectory x w t =
      C.preferredExpAtTrajectory P w t) :
    C.preferredTransportedSelectorTrajectory x w =ᶠ[nhds t]
      C.preferredExpAtTrajectory P w := by
  let B := C.selector.projectFirstVariational
  let q : ℝ → E × E := C.normalizedSelectorTrajectory x w
  let μ : ℝ → E × E := C.preferredTransportedSelectorTrajectory x w
  let η : ℝ → E × E := C.preferredExpAtTrajectory P w
  let F : E × E → E × E :=
    geodesicFlowField
      (GeodesicTransport.chartChristoffelField g x)
  have hselector := B.selector_data
    (extChartAt I x₀ x, C.time⁻¹ • w) data.selectorInitial_mem
  have htUpper : t < B.epsilon := by
    have htimeProtected : C.time < B.epsilon / 2 := by
      simpa [B] using C.time_protected.2
    linarith [ht.2, B.epsilon_pos]
  have htLower : -B.epsilon < t := by
    linarith [ht.1, B.epsilon_pos]
  have hselectorInterval : Ioo (-B.epsilon) B.epsilon ∈ nhds t :=
    Ioo_mem_nhds htLower htUpper
  have hqder : ∀ᶠ s in nhds t,
      HasDerivAt q
        (geodesicFlowField
          (GeodesicTransport.chartChristoffelField g x₀) (q s)) s := by
    filter_upwards [hselectorInterval] with s hs
    simpa [q, B, normalizedSelectorTrajectory,
      CartanSourceExponentialLocalChartSelector.fixedChartGeodesicField] using
        (hselector.2.1 s (Ioo_subset_Icc_self hs)).hasDerivAt
          (Icc_mem_nhds hs.1 hs.2)
  have hμder : ∀ᶠ s in nhds t,
      HasDerivAt μ (F (μ s)) s := by
    filter_upwards [hqder, hgood] with s hqs hgs
    have hsourceN :=
      (isOpen_extChartAt_target x₀).mem_nhds hgs.1.1.1
    have htargetN :
        {r : E | (extChartAt I x₀).symm r ∈
          (extChartAt I x).source} ∈ nhds (q s).1 :=
      (continuousAt_extChartAt_symm'' hgs.1.1.1).preimage_mem_nhds
        ((isOpen_extChartAt_source x).mem_nhds hgs.1.1.2)
    have hsourceCut :=
      IsometryInstantiate.cutoff_eventuallyEq_one_of_mem_cutoffOneLocus
        hgs.1.2
    have htransition :=
      GeodesicTransport.chartTransition_hasFDerivAt_chartTransitionMFDeriv
        x₀ x hgs.1.1.1 hgs.1.1.2
    have htargetCut := htransition.continuousAt.preimage_mem_nhds
      (IsometryInstantiate.cutoff_eventuallyEq_one_of_mem_cutoffOneLocus hgs.2)
    simpa [μ, q, F, preferredTransportedSelectorTrajectory] using
      GeodesicTransport.chartTransitionState_hasDerivAt_of_cutoff_eq_one_nhds
        g x₀ x hqs hsourceN htargetN hsourceCut htargetCut
  let v : E := C.time⁻¹ • fixedToAnchorVelocity x₀ (x, w)
  have htPreferredUpper : t < P.time :=
    ht.2.trans_le data.preferredTime_le
  have htPreferredLower : -P.time < t := by
    linarith [P.time_pos, ht.1]
  have hpreferredInterval : Ioo (-P.time) P.time ∈ nhds t :=
    Ioo_mem_nhds htPreferredLower htPreferredUpper
  have hηder : ∀ᶠ s in nhds t, HasDerivAt η (F (η s)) s := by
    filter_upwards [hpreferredInterval] with s hs
    simpa [η, F, preferredExpAtTrajectory, v] using
      (P.derivative v data.preferredVelocity_small s
        (Ioo_subset_Icc_self hs)).hasDerivAt
          (Icc_mem_nhds hs.1 hs.2)
  let p : E × E := μ t
  rcases
      GeodesicTransport.geodesicFlowField_chartChristoffelField_lipschitzOn_closedBall
        g x p 1 with ⟨K, hK⟩
  have hμcont : ContinuousAt μ t :=
    (hμder.self_of_nhds).continuousAt
  have hηcont : ContinuousAt η t :=
    (hηder.self_of_nhds).continuousAt
  have hμmem : ∀ᶠ s in nhds t, μ s ∈ closedBall p 1 :=
    hμcont.preimage_mem_nhds (Metric.closedBall_mem_nhds p zero_lt_one)
  have hηmem : ∀ᶠ s in nhds t, η s ∈ closedBall p 1 := by
    have hpref : η t = p := by simpa [p, μ, η] using heq.symm
    exact hηcont.preimage_mem_nhds (by
      simpa [hpref] using Metric.closedBall_mem_nhds (η t) zero_lt_one)
  have hresult : μ =ᶠ[nhds t] η :=
    ODE_solution_unique_of_eventually
      (v := fun _ : ℝ => F)
      (s := fun _ : ℝ => closedBall p 1)
      (K := K)
      (.of_forall fun _ => by simpa [F] using hK)
      (hμder.and hμmem)
      (hηder.and hηmem)
      (by simpa [μ, η] using heq)
  simpa [μ, η] using hresult

/-- Fixed-chart protection and the preferred trajectory's retained target
domains force the two manifold position readings to agree on the complete
comparison interval.  The proof continues the locus carrying both manifold
position equality and target-chart state equality across the connected
half-open interval, then takes the endpoint limit. -/
theorem pulledbackPosition_eqOn_Icc_of_fixedSourceChartCutoff_protectedInnerBall
    (C : FixedChartAnchorEndpointPackage g x₀)
    {x : M} {w : E}
    {P : GeodesicTransport.PreferredChartExpAtTrajectoryPackage g x}
    (hx : x ∈ C.restrictToFixedAnchorCutoffOne.rawLocalFamily.anchors)
    (data : GenericInverseEndpointODEAdmissibilityData
      C.restrictToFixedAnchorCutoffOne x w P)
    (hprotectedFixed :
      ∀ q ∈ closedBall (extChartAt I x₀ x₀, (0 : E))
          C.selector.projectFirstVariational.protectedInnerRadius,
        q.1 ∈ (extChartAt I x₀).target ∧
          q.1 ∈ IsometryInstantiate.cutoffOneLocus x₀) :
    ∀ t ∈ Icc (0 : ℝ) C.time,
      (extChartAt I x₀).symm
          (C.restrictToFixedAnchorCutoffOne.normalizedSelectorTrajectory
            x w t).1 =
        (extChartAt I x).symm
          (C.restrictToFixedAnchorCutoffOne.preferredExpAtTrajectory
            P w t).1 := by
  let D := C.restrictToFixedAnchorCutoffOne
  let q : ℝ → E × E := D.normalizedSelectorTrajectory x w
  let μ : ℝ → E × E := D.preferredTransportedSelectorTrajectory x w
  let η : ℝ → E × E := D.preferredExpAtTrajectory P w
  let φ : ℝ → M := fun t => (extChartAt I x₀).symm (q t).1
  let ψ : ℝ → M := fun t => (extChartAt I x).symm (η t).1
  let v : E := D.time⁻¹ • fixedToAnchorVelocity x₀ (x, w)
  let B := D.selector.projectFirstVariational
  have hselector := B.selector_data
    (extChartAt I x₀ x, D.time⁻¹ • w) data.selectorInitial_mem
  have hqContinuousAt : ∀ t ∈ Icc (0 : ℝ) C.time,
      ContinuousAt q t := by
    intro t ht
    have htInterior : t ∈ Ioo (-B.epsilon) B.epsilon := by
      have htimeProtected : C.time < B.epsilon / 2 := by
        simpa [B, D] using C.time_protected.2
      constructor
      · linarith [B.epsilon_pos, ht.1]
      · linarith [ht.2, htimeProtected, B.epsilon_pos]
    have hder : HasDerivAt q
        (geodesicFlowField
          (GeodesicTransport.chartChristoffelField g x₀) (q t)) t := by
      simpa [q, B, normalizedSelectorTrajectory,
        CartanSourceExponentialLocalChartSelector.fixedChartGeodesicField] using
          (hselector.2.1 t (Ioo_subset_Icc_self htInterior)).hasDerivAt
            (Icc_mem_nhds htInterior.1 htInterior.2)
    exact hder.continuousAt
  have hqContinuousOn : ContinuousOn q (Icc (0 : ℝ) C.time) :=
    fun t ht => (hqContinuousAt t ht).continuousWithinAt
  have hintervalPreferred : Icc (0 : ℝ) C.time ⊆ Icc (-P.time) P.time := by
    intro t ht
    exact ⟨by linarith [P.time_pos, ht.1], ht.2.trans data.preferredTime_le⟩
  have hηContinuousOn : ContinuousOn η (Icc (0 : ℝ) C.time) := by
    intro t ht
    have hder := P.derivative v data.preferredVelocity_small t
      (hintervalPreferred ht)
    exact (hder.mono hintervalPreferred).continuousWithinAt
  have hqFixed : ∀ t ∈ Icc (0 : ℝ) C.time,
      (q t).1 ∈ (extChartAt I x₀).target ∧
        (q t).1 ∈ IsometryInstantiate.cutoffOneLocus x₀ := by
    intro t ht
    apply hprotectedFixed
    simpa [q, D] using
      C.normalizedSelectorTrajectory_mem_protectedInnerBall_on_Icc data t ht
  have hηPreferred : ∀ t ∈ Icc (0 : ℝ) C.time,
      (η t).1 ∈ (extChartAt I x).target ∧
        (η t).1 ∈ IsometryInstantiate.cutoffOneLocus x := by
    intro t ht
    exact ⟨P.position_mem_target v data.preferredVelocity_small t
        (hintervalPreferred ht),
      P.position_mem_cutoffOne v data.preferredVelocity_small t
        (hintervalPreferred ht)⟩
  have hφContinuousOn : ContinuousOn φ (Icc (0 : ℝ) C.time) := by
    exact (continuousOn_extChartAt_symm x₀).comp hqContinuousOn.fst
      (fun t ht => (hqFixed t ht).1)
  have hψContinuousOn : ContinuousOn ψ (Icc (0 : ℝ) C.time) := by
    exact (continuousOn_extChartAt_symm x).comp hηContinuousOn.fst
      (fun t ht => (hηPreferred t ht).1)
  let J := {t : ℝ // t ∈ Ico (0 : ℝ) C.time}
  let φJ : J → M := fun t => φ t
  let ψJ : J → M := fun t => ψ t
  let μJ : J → E × E := fun t => μ t
  let ηJ : J → E × E := fun t => η t
  let continuationLocus : Set J :=
    {t | φJ t = ψJ t ∧ μJ t = ηJ t}
  have hφJContinuous : Continuous φJ := by
    simpa [φJ, J] using
      (hφContinuousOn.mono Ico_subset_Icc_self).restrict
  have hψJContinuous : Continuous ψJ := by
    simpa [ψJ, J] using
      (hψContinuousOn.mono Ico_subset_Icc_self).restrict
  have hηJContinuous : Continuous ηJ := by
    change Continuous ((Ico (0 : ℝ) C.time).restrict η)
    exact (hηContinuousOn.mono Ico_subset_Icc_self).restrict
  have hgood_of_pullback : ∀ t : J, φJ t = ψJ t →
      (q t).1 ∈ chartTransitionCutoffGoodLocus x₀ x := by
    intro t hpullback
    have htIcc : (t : ℝ) ∈ Icc (0 : ℝ) C.time :=
      Ico_subset_Icc_self t.property
    have hmoving := moving_memberships_of_pulledback_position_eq
      (hηPreferred t htIcc).1 (hηPreferred t htIcc).2
      (by simpa [φJ, ψJ, φ, ψ] using hpullback)
    exact ⟨⟨⟨(hqFixed t htIcc).1, hmoving.1⟩,
      (hqFixed t htIcc).2⟩, hmoving.2.2⟩
  have hqJContinuous : Continuous (fun t : J => q t) := by
    change Continuous ((Ico (0 : ℝ) C.time).restrict q)
    exact (hqContinuousOn.mono Ico_subset_Icc_self).restrict
  have hcontinuationClosed : IsClosed continuationLocus := by
    rw [isClosed_iff_forall_filter]
    intro t F hF hFlocus hFt
    have hlocus : ∀ᶠ s in F, s ∈ continuationLocus :=
      hFlocus (by simp)
    have hpullbackEventually : φJ =ᶠ[F] ψJ :=
      hlocus.mono (fun s hs => hs.1)
    have hpullback : φJ t = ψJ t :=
      tendsto_nhds_unique_of_eventuallyEq
        (hφJContinuous.continuousAt.tendsto.mono_left hFt)
        (hψJContinuous.continuousAt.tendsto.mono_left hFt)
        hpullbackEventually
    have hgood := hgood_of_pullback t hpullback
    have htIcc : (t : ℝ) ∈ Icc (0 : ℝ) C.time :=
      Ico_subset_Icc_self t.property
    have hμContinuousAtReal : ContinuousAt μ t := by
      simpa [μ, D] using
        D.preferredTransportedSelectorTrajectory_continuousAt_of_good
          data htIcc hgood
    have hμJContinuousAt : ContinuousAt μJ t := by
      simpa [μJ] using hμContinuousAtReal.comp
        continuous_subtype_val.continuousAt
    have hstateEventually : μJ =ᶠ[F] ηJ :=
      hlocus.mono (fun s hs => hs.2)
    have hstate : μJ t = ηJ t :=
      tendsto_nhds_unique_of_eventuallyEq
        (hμJContinuousAt.tendsto.mono_left hFt)
        (hηJContinuous.continuousAt.tendsto.mono_left hFt)
        hstateEventually
    exact ⟨hpullback, hstate⟩
  have hcontinuationOpen : IsOpen continuationLocus := by
    rw [isOpen_iff_mem_nhds]
    intro t ht
    have hgood := hgood_of_pullback t ht.1
    have hqPositionContinuousAt :
        ContinuousAt (fun s : ℝ => (q s).1) t := by
      have htIcc : (t : ℝ) ∈ Icc (0 : ℝ) C.time :=
        Ico_subset_Icc_self t.property
      exact (hqContinuousAt t htIcc).fst
    have hgoodEventually : ∀ᶠ s in nhds (t : ℝ),
        (q s).1 ∈ chartTransitionCutoffGoodLocus x₀ x :=
      hqPositionContinuousAt.preimage_mem_nhds
        ((isOpen_chartTransitionCutoffGoodLocus x₀ x).mem_nhds hgood)
    have hstateEventually : μ =ᶠ[nhds (t : ℝ)] η := by
      simpa [μ, η, q, D] using
        D.preferredTransportedSelectorTrajectory_eventuallyEq_of_good_and_eq
          data t.property hgoodEventually (by simpa [μJ, ηJ] using ht.2)
    have hlocusReal : ∀ᶠ s in nhds (t : ℝ),
        φ s = ψ s ∧ μ s = η s := by
      filter_upwards [hgoodEventually, hstateEventually] with s hgs hse
      have hpull : φ s = ψ s := by
        have hfirst := congrArg Prod.fst hse
        have htarget : (extChartAt I x₀).symm (q s).1 ∈
            (extChartAt I x).source := hgs.1.1.2
        calc
          φ s = (extChartAt I x).symm
              (GeodesicTransport.chartTransition x₀ x (q s).1) := by
            simpa [φ, GeodesicTransport.chartTransition_apply] using
              ((extChartAt I x).left_inv htarget).symm
          _ = ψ s := by
            simpa [μ, η, ψ, preferredTransportedSelectorTrajectory] using
              congrArg (extChartAt I x).symm hfirst
      exact ⟨hpull, hse⟩
    have hlocusJ : ∀ᶠ s in nhds t, s ∈ continuationLocus := by
      have hcomp :=
        (show (fun s : ℝ => (φ s, μ s)) =ᶠ[nhds (t : ℝ)]
            (fun s : ℝ => (ψ s, η s)) from
          hlocusReal.mono (fun s hs => Prod.ext hs.1 hs.2)).comp_tendsto
            continuous_subtype_val.continuousAt
      exact hcomp.mono (fun s hs => by
        exact ⟨congrArg Prod.fst hs, congrArg Prod.snd hs⟩)
    exact hlocusJ
  letI : PreconnectedSpace J :=
    Subtype.preconnectedSpace (isPreconnected_Ico :
      IsPreconnected (Ico (0 : ℝ) C.time))
  have hzeroJ : (0 : ℝ) ∈ Ico (0 : ℝ) C.time :=
    ⟨le_rfl, C.time_pos⟩
  let tzero : J := ⟨0, hzeroJ⟩
  have hzeroPullback : φJ tzero = ψJ tzero := by
    have hselectorInitial := data.selectorInitial
    have hpreferredInitial := P.initial v data.preferredVelocity_small
    have hxSource : x ∈ (extChartAt I x₀).source := hx.1
    change (extChartAt I x₀).symm (q 0).1 =
      (extChartAt I x).symm (η 0).1
    rw [show q 0 = (extChartAt I x₀ x, D.time⁻¹ • w) by
      simpa [q] using hselectorInitial]
    rw [show η 0 = (extChartAt I x x, v) by
      simpa [η, v, preferredExpAtTrajectory] using hpreferredInitial]
    rw [(extChartAt I x₀).left_inv hxSource,
      (extChartAt I x).left_inv (mem_extChartAt_source x)]
  have hzeroState : μJ tzero = ηJ tzero := by
    have hselectorInitial := data.selectorInitial
    have htransported :=
      D.preferredTransportedSelectorTrajectory_zero_of_selectorInitial
        hx hselectorInitial
    have hpreferredInitial := P.initial v data.preferredVelocity_small
    simpa [μJ, ηJ, μ, η, v, preferredExpAtTrajectory] using
      htransported.trans hpreferredInitial.symm
  have hcontinuationNonempty : continuationLocus.Nonempty :=
    ⟨tzero, hzeroPullback, hzeroState⟩
  have hcontinuationAll : continuationLocus = Set.univ :=
    IsClopen.eq_univ ⟨hcontinuationClosed, hcontinuationOpen⟩
      hcontinuationNonempty
  have hpullbackIco : EqOn φ ψ (Ico (0 : ℝ) C.time) := by
    intro t ht
    have hmem : (⟨t, ht⟩ : J) ∈ continuationLocus := by
      rw [hcontinuationAll]
      exact Set.mem_univ _
    exact hmem.1
  intro t ht
  haveI : NeBot (nhdsWithin t (Ico (0 : ℝ) C.time)) :=
    mem_closure_iff_nhdsWithin_neBot.mp (by
      rw [closure_Ico (ne_of_lt C.time_pos)]
      exact ht)
  have hφt : Tendsto φ (nhdsWithin t (Ico (0 : ℝ) C.time)) (nhds (φ t)) :=
    (hφContinuousOn t ht).tendsto.mono_left
      (nhdsWithin_mono t Ico_subset_Icc_self)
  have hψt : Tendsto ψ (nhdsWithin t (Ico (0 : ℝ) C.time)) (nhds (ψ t)) :=
    (hψContinuousOn t ht).tendsto.mono_left
      (nhdsWithin_mono t Ico_subset_Icc_self)
  have heventual : φ =ᶠ[nhdsWithin t (Ico (0 : ℝ) C.time)] ψ :=
    hpullbackIco.eventuallyEq_of_mem self_mem_nhdsWithin
  simpa [φ, ψ, q, η, D] using
    tendsto_nhds_unique_of_eventuallyEq hφt hψt heventual

/-- Admissibility and fixed-chart protection now construct the complete tail
overlap package.  The preferred PL trajectory supplies the moving chart and
cutoff domains, while connected ODE continuation identifies its manifold
position with the transported fixed selector. -/
theorem nonempty_genericInverseEndpointODETailOverlapData_of_fixedSourceChartCutoff_protectedInnerBall_automatic
    (C : FixedChartAnchorEndpointPackage g x₀)
    {x : M} {w : E}
    {P : GeodesicTransport.PreferredChartExpAtTrajectoryPackage g x}
    (hx : x ∈ C.restrictToFixedAnchorCutoffOne.rawLocalFamily.anchors)
    (data : GenericInverseEndpointODEAdmissibilityData
      C.restrictToFixedAnchorCutoffOne x w P)
    (hprotectedFixed :
      ∀ q ∈ closedBall (extChartAt I x₀ x₀, (0 : E))
          C.selector.projectFirstVariational.protectedInnerRadius,
        q.1 ∈ (extChartAt I x₀).target ∧
          q.1 ∈ IsometryInstantiate.cutoffOneLocus x₀) :
    Nonempty (C.GenericInverseEndpointODETailOverlapData x w P hx) := by
  have hpullback :=
    C.pulledbackPosition_eqOn_Icc_of_fixedSourceChartCutoff_protectedInnerBall
      hx data hprotectedFixed
  apply
    C.nonempty_genericInverseEndpointODETailOverlapData_of_fixedSourceChartCutoff_protectedInnerBall
      hx data hprotectedFixed
  · intro t ht
    let v : E := C.time⁻¹ • fixedToAnchorVelocity x₀ (x, w)
    have htIcc : t ∈ Icc (0 : ℝ) C.time :=
      ⟨(C.initialOverlapTime_pos hx data).le.trans ht.1.le, ht.2⟩
    have htPreferred : t ∈ Icc (-P.time) P.time :=
      ⟨by linarith [P.time_pos, htIcc.1],
        htIcc.2.trans data.preferredTime_le⟩
    have hmoving := moving_memberships_of_pulledback_position_eq
      (P.position_mem_target v data.preferredVelocity_small t htPreferred)
      (P.position_mem_cutoffOne v data.preferredVelocity_small t htPreferred)
      (hpullback t htIcc)
    exact hmoving.1
  · intro t ht
    let v : E := C.time⁻¹ • fixedToAnchorVelocity x₀ (x, w)
    have htIcc : t ∈ Icc (0 : ℝ) C.time :=
      ⟨(C.initialOverlapTime_pos hx data).le.trans ht.1.le, ht.2⟩
    have htPreferred : t ∈ Icc (-P.time) P.time :=
      ⟨by linarith [P.time_pos, htIcc.1],
        htIcc.2.trans data.preferredTime_le⟩
    have hmoving := moving_memberships_of_pulledback_position_eq
      (P.position_mem_target v data.preferredVelocity_small t htPreferred)
      (P.position_mem_cutoffOne v data.preferredVelocity_small t htPreferred)
      (hpullback t htIcc)
    exact hmoving.2.2

namespace GenericInverseEndpointODETailOverlapData

/-- The automatic initial interval and the exact tail residual combine to
the previously verified strictly-positive-time package. -/
def toPositiveTimeOverlapData
    {C : FixedChartAnchorEndpointPackage g x₀}
    {x : M} {w : E}
    {P : GeodesicTransport.PreferredChartExpAtTrajectoryPackage g x}
    {hx : x ∈ C.restrictToFixedAnchorCutoffOne.rawLocalFamily.anchors}
    (data : C.GenericInverseEndpointODETailOverlapData x w P hx) :
    GenericInverseEndpointODEPositiveTimeOverlapData
      C.restrictToFixedAnchorCutoffOne x w P where
  selectorInitial_mem := data.admissibility.selectorInitial_mem
  preferredTime_le := data.admissibility.preferredTime_le
  preferredVelocity_small := data.admissibility.preferredVelocity_small
  sourceChart_mem := by
    intro t ht
    by_cases htail : C.initialOverlapTime hx data.admissibility < t
    · exact data.sourceChart_mem t ⟨htail, ht.2⟩
    · have hgood := C.initialOverlapTime_mem_goodLocus hx data.admissibility
          t ⟨ht.1.le, le_of_not_gt htail⟩
      exact hgood.1.1.1
  targetChart_mem := by
    intro t ht
    by_cases htail : C.initialOverlapTime hx data.admissibility < t
    · exact data.targetChart_mem t ⟨htail, ht.2⟩
    · have hgood := C.initialOverlapTime_mem_goodLocus hx data.admissibility
          t ⟨ht.1.le, le_of_not_gt htail⟩
      exact hgood.1.1.2
  sourceCutoffOne_mem := by
    intro t ht
    by_cases htail : C.initialOverlapTime hx data.admissibility < t
    · exact data.sourceCutoffOne_mem t ⟨htail, ht.2⟩
    · have hgood := C.initialOverlapTime_mem_goodLocus hx data.admissibility
          t ⟨ht.1.le, le_of_not_gt htail⟩
      exact hgood.1.2
  targetCutoffOne_mem := by
    intro t ht
    by_cases htail : C.initialOverlapTime hx data.admissibility < t
    · exact data.targetCutoffOne_mem t ⟨htail, ht.2⟩
    · have hgood := C.initialOverlapTime_mem_goodLocus hx data.admissibility
          t ⟨ht.1.le, le_of_not_gt htail⟩
      exact hgood.2

end GenericInverseEndpointODETailOverlapData

/-! ## Provider reduction -/

def GenericInverseEndpointODETailOverlapProvider
    (C : FixedChartAnchorEndpointPackage g x₀) : Prop :=
  ∀ (x : M) (w : E)
      (hx : x ∈ C.restrictToFixedAnchorCutoffOne.rawLocalFamily.anchors),
    (extChartAt I x₀ x, w) ∈
      C.restrictToFixedAnchorCutoffOne.endpoint.source →
    (x, fixedToAnchorVelocity x₀ (x, w)) ∈
      (genericFamily g).targetLocus →
      ∃ P : GeodesicTransport.PreferredChartExpAtTrajectoryPackage g x,
        Nonempty (C.GenericInverseEndpointODETailOverlapData x w P hx)

/-- The remaining provider after connected continuation: choose compatible
selector/public-flow domains, but supply no chart or cutoff retention along
the trajectory. -/
def GenericInverseEndpointODEAdmissibilityProvider
    (C : FixedChartAnchorEndpointPackage g x₀) : Prop :=
  ∀ (x : M) (w : E)
      (_hx : x ∈ C.restrictToFixedAnchorCutoffOne.rawLocalFamily.anchors),
    (extChartAt I x₀ x, w) ∈
      C.restrictToFixedAnchorCutoffOne.endpoint.source →
    (x, fixedToAnchorVelocity x₀ (x, w)) ∈
      (genericFamily g).targetLocus →
      ∃ P : GeodesicTransport.PreferredChartExpAtTrajectoryPackage g x,
        GenericInverseEndpointODEAdmissibilityData
          C.restrictToFixedAnchorCutoffOne x w P

/-- The time-normalized provider boundary.  It retains only selector-domain
membership and the scale-invariant preferred-flow budget for an unscaled
trajectory package. -/
def GenericInverseEndpointODEVelocityBudgetProvider
    (C : FixedChartAnchorEndpointPackage g x₀) : Prop :=
  ∀ (x : M) (w : E)
      (_hx : x ∈ C.restrictToFixedAnchorCutoffOne.rawLocalFamily.anchors),
    (extChartAt I x₀ x, w) ∈
      C.restrictToFixedAnchorCutoffOne.endpoint.source →
    (x, fixedToAnchorVelocity x₀ (x, w)) ∈
      (genericFamily g).targetLocus →
      ∃ P : GeodesicTransport.PreferredChartExpAtTrajectoryPackage g x,
        (extChartAt I x₀ x,
            C.restrictToFixedAnchorCutoffOne.time⁻¹ • w) ∈
          closedBall (extChartAt I x₀ x₀, (0 : E))
            (C.restrictToFixedAnchorCutoffOne.selector.projectFirstVariational.initialRadius : ℝ) ∧
        ‖fixedToAnchorVelocity x₀ (x, w)‖ <
          P.time * P.velocityRadius

/-- Reparameterizing each unscaled preferred package at `C.time` converts the
velocity-budget provider into the existing admissibility provider. -/
theorem genericInverseEndpointODEAdmissibilityProvider_of_velocityBudget
    (C : FixedChartAnchorEndpointPackage g x₀)
    (hbudget : C.GenericInverseEndpointODEVelocityBudgetProvider) :
    C.GenericInverseEndpointODEAdmissibilityProvider := by
  intro x w hx hw htarget
  rcases hbudget x w hx hw htarget with
    ⟨P, hselector, hvelocity⟩
  rcases
      C.restrictToFixedAnchorCutoffOne.nonempty_reparameterized_admissibility_of_velocity_budget
        x w P hselector hvelocity with
    ⟨Q, _hQtime, ⟨data⟩⟩
  exact ⟨Q, data⟩

/-- Fixed-chart protection and admissibility alone provide every tail-overlap
package.  Connected ODE continuation supplies the two moving-chart fields. -/
theorem genericInverseEndpointODETailOverlapProvider_of_admissibility
    (C : FixedChartAnchorEndpointPackage g x₀)
    (hprotectedFixed :
      ∀ q ∈ closedBall (extChartAt I x₀ x₀, (0 : E))
          C.selector.projectFirstVariational.protectedInnerRadius,
        q.1 ∈ (extChartAt I x₀).target ∧
          q.1 ∈ IsometryInstantiate.cutoffOneLocus x₀)
    (hadmissible : C.GenericInverseEndpointODEAdmissibilityProvider) :
    C.GenericInverseEndpointODETailOverlapProvider := by
  intro x w hx hw htarget
  rcases hadmissible x w hx hw htarget with ⟨P, data⟩
  exact ⟨P,
    C.nonempty_genericInverseEndpointODETailOverlapData_of_fixedSourceChartCutoff_protectedInnerBall_automatic
      hx data hprotectedFixed⟩

theorem genericInverseEndpointODEPositiveTimeOverlapProvider_of_tail
    (C : FixedChartAnchorEndpointPackage g x₀)
    (htail : C.GenericInverseEndpointODETailOverlapProvider) :
    C.GenericInverseEndpointODEPositiveTimeOverlapProvider := by
  intro x w hx hw htarget
  rcases htail x w hx hw htarget with ⟨P, ⟨data⟩⟩
  exact ⟨P, ⟨data.toPositiveTimeOverlapData⟩⟩

theorem genericInverseEndpointODEComparisonProvider_of_tailOverlap
    (C : FixedChartAnchorEndpointPackage g x₀)
    (htail : C.GenericInverseEndpointODETailOverlapProvider) :
    GenericInverseEndpointODEComparisonProvider
      C.restrictToFixedAnchorCutoffOne :=
  C.genericInverseEndpointODEComparisonProvider_of_positiveTimeOverlap
    (C.genericInverseEndpointODEPositiveTimeOverlapProvider_of_tail htail)

theorem genericInverseEndpointAgreement_of_tailOverlap
    (C : FixedChartAnchorEndpointPackage g x₀)
    (htail : C.GenericInverseEndpointODETailOverlapProvider) :
    C.restrictToFixedAnchorCutoffOne.GenericInverseEndpointAgreement :=
  C.genericInverseEndpointAgreement_of_positiveTimeOverlap
    (C.genericInverseEndpointODEPositiveTimeOverlapProvider_of_tail htail)

/-- The fixed-chart ODE construction reaches generic inverse-endpoint
agreement from its three genuine domain inequalities alone.  No moving chart
or cutoff path hypothesis remains. -/
theorem genericInverseEndpointAgreement_of_admissibility
    (C : FixedChartAnchorEndpointPackage g x₀)
    (hprotectedFixed :
      ∀ q ∈ closedBall (extChartAt I x₀ x₀, (0 : E))
          C.selector.projectFirstVariational.protectedInnerRadius,
        q.1 ∈ (extChartAt I x₀).target ∧
          q.1 ∈ IsometryInstantiate.cutoffOneLocus x₀)
    (hadmissible : C.GenericInverseEndpointODEAdmissibilityProvider) :
    C.restrictToFixedAnchorCutoffOne.GenericInverseEndpointAgreement :=
  C.genericInverseEndpointAgreement_of_tailOverlap
    (C.genericInverseEndpointODETailOverlapProvider_of_admissibility
      hprotectedFixed hadmissible)

/-- The scale-invariant preferred-flow budget, together with selector-domain
membership, is enough for generic inverse-endpoint agreement. -/
theorem genericInverseEndpointAgreement_of_velocityBudget
    (C : FixedChartAnchorEndpointPackage g x₀)
    (hprotectedFixed :
      ∀ q ∈ closedBall (extChartAt I x₀ x₀, (0 : E))
          C.selector.projectFirstVariational.protectedInnerRadius,
        q.1 ∈ (extChartAt I x₀).target ∧
          q.1 ∈ IsometryInstantiate.cutoffOneLocus x₀)
    (hbudget : C.GenericInverseEndpointODEVelocityBudgetProvider) :
    C.restrictToFixedAnchorCutoffOne.GenericInverseEndpointAgreement :=
  C.genericInverseEndpointAgreement_of_admissibility hprotectedFixed
    (C.genericInverseEndpointODEAdmissibilityProvider_of_velocityBudget
      hbudget)

/-- A protected fixed-chart package can always be chosen so that generic
inverse-endpoint agreement is reduced exactly to the three admissibility
domain conditions. -/
theorem exists_fixedChartAnchorEndpointPackage_with_genericInverseEndpointAgreement_of_admissibility
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M) :
    ∃ C : FixedChartAnchorEndpointPackage g x₀,
      C.GenericInverseEndpointODEAdmissibilityProvider →
        C.restrictToFixedAnchorCutoffOne.GenericInverseEndpointAgreement := by
  rcases
      exists_fixedChartAnchorEndpointPackage_with_fixedSourceChartCutoff_protectedInnerBall
        g x₀ with
    ⟨C, hprotectedFixed⟩
  exact ⟨C, C.genericInverseEndpointAgreement_of_admissibility
    hprotectedFixed⟩

/-- A protected fixed-chart package can be chosen so that generic
inverse-endpoint agreement is reduced to selector-domain membership and the
scale-invariant preferred-flow velocity budget. -/
theorem exists_fixedChartAnchorEndpointPackage_with_genericInverseEndpointAgreement_of_velocityBudget
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M) :
    ∃ C : FixedChartAnchorEndpointPackage g x₀,
      C.GenericInverseEndpointODEVelocityBudgetProvider →
        C.restrictToFixedAnchorCutoffOne.GenericInverseEndpointAgreement := by
  rcases
      exists_fixedChartAnchorEndpointPackage_with_fixedSourceChartCutoff_protectedInnerBall
        g x₀ with
    ⟨C, hprotectedFixed⟩
  exact ⟨C, C.genericInverseEndpointAgreement_of_velocityBudget
    hprotectedFixed⟩

end FixedChartAnchorEndpointPackage
end CartanSourceExponentialLocalFamilyTransport
end Poincare
