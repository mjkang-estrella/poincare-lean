import Poincare.Global.CartanFixedChartGenericInverseEndpointODEPositiveTimeOverlapReduction

/-!
# Automatic initial overlap and the remaining positive-time tail

After fixed-cutoff subordination, the selector starts in the combined open
chart/cutoff good locus.  Its ODE derivative makes the selector position
continuous at time zero.  Therefore one positive initial interval remains in
that good locus automatically.

This file chooses such an interval, bounded above by the fixed package time,
and retains the four honest overlap residuals only on the complementary
tail.  The residual field names and meanings are unchanged; only their time
domain becomes `Ioc initialOverlapTime C.time`.
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

end FixedChartAnchorEndpointPackage
end CartanSourceExponentialLocalFamilyTransport
end Poincare
