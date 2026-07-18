import Poincare.Global.CartanFixedChartGenericInverseEndpointODEPrimitive
import Poincare.Global.IsometryInstantiate

/-!
# Pointwise overlap data for the generic-inverse ODE comparison

The chart-transition ODE theorem is phrased using four neighborhood-valued
hypotheses along the source selector.  This file lowers all four to ordinary
pointwise membership:

* the source position lies in the fixed chart target;
* its fixed-chart inverse lies in the moving chart source;
* the source position lies in the fixed-anchor cutoff-one locus; and
* the transitioned position lies in the moving-anchor cutoff-one locus.

Openness of chart targets and cutoff-one loci, together with continuity of
the inverse chart and the honest chart transition on their overlap, recovers
the neighborhood hypotheses.  Compactness of the continuous selector path
then gives one positive uniform thickening contained in the combined good
locus.
-/

noncomputable section

set_option maxHeartbeats 1400000
set_option synthInstance.maxHeartbeats 200000

open Filter Function Metric Set
open scoped Manifold ContDiff Topology RealInnerProductSpace NNReal

namespace Poincare

universe u

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

namespace IsometryInstantiate

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace E M]
variable [IsManifold I ∞ M]

/-- The germ-defined cutoff-one locus is open. -/
theorem isOpen_cutoffOneLocus (x : M) : IsOpen (cutoffOneLocus x) := by
  exact isOpen_setOf_eventually_nhds

end IsometryInstantiate

namespace CartanSourceExponentialLocalFamilyTransport
namespace FixedChartAnchorEndpointPackage

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace E M]
variable [IsManifold I ∞ M]

variable {g : ClosedSmoothRiemannianMetric 3 M} {x₀ : M}

open CartanSourceExponential
open CartanGenericSuccessorDataMovingPersistenceReduction

/-- The model-space locus on which both charts overlap and both blended
Christoffel fields equal their raw chart fields as germs. -/
def chartTransitionCutoffGoodLocus (x₀ x : M) : Set E :=
  (((extChartAt I x₀).target ∩
      {q : E | (extChartAt I x₀).symm q ∈ (extChartAt I x).source}) ∩
    IsometryInstantiate.cutoffOneLocus x₀) ∩
      GeodesicTransport.chartTransition x₀ x ⁻¹'
        IsometryInstantiate.cutoffOneLocus x

/-- The combined honest chart-overlap/cutoff locus is open. -/
theorem isOpen_chartTransitionCutoffGoodLocus (x₀ x : M) :
    IsOpen (chartTransitionCutoffGoodLocus x₀ x) := by
  let overlap : Set E :=
    (extChartAt I x₀).target ∩
      {q : E | (extChartAt I x₀).symm q ∈ (extChartAt I x).source}
  have hopenOverlap : IsOpen overlap := by
    exact (continuousOn_extChartAt_symm x₀).isOpen_inter_preimage
      (isOpen_extChartAt_target x₀) (isOpen_extChartAt_source x)
  have htransition : ContinuousOn
      (GeodesicTransport.chartTransition x₀ x) overlap := by
    have hsymm : ContinuousOn (extChartAt I x₀).symm overlap :=
      (continuousOn_extChartAt_symm x₀).mono inter_subset_left
    have hchart : ContinuousOn (extChartAt I x) (extChartAt I x).source :=
      continuousOn_extChartAt x
    have hcomp := hchart.comp hsymm (fun _q hq => hq.2)
    simpa [GeodesicTransport.chartTransition] using hcomp
  let base : Set E := overlap ∩ IsometryInstantiate.cutoffOneLocus x₀
  have hopenBase : IsOpen base :=
    hopenOverlap.inter (IsometryInstantiate.isOpen_cutoffOneLocus x₀)
  have htransitionBase : ContinuousOn
      (GeodesicTransport.chartTransition x₀ x) base :=
    htransition.mono inter_subset_left
  simpa [chartTransitionCutoffGoodLocus, overlap, base] using
    htransitionBase.isOpen_inter_preimage hopenBase
      (IsometryInstantiate.isOpen_cutoffOneLocus x)

/-- Ordinary pointwise path membership plus the same selector/public-flow
domain admissibility used by the primitive constructor.  No neighborhood is
stored in this record. -/
structure GenericInverseEndpointODEPointwiseOverlapData
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
  sourceChart_mem : ∀ t ∈ Icc (0 : ℝ) C.time,
    (C.normalizedSelectorTrajectory x w t).1 ∈
      (extChartAt I x₀).target
  targetChart_mem : ∀ t ∈ Icc (0 : ℝ) C.time,
    (extChartAt I x₀).symm (C.normalizedSelectorTrajectory x w t).1 ∈
      (extChartAt I x).source
  sourceCutoffOne_mem : ∀ t ∈ Icc (0 : ℝ) C.time,
    (C.normalizedSelectorTrajectory x w t).1 ∈
      IsometryInstantiate.cutoffOneLocus x₀
  targetCutoffOne_mem : ∀ t ∈ Icc (0 : ℝ) C.time,
    GeodesicTransport.chartTransition x₀ x
        (C.normalizedSelectorTrajectory x w t).1 ∈
      IsometryInstantiate.cutoffOneLocus x

namespace GenericInverseEndpointODEPointwiseOverlapData

/-- Pointwise honest overlap membership recovers all four neighborhood-valued
fields of `GenericInverseEndpointODEPrimitiveData`. -/
def toODEPrimitiveData
    {C : FixedChartAnchorEndpointPackage g x₀}
    {x : M} {w : E}
    {P : GeodesicTransport.PreferredChartExpAtTrajectoryPackage g x}
    (data : C.GenericInverseEndpointODEPointwiseOverlapData x w P) :
    C.GenericInverseEndpointODEPrimitiveData x w P where
  selectorInitial_mem := data.selectorInitial_mem
  preferredTime_le := data.preferredTime_le
  preferredVelocity_small := data.preferredVelocity_small
  sourceChart_nhds := by
    intro t ht
    exact (isOpen_extChartAt_target x₀).mem_nhds (data.sourceChart_mem t ht)
  targetChart_nhds := by
    intro t ht
    let q : E := (C.normalizedSelectorTrajectory x w t).1
    have hsource : (extChartAt I x).source ∈
        nhds ((extChartAt I x₀).symm q) :=
      (isOpen_extChartAt_source x).mem_nhds (data.targetChart_mem t ht)
    exact (continuousAt_extChartAt_symm'' (data.sourceChart_mem t ht)).preimage_mem_nhds
      hsource
  sourceCutoff_nhds := by
    intro t ht
    exact IsometryInstantiate.cutoff_eventuallyEq_one_of_mem_cutoffOneLocus
      (data.sourceCutoffOne_mem t ht)
  targetCutoff_nhds := by
    intro t ht
    let q : E := (C.normalizedSelectorTrajectory x w t).1
    have htransition :=
      GeodesicTransport.chartTransition_hasFDerivAt_chartTransitionMFDeriv
        x₀ x (data.sourceChart_mem t ht) (data.targetChart_mem t ht)
    have htarget :=
      IsometryInstantiate.cutoff_eventuallyEq_one_of_mem_cutoffOneLocus
        (data.targetCutoffOne_mem t ht)
    exact htransition.continuousAt.preimage_mem_nhds htarget

/-- At time zero, fixed-chart target membership follows from the retained
anchor and the regular selector's initial-value theorem; it is not an
additional moving-chart hypothesis. -/
theorem sourceChart_mem_zero_of_anchor
    {C : FixedChartAnchorEndpointPackage g x₀}
    {x : M} {w : E}
    {P : GeodesicTransport.PreferredChartExpAtTrajectoryPackage g x}
    (hx : x ∈ C.rawLocalFamily.anchors)
    (data : C.GenericInverseEndpointODEPointwiseOverlapData x w P) :
    (C.normalizedSelectorTrajectory x w 0).1 ∈
      (extChartAt I x₀).target := by
  have hzero := data.toODEPrimitiveData.selectorInitial
  rw [hzero]
  exact (extChartAt I x₀).map_source hx.1

/-- At time zero, moving-chart source membership is automatic because the
fixed chart inverse is the retained anchor and every preferred chart contains
its own anchor. -/
theorem targetChart_mem_zero_of_anchor
    {C : FixedChartAnchorEndpointPackage g x₀}
    {x : M} {w : E}
    {P : GeodesicTransport.PreferredChartExpAtTrajectoryPackage g x}
    (hx : x ∈ C.rawLocalFamily.anchors)
    (data : C.GenericInverseEndpointODEPointwiseOverlapData x w P) :
    (extChartAt I x₀).symm (C.normalizedSelectorTrajectory x w 0).1 ∈
      (extChartAt I x).source := by
  have hzero := data.toODEPrimitiveData.selectorInitial
  rw [hzero, (extChartAt I x₀).left_inv hx.1]
  exact mem_extChartAt_source x

/-- The transitioned time-zero position is the moving chart's anchor
coordinate, hence lies automatically in its cutoff-one locus. -/
theorem targetCutoffOne_mem_zero_of_anchor
    {C : FixedChartAnchorEndpointPackage g x₀}
    {x : M} {w : E}
    {P : GeodesicTransport.PreferredChartExpAtTrajectoryPackage g x}
    (hx : x ∈ C.rawLocalFamily.anchors)
    (data : C.GenericInverseEndpointODEPointwiseOverlapData x w P) :
    GeodesicTransport.chartTransition x₀ x
        (C.normalizedSelectorTrajectory x w 0).1 ∈
      IsometryInstantiate.cutoffOneLocus x := by
  have hzero := data.toODEPrimitiveData.selectorInitial
  have hanchor : extChartAt I x x ∈
      IsometryInstantiate.cutoffOneLocus x :=
    mem_of_mem_nhds
      (IsometryInstantiate.cutoffOneLocus_mem_nhds_anchor x)
  rw [hzero]
  change extChartAt I x
      ((extChartAt I x₀).symm (extChartAt I x₀ x)) ∈
    IsometryInstantiate.cutoffOneLocus x
  rw [(extChartAt I x₀).left_inv hx.1]
  exact hanchor

/-- The normalized selector path is continuous on its full selected
interval. -/
theorem normalizedSelectorPosition_continuousOn
    {C : FixedChartAnchorEndpointPackage g x₀}
    {x : M} {w : E}
    {P : GeodesicTransport.PreferredChartExpAtTrajectoryPackage g x}
    (data : C.GenericInverseEndpointODEPointwiseOverlapData x w P) :
    ContinuousOn (fun t : ℝ => (C.normalizedSelectorTrajectory x w t).1)
      (Icc (0 : ℝ) C.time) := by
  let B := C.selector.projectFirstVariational
  have hselector := B.selector_data
    (extChartAt I x₀ x, C.time⁻¹ • w) data.selectorInitial_mem
  have htimeProtected : C.time < B.epsilon / 2 := by
    simpa [B] using C.time_protected.2
  have hinterval : Icc (0 : ℝ) C.time ⊆ Icc (-B.epsilon) B.epsilon := by
    intro t ht
    constructor
    · linarith [B.epsilon_pos, ht.1]
    · linarith [ht.2, htimeProtected, B.epsilon_pos]
  have hstate : ContinuousOn (C.normalizedSelectorTrajectory x w)
      (Icc (0 : ℝ) C.time) := by
    apply HasDerivWithinAt.continuousOn
    intro t ht
    simpa [normalizedSelectorTrajectory,
      CartanSourceExponentialLocalChartSelector.fixedChartGeodesicField] using
        (hselector.2.1 t (hinterval ht)).mono hinterval
  exact hstate.fst

/-- The full selector-position image lies in the one combined open good
locus. -/
theorem normalizedSelectorPosition_image_subset_goodLocus
    {C : FixedChartAnchorEndpointPackage g x₀}
    {x : M} {w : E}
    {P : GeodesicTransport.PreferredChartExpAtTrajectoryPackage g x}
    (data : C.GenericInverseEndpointODEPointwiseOverlapData x w P) :
    (fun t : ℝ => (C.normalizedSelectorTrajectory x w t).1) ''
        Icc (0 : ℝ) C.time ⊆ chartTransitionCutoffGoodLocus x₀ x := by
  rintro _q ⟨t, ht, rfl⟩
  exact ⟨⟨⟨data.sourceChart_mem t ht, data.targetChart_mem t ht⟩,
    data.sourceCutoffOne_mem t ht⟩, data.targetCutoffOne_mem t ht⟩

/-- Compactness upgrades pointwise membership to a positive uniform metric
thickening of the entire selector-position path inside the good locus. -/
theorem exists_uniform_goodLocus_thickening
    {C : FixedChartAnchorEndpointPackage g x₀}
    {x : M} {w : E}
    {P : GeodesicTransport.PreferredChartExpAtTrajectoryPackage g x}
    (data : C.GenericInverseEndpointODEPointwiseOverlapData x w P) :
    ∃ ρ > (0 : ℝ),
      thickening ρ
          ((fun t : ℝ => (C.normalizedSelectorTrajectory x w t).1) ''
            Icc (0 : ℝ) C.time) ⊆
        chartTransitionCutoffGoodLocus x₀ x := by
  have hcompact : IsCompact
      ((fun t : ℝ => (C.normalizedSelectorTrajectory x w t).1) ''
        Icc (0 : ℝ) C.time) :=
    isCompact_Icc.image_of_continuousOn data.normalizedSelectorPosition_continuousOn
  exact hcompact.exists_thickening_subset_open
    (isOpen_chartTransitionCutoffGoodLocus x₀ x)
    data.normalizedSelectorPosition_image_subset_goodLocus

end GenericInverseEndpointODEPointwiseOverlapData

/-! ## Provider reduction -/

def GenericInverseEndpointODEPointwiseOverlapProvider
    (C : FixedChartAnchorEndpointPackage g x₀) : Prop :=
  ∀ (x : M) (w : E), x ∈ C.rawLocalFamily.anchors →
    (extChartAt I x₀ x, w) ∈ C.endpoint.source →
    (x, fixedToAnchorVelocity x₀ (x, w)) ∈
      (genericFamily g).targetLocus →
      ∃ P : GeodesicTransport.PreferredChartExpAtTrajectoryPackage g x,
        Nonempty (C.GenericInverseEndpointODEPointwiseOverlapData x w P)

theorem genericInverseEndpointODEPrimitiveProvider_of_pointwiseOverlap
    (C : FixedChartAnchorEndpointPackage g x₀)
    (hpointwise : C.GenericInverseEndpointODEPointwiseOverlapProvider) :
    C.GenericInverseEndpointODEPrimitiveProvider := by
  intro x w hx hw htarget
  rcases hpointwise x w hx hw htarget with ⟨P, ⟨data⟩⟩
  exact ⟨P, ⟨data.toODEPrimitiveData⟩⟩

theorem genericInverseEndpointAgreement_of_pointwiseOverlap
    (C : FixedChartAnchorEndpointPackage g x₀)
    (hpointwise : C.GenericInverseEndpointODEPointwiseOverlapProvider) :
    C.GenericInverseEndpointAgreement :=
  C.genericInverseEndpointAgreement_of_odePrimitive
    (C.genericInverseEndpointODEPrimitiveProvider_of_pointwiseOverlap hpointwise)

end FixedChartAnchorEndpointPackage
end CartanSourceExponentialLocalFamilyTransport
end Poincare
