import Poincare.Global.CartanFixedChartGenericInverseEndpointODEComparison
import Poincare.Global.ExponentialFixedTime
import Poincare.Global.IsometryInstantiate

/-!
# Constructing the generic-inverse ODE comparison from actual selectors

This file chooses the preferred trajectory from the PL flow that defines the
repository's public `expAt`.  Its initial value, geodesic ODE, continuity,
closed-ball bound, chart-target membership, and endpoint evaluation are
therefore theorems rather than comparison-package inputs.

For the fixed-chart curve, the regular selector supplies its initial value
and source-chart ODE.  The chart-transition theorem transports that ODE once
the genuine overlap and cutoff-one neighborhoods are supplied along the
path.  Compactness of the two continuous trajectories constructs their common
closed ball automatically.

The remaining primitive fields are honest local obligations: both initial
velocities must lie in the retained selector domains, the public PL interval
must cover the selected fixed time, and the moving chart overlap/cutoff germs
must hold along the fixed selector.  No endpoint equality is assumed.
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

/-! ## The actual preferred-chart PL trajectory -/

namespace GeodesicTransport

variable {M : Type u}
variable [TopologicalSpace M]
variable [ChartedSpace E M]
variable [IsManifold I ∞ M]

/-- A closed interval of the actual PL flow used to define `expAt`, restricted
so that the flow and endpoint laws share one positive time. -/
structure PreferredChartExpAtTrajectoryPackage
    (g : ClosedSmoothRiemannianMetric 3 M) (x : M) where
  time : ℝ
  time_pos : 0 < time
  velocityRadius : ℝ
  velocityRadius_pos : 0 < velocityRadius
  stateRadius : ℝ≥0
  trajectory : E → ℝ → E × E
  initial : ∀ v : E, ‖v‖ < velocityRadius →
    trajectory v 0 = (extChartAt I x x, v)
  derivative : ∀ v : E, ‖v‖ < velocityRadius →
    ∀ t ∈ Icc (-time) time,
      HasDerivWithinAt (trajectory v)
        (geodesicFlowField (chartChristoffelField g x) (trajectory v t))
        (Icc (-time) time) t
  mem_closedBall : ∀ v : E, ‖v‖ < velocityRadius →
    ∀ t ∈ Icc (-time) time,
      trajectory v t ∈
        closedBall (extChartAt I x x, (0 : E)) (stateRadius : ℝ)
  position_mem_target : ∀ v : E, ‖v‖ < velocityRadius →
    ∀ t ∈ Icc (-time) time,
      (trajectory v t).1 ∈ (extChartAt I x).target
  position_mem_cutoffOne : ∀ v : E, ‖v‖ < velocityRadius →
    ∀ t ∈ Icc (-time) time,
      (trajectory v t).1 ∈ IsometryInstantiate.cutoffOneLocus x
  expAt_eq : ∀ v : E, ‖v‖ < velocityRadius →
    ∀ t ∈ Icc (0 : ℝ) time,
      expAt g x (t • v) =
        (extChartAt I x).symm (trajectory v t).1

/-- Every neighborhood of the preferred-chart anchor admits an actual public
`expAt` trajectory package whose positions remain in that neighborhood and in
the cutoff-one locus. -/
theorem exists_preferredChartExpAtTrajectoryPackage_with_position_mem_neighborhood
    (g : ClosedSmoothRiemannianMetric 3 M) (x : M)
    {U : Set E} (hU : U ∈ 𝓝 (extChartAt I x x)) :
    ∃ P : PreferredChartExpAtTrajectoryPackage g x,
      ∀ v : E, ‖v‖ < P.velocityRadius →
        ∀ t ∈ Icc (-P.time) P.time, (P.trajectory v t).1 ∈ U := by
  rcases expAt_uniform_pl_flow_eq_on_Icc (g := g) (x₀ := x) with
    ⟨τ, hτ, δ, hδ, ε, hε, a, α, hα, hexp⟩
  let z₀ : E := extChartAt I x x
  have hprotected_nhds :
      IsometryInstantiate.cutoffOneLocus x ∩ U ∈ 𝓝 z₀ := by
    exact inter_mem
      (by simpa [z₀] using
        IsometryInstantiate.cutoffOneLocus_mem_nhds_anchor x)
      (by simpa [z₀] using hU)
  rcases Metric.nhds_basis_closedBall.mem_iff.mp hprotected_nhds with
    ⟨ρ, hρpos, hρsub⟩
  let κ : ℝ := ρ / (2 * ((a : ℝ) + 1))
  have hκ : 0 < κ := by
    dsimp [κ]
    positivity
  let T : ℝ := min τ (min ε κ)
  have hT : 0 < T := by
    dsimp [T]
    exact lt_min hτ (lt_min hε hκ)
  have hTτ : T ≤ τ := by
    dsimp [T]
    exact min_le_left _ _
  have hTε : T ≤ ε := by
    dsimp [T]
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hTκ : T ≤ κ := by
    dsimp [T]
    exact (min_le_right _ _).trans (min_le_right _ _)
  have hsymm : Icc (-T) T ⊆ Icc (-ε) ε := by
    intro t ht
    exact ⟨(neg_le_neg hTε).trans ht.1, ht.2.trans hTε⟩
  have hposition_mem_protected :
      ∀ v : E, ‖v‖ < δ → ∀ t ∈ Icc (-T) T,
        (α (extChartAt I x x, v) t).1 ∈
          IsometryInstantiate.cutoffOneLocus x ∩ U := by
    intro v hv t ht
    apply hρsub
    rcases hα v hv with ⟨hα0, hαder, hαmem, _hαtarget, _hhom⟩
    have hdist :
        dist (α (extChartAt I x x, v) t).1 z₀ ≤ (a : ℝ) * |t| := by
      simpa [z₀] using
        plFlowPosition_dist_anchor_le_radius_mul_abs
          (g := g) (x₀ := x) (ε := ε) (τ := T) (a := a)
          (α := α) (v₀ := v) hT.le hTε hα0 hαder hαmem ht
    have habs : |t| ≤ T := abs_le.mpr ht
    have ha_nonneg : 0 ≤ (a : ℝ) := NNReal.coe_nonneg a
    have hdistρ : dist (α (extChartAt I x x, v) t).1 z₀ ≤ ρ := by
      calc
        dist (α (extChartAt I x x, v) t).1 z₀
            ≤ (a : ℝ) * |t| := hdist
        _ ≤ (a : ℝ) * T := mul_le_mul_of_nonneg_left habs ha_nonneg
        _ ≤ (a : ℝ) * κ := mul_le_mul_of_nonneg_left hTκ ha_nonneg
        _ = (ρ / 2) * ((a : ℝ) / ((a : ℝ) + 1)) := by
          dsimp [κ]
          have hden : ((a : ℝ) + 1) ≠ 0 := by positivity
          field_simp [hden]
        _ ≤ (ρ / 2) * 1 := by
          gcongr
          rw [div_le_one (by positivity : 0 < (a : ℝ) + 1)]
          linarith
        _ ≤ ρ := by linarith
    simpa [Metric.mem_closedBall] using hdistρ
  refine ⟨{
    time := T
    time_pos := hT
    velocityRadius := δ
    velocityRadius_pos := hδ
    stateRadius := a
    trajectory := fun v t => α (extChartAt I x x, v) t
    initial := ?_
    derivative := ?_
    mem_closedBall := ?_
    position_mem_target := ?_
    position_mem_cutoffOne := ?_
    expAt_eq := ?_ }, ?_⟩
  · intro v hv
    exact (hα v hv).1
  · intro v hv t ht
    exact ((hα v hv).2.1 t (hsymm ht)).mono hsymm
  · intro v hv t ht
    exact (hα v hv).2.2.1 t (hsymm ht)
  · intro v hv t ht
    exact (hα v hv).2.2.2.1 t (hsymm ht)
  · intro v hv t ht
    exact (hposition_mem_protected v hv t ht).1
  · intro v hv t ht
    exact hexp v hv t ⟨ht.1, ht.2.trans hTτ⟩
  · intro v hv t ht
    exact (hposition_mem_protected v hv t ht).2

/-- Every preferred chart has an actual trajectory package.  This is the
universal-neighborhood wrapper around the protected constructor. -/
theorem exists_preferredChartExpAtTrajectoryPackage
    (g : ClosedSmoothRiemannianMetric 3 M) (x : M) :
    Nonempty (PreferredChartExpAtTrajectoryPackage g x) := by
  rcases
      exists_preferredChartExpAtTrajectoryPackage_with_position_mem_neighborhood
        g x (U := Set.univ) Filter.univ_mem with
    ⟨P, _hP⟩
  exact ⟨P⟩

end GeodesicTransport

/-! ## Primitive comparison data -/

namespace CartanSourceExponentialLocalFamilyTransport
namespace FixedChartAnchorEndpointPackage

variable {M : Type u}
variable [TopologicalSpace M]
variable [ChartedSpace E M]
variable [IsManifold I ∞ M]

variable {g : ClosedSmoothRiemannianMetric 3 M} {x₀ : M}

open CartanSourceExponential
open CartanGenericSuccessorDataMovingPersistenceReduction

/-- The actual preferred PL trajectory, normalized so that its value at
`C.time` represents the public exponential of the transported vector. -/
def preferredExpAtTrajectory
    (C : FixedChartAnchorEndpointPackage g x₀)
    {x : M}
    (P : GeodesicTransport.PreferredChartExpAtTrajectoryPackage g x)
    (w : E) : ℝ → E × E :=
  P.trajectory
    (C.time⁻¹ • fixedToAnchorVelocity x₀ (x, w))

/-- Local admissibility and moving-chart overlap facts needed to turn the two
already existing selectors into an ODE comparison.  There is deliberately no
curve equality and no endpoint equality in this record. -/
structure GenericInverseEndpointODEPrimitiveData
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
  sourceChart_nhds : ∀ t ∈ Icc (0 : ℝ) C.time,
    (extChartAt I x₀).target ∈
      nhds (C.normalizedSelectorTrajectory x w t).1
  targetChart_nhds : ∀ t ∈ Icc (0 : ℝ) C.time,
    {q : E | (extChartAt I x₀).symm q ∈
      (extChartAt I x).source} ∈
        nhds (C.normalizedSelectorTrajectory x w t).1
  sourceCutoff_nhds : ∀ t ∈ Icc (0 : ℝ) C.time,
    {q : E | GeodesicTransport.cutoff (n := 3) x₀ q = 1} ∈
      nhds (C.normalizedSelectorTrajectory x w t).1
  targetCutoff_nhds : ∀ t ∈ Icc (0 : ℝ) C.time,
    {q : E | GeodesicTransport.cutoff (n := 3) x
      (GeodesicTransport.chartTransition x₀ x q) = 1} ∈
        nhds (C.normalizedSelectorTrajectory x w t).1

namespace GenericInverseEndpointODEPrimitiveData

/-- The source regular selector starts at the requested normalized state. -/
theorem selectorInitial
    {C : FixedChartAnchorEndpointPackage g x₀}
    {x : M} {w : E}
    {P : GeodesicTransport.PreferredChartExpAtTrajectoryPackage g x}
    (data : C.GenericInverseEndpointODEPrimitiveData x w P) :
    C.normalizedSelectorTrajectory x w 0 =
      (extChartAt I x₀ x, C.time⁻¹ • w) := by
  simpa [normalizedSelectorTrajectory] using
    (C.selector.projectFirstVariational.selector_data
      (extChartAt I x₀ x, C.time⁻¹ • w)
      data.selectorInitial_mem).1

/-- The preferred PL trajectory starts at the transported normalized state. -/
theorem preferredInitial
    {C : FixedChartAnchorEndpointPackage g x₀}
    {x : M} {w : E}
    {P : GeodesicTransport.PreferredChartExpAtTrajectoryPackage g x}
    (data : C.GenericInverseEndpointODEPrimitiveData x w P) :
    C.preferredExpAtTrajectory P w 0 =
      (extChartAt I x x,
        C.time⁻¹ • fixedToAnchorVelocity x₀ (x, w)) := by
  exact P.initial _ data.preferredVelocity_small

/-- The preferred PL trajectory evaluates at the selected time to the public
charted exponential. -/
theorem preferredEndpoint
    {C : FixedChartAnchorEndpointPackage g x₀}
    {x : M} {w : E}
    {P : GeodesicTransport.PreferredChartExpAtTrajectoryPackage g x}
    (data : C.GenericInverseEndpointODEPrimitiveData x w P) :
    (C.preferredExpAtTrajectory P w C.time).1 =
      GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x
        (fixedToAnchorVelocity x₀ (x, w)) := by
  let v : E := C.time⁻¹ • fixedToAnchorVelocity x₀ (x, w)
  have htime : C.time ∈ Icc (0 : ℝ) P.time :=
    ⟨C.time_pos.le, data.preferredTime_le⟩
  have hfull : C.time ∈ Icc (-P.time) P.time :=
    ⟨by linarith [P.time_pos, C.time_pos], data.preferredTime_le⟩
  have htarget : (P.trajectory v C.time).1 ∈ (extChartAt I x).target :=
    P.position_mem_target v data.preferredVelocity_small C.time hfull
  have hscale : C.time • v = fixedToAnchorVelocity x₀ (x, w) := by
    simp [v, smul_smul, ne_of_gt C.time_pos]
  have hexp := P.expAt_eq v data.preferredVelocity_small C.time htime
  rw [hscale] at hexp
  calc
    (C.preferredExpAtTrajectory P w C.time).1 =
        extChartAt I x ((extChartAt I x).symm (P.trajectory v C.time).1) := by
      change (P.trajectory v C.time).1 = _
      exact ((extChartAt I x).right_inv htarget).symm
    _ = extChartAt I x
          (GeodesicTransport.expAt g x
            (fixedToAnchorVelocity x₀ (x, w))) :=
      congrArg (extChartAt I x) hexp.symm
    _ = GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x
          (fixedToAnchorVelocity x₀ (x, w)) := rfl

/-- The overlap germs transport the fixed selector's source-chart ODE into
the preferred chart at every point of the full comparison interval. -/
theorem transported_hasDerivAt
    {C : FixedChartAnchorEndpointPackage g x₀}
    {x : M} {w : E}
    {P : GeodesicTransport.PreferredChartExpAtTrajectoryPackage g x}
    (data : C.GenericInverseEndpointODEPrimitiveData x w P) :
    ∀ t ∈ Icc (0 : ℝ) C.time,
      HasDerivAt (C.preferredTransportedSelectorTrajectory x w)
        (geodesicFlowField
          (GeodesicTransport.chartChristoffelField g x)
          (C.preferredTransportedSelectorTrajectory x w t)) t := by
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
  intro t ht
  have htInterior : t ∈ Ioo (-B.epsilon) B.epsilon := by
    constructor
    · linarith [B.epsilon_pos, ht.1]
    · linarith [ht.2, htimeProtected, B.epsilon_pos]
  have hsource : HasDerivAt (C.normalizedSelectorTrajectory x w)
      (geodesicFlowField
        (GeodesicTransport.chartChristoffelField g x₀)
        (C.normalizedSelectorTrajectory x w t)) t := by
    simpa [normalizedSelectorTrajectory,
      CartanSourceExponentialLocalChartSelector.fixedChartGeodesicField] using
        (hselector.2.1 t (hinterval ht)).hasDerivAt
          (Icc_mem_nhds htInterior.1 htInterior.2)
  simpa [preferredTransportedSelectorTrajectory] using
    GeodesicTransport.chartTransitionState_hasDerivAt_of_cutoff_eq_one_nhds
      g x₀ x hsource
        (data.sourceChart_nhds t ht)
        (data.targetChart_nhds t ht)
        (data.sourceCutoff_nhds t ht)
        (data.targetCutoff_nhds t ht)

/-- The actual PL flow gives the preferred curve's ODE on the comparison
interval. -/
theorem preferred_hasDerivWithinAt
    {C : FixedChartAnchorEndpointPackage g x₀}
    {x : M} {w : E}
    {P : GeodesicTransport.PreferredChartExpAtTrajectoryPackage g x}
    (data : C.GenericInverseEndpointODEPrimitiveData x w P) :
    ∀ t ∈ Icc (0 : ℝ) C.time,
      HasDerivWithinAt (C.preferredExpAtTrajectory P w)
        (geodesicFlowField
          (GeodesicTransport.chartChristoffelField g x)
          (C.preferredExpAtTrajectory P w t))
        (Icc (0 : ℝ) C.time) t := by
  let v : E := C.time⁻¹ • fixedToAnchorVelocity x₀ (x, w)
  have hinterval : Icc (0 : ℝ) C.time ⊆ Icc (-P.time) P.time := by
    intro t ht
    exact ⟨by linarith [P.time_pos, ht.1], ht.2.trans data.preferredTime_le⟩
  intro t ht
  exact
    (P.derivative v data.preferredVelocity_small t (hinterval ht)).mono hinterval

/-- The pathwise target-chart overlap includes the whole selector path. -/
theorem selectorPositionOverlap
    {C : FixedChartAnchorEndpointPackage g x₀}
    {x : M} {w : E}
    {P : GeodesicTransport.PreferredChartExpAtTrajectoryPackage g x}
    (data : C.GenericInverseEndpointODEPrimitiveData x w P) :
    ∀ t ∈ Icc (0 : ℝ) C.time,
      (extChartAt I x₀).symm (C.normalizedSelectorTrajectory x w t).1 ∈
        (chartAt E x).source := by
  intro t ht
  have hmem :
      (extChartAt I x₀).symm (C.normalizedSelectorTrajectory x w t).1 ∈
        (extChartAt I x).source :=
    mem_of_mem_nhds
      (x := (C.normalizedSelectorTrajectory x w t).1)
      (s := {q : E | (extChartAt I x₀).symm q ∈
        (extChartAt I x).source})
      (data.targetChart_nhds t ht)
  rwa [extChartAt_source] at hmem

/-- Assemble the full ODE comparison.  The common closed ball is obtained
from compactness of the two already proved continuous trajectories. -/
noncomputable def toODEComparison
    {C : FixedChartAnchorEndpointPackage g x₀}
    {x : M} {w : E}
    {P : GeodesicTransport.PreferredChartExpAtTrajectoryPackage g x}
    (data : C.GenericInverseEndpointODEPrimitiveData x w P) :
    C.GenericInverseEndpointODEComparison x w := by
  let γ : ℝ → E × E := C.preferredTransportedSelectorTrajectory x w
  let η : ℝ → E × E := C.preferredExpAtTrajectory P w
  have hγder : ∀ t ∈ Icc (0 : ℝ) C.time,
      HasDerivAt γ
        (geodesicFlowField
          (GeodesicTransport.chartChristoffelField g x) (γ t)) t := by
    simpa [γ] using data.transported_hasDerivAt
  have hηder : ∀ t ∈ Icc (0 : ℝ) C.time,
      HasDerivWithinAt η
        (geodesicFlowField
          (GeodesicTransport.chartChristoffelField g x) (η t))
        (Icc (0 : ℝ) C.time) t := by
    simpa [η] using data.preferred_hasDerivWithinAt
  have hγcont : ContinuousOn γ (Icc (0 : ℝ) C.time) :=
    HasDerivAt.continuousOn hγder
  have hηcont : ContinuousOn η (Icc (0 : ℝ) C.time) :=
    HasDerivWithinAt.continuousOn hηder
  have hcompact : IsCompact
      (γ '' Icc (0 : ℝ) C.time ∪ η '' Icc (0 : ℝ) C.time) :=
    (isCompact_Icc.image_of_continuousOn hγcont).union
      (isCompact_Icc.image_of_continuousOn hηcont)
  let R : ℝ := Classical.choose
    (hcompact.isBounded.subset_closedBall (extChartAt I x x, (0 : E)))
  have hR : γ '' Icc (0 : ℝ) C.time ∪ η '' Icc (0 : ℝ) C.time ⊆
      closedBall (extChartAt I x x, (0 : E)) R :=
    Classical.choose_spec
      (hcompact.isBounded.subset_closedBall (extChartAt I x x, (0 : E)))
  exact {
    preferredTrajectory := η
    commonCenter := (extChartAt I x x, (0 : E))
    commonRadius := R
    selectorInitial := data.selectorInitial
    preferredInitial := by simpa [η] using data.preferredInitial
    transportedContinuous := hγcont
    preferredContinuous := hηcont
    transportedDerivative := by
      intro t ht
      exact (hγder t (Ico_subset_Icc_self ht)).hasDerivWithinAt
    preferredDerivative := by
      intro t ht
      exact
        (hηder t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin
          (Icc_mem_nhdsGE_of_mem ⟨ht.1, ht.2⟩)
    transportedMem := by
      intro t ht
      exact hR (Or.inl ⟨t, Ico_subset_Icc_self ht, rfl⟩)
    preferredMem := by
      intro t ht
      exact hR (Or.inr ⟨t, Ico_subset_Icc_self ht, rfl⟩)
    selectorPositionOverlap := data.selectorPositionOverlap
    preferredTrajectory_endpoint := by
      simpa [η] using data.preferredEndpoint }

end GenericInverseEndpointODEPrimitiveData

/-! ## Provider reduction -/

/-- At every relevant input, choose one actual public PL trajectory package
whose retained domains and moving-chart overlap germs contain the comparison
interval. -/
def GenericInverseEndpointODEPrimitiveProvider
    (C : FixedChartAnchorEndpointPackage g x₀) : Prop :=
  ∀ (x : M) (w : E), x ∈ C.rawLocalFamily.anchors →
    (extChartAt I x₀ x, w) ∈ C.endpoint.source →
    (x, fixedToAnchorVelocity x₀ (x, w)) ∈
      (genericFamily g).targetLocus →
      ∃ P : GeodesicTransport.PreferredChartExpAtTrajectoryPackage g x,
        Nonempty (C.GenericInverseEndpointODEPrimitiveData x w P)

/-- The primitive provider fills every field of the previously verified ODE
comparison provider. -/
theorem genericInverseEndpointODEComparisonProvider_of_primitive
    (C : FixedChartAnchorEndpointPackage g x₀)
    (hprimitive : C.GenericInverseEndpointODEPrimitiveProvider) :
    C.GenericInverseEndpointODEComparisonProvider := by
  intro x w hx hw htarget
  rcases hprimitive x w hx hw htarget with ⟨P, ⟨data⟩⟩
  exact ⟨data.toODEComparison⟩

/-- Hence actual selector/PL-flow primitive data prove the moving
generic-inverse endpoint identity. -/
theorem genericInverseEndpointAgreement_of_odePrimitive
    (C : FixedChartAnchorEndpointPackage g x₀)
    (hprimitive : C.GenericInverseEndpointODEPrimitiveProvider) :
    C.GenericInverseEndpointAgreement :=
  C.genericInverseEndpointAgreement_of_odeComparison
    (C.genericInverseEndpointODEComparisonProvider_of_primitive hprimitive)

end FixedChartAnchorEndpointPackage
end CartanSourceExponentialLocalFamilyTransport
end Poincare
