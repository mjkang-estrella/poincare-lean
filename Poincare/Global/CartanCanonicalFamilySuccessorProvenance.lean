import Poincare.Global.CartanCanonicalRootedRealizationTransfer

/-!
# Provenance-retaining canonical successor transfer

The canonical local-data argument starts with a generic differential successor
datum and transfers its target-chart fields to the canonical target
exponential.  This module retains the generic datum, the target-chart germ
comparison, and the dependent successor equality instead of returning only
the canonical datum.
-/

noncomputable section

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 140000

open Filter Function Metric Set
open scoped Manifold ContDiff Topology RealInnerProductSpace

namespace Poincare
namespace CartanCanonicalFamilySuccessorProvenance

universe u

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M]
variable [ChartedSpace E M]
variable [IsManifold I ∞ M]

open CartanTargetExponential
open CartanCanonicalFamilyGermComparison
open CartanCanonicalFamilyLocalDataTransfer
open CartanCanonicalRootedRealizationTransfer

/-- The supplied generic-family alignment has the same underlying tangent
alignment as the legacy generic datum from which it was built. -/
theorem ofGeneric_alignment_eq
    {g : ClosedSmoothRiemannianMetric 3 M}
    {s : CartanChain.ChainState g} {z : M}
    (d : DifferentialInducedSuccessor.Data s z) :
    (Data.ofGeneric d).alignment = d.alignment := by
  apply DFunLike.coe_injective
  funext u
  rfl

/-- Equality of target indices and of underlying continuous linear maps gives
heterogeneous equality of the dependent tangent alignments. -/
private theorem tangentAlignment_heq_of_target_eq_of_clm_eq
    {g : ClosedSmoothRiemannianMetric 3 M} {x : M}
    {p₁ p₂ : RoundSphere3}
    (L₁ : CartanMap.TangentAlignment g x p₁)
    (L₂ : CartanMap.TangentAlignment g x p₂)
    (hp : p₁ = p₂)
    (hclm : (L₁.toContinuousLinearEquiv : E →L[ℝ] E) =
      (L₂.toContinuousLinearEquiv : E →L[ℝ] E)) :
    HEq L₁ L₂ := by
  subst p₂
  apply heq_of_eq
  apply DFunLike.coe_injective
  funext u
  exact DFunLike.congr_fun hclm u

/-- Supplied-family alignments built over the same geometric predecessor have
the same dependent value when their target values and the two endpoint
derivative equivalences agree.  The target families themselves do not enter
the induced-alignment formula. -/
theorem retarget_alignment_heq
    {g : ClosedSmoothRiemannianMetric 3 M}
    {F₁ F₂ : Family} {s : CartanChain.ChainState g} {z : M}
    (d₁ : Data F₁ (ChainState.retarget F₁ s) z)
    (d₂ : Data F₂ (ChainState.retarget F₂ s) z)
    (hmap : (ChainState.retarget F₁ s).map z =
      (ChainState.retarget F₂ s).map z)
    (hA : d₁.A = d₂.A) (hB : d₁.B = d₂.B) :
    HEq d₁.alignment d₂.alignment := by
  have hclm :
      (d₁.alignment.toContinuousLinearEquiv : E →L[ℝ] E) =
        (d₂.alignment.toContinuousLinearEquiv : E →L[ℝ] E) := by
    let zSource : E := extChartAt I z z
    have hzSource : zSource ∈ (extChartAt I z).target := by
      simpa [zSource] using
        (extChartAt I z).map_source (mem_extChartAt_source z)
    have hsourceSymm : (extChartAt I z).symm zSource = z := by
      simpa [zSource] using
        (extChartAt I z).left_inv (mem_extChartAt_source z)
    have hySource :
        (extChartAt I z).symm zSource ∈
          (extChartAt I s.anchor).source := by
      rw [hsourceSymm]
      exact d₁.source_mem_oldChart
    let sourceCLM : E →L[ℝ] E :=
      GeodesicTransport.chartTransitionMFDeriv
        (x₀ := z) (y₀ := s.anchor) zSource
    have hsourceInv : sourceCLM.IsInvertible := by
      dsimp [sourceCLM, GeodesicTransport.chartTransitionMFDeriv]
      exact
        (isInvertible_mfderiv_extChartAt hySource).comp
          (isInvertible_mfderivWithin_extChartAt_symm hzSource)
    let S : E ≃L[ℝ] E :=
      InducedAlignment.continuousLinearEquivOfInvertible sourceCLM hsourceInv
    let p₁ : RoundSphere3 := (ChainState.retarget F₁ s).map z
    let p₂ : RoundSphere3 := (ChainState.retarget F₂ s).map z
    have hp : p₁ = p₂ := hmap
    let zTarget₁ : E := extChartAt I p₁ p₁
    have hzTarget₁ : zTarget₁ ∈ (extChartAt I p₁).target := by
      simpa [zTarget₁] using
        (extChartAt I p₁).map_source (mem_extChartAt_source p₁)
    have htargetSymm₁ : (extChartAt I p₁).symm zTarget₁ = p₁ := by
      simpa [zTarget₁] using
        (extChartAt I p₁).left_inv (mem_extChartAt_source p₁)
    have hyTarget₁ :
        (extChartAt I p₁).symm zTarget₁ ∈
          (extChartAt I s.target).source := by
      rw [htargetSymm₁]
      exact d₁.target_mem_oldChart
    let targetCLM₁ : E →L[ℝ] E :=
      GeodesicTransport.chartTransitionMFDeriv
        (x₀ := p₁) (y₀ := s.target) zTarget₁
    have htargetInv₁ : targetCLM₁.IsInvertible := by
      dsimp [targetCLM₁, GeodesicTransport.chartTransitionMFDeriv]
      exact
        (isInvertible_mfderiv_extChartAt hyTarget₁).comp
          (isInvertible_mfderivWithin_extChartAt_symm hzTarget₁)
    let T₁ : E ≃L[ℝ] E :=
      InducedAlignment.continuousLinearEquivOfInvertible targetCLM₁ htargetInv₁
    have hT₁coe : (T₁ : E →L[ℝ] E) = targetCLM₁ := by
      simpa [T₁, InducedAlignment.continuousLinearEquivOfInvertible] using
        Classical.choose_spec htargetInv₁
    let zTarget₂ : E := extChartAt I p₂ p₂
    have hzTarget₂ : zTarget₂ ∈ (extChartAt I p₂).target := by
      simpa [zTarget₂] using
        (extChartAt I p₂).map_source (mem_extChartAt_source p₂)
    have htargetSymm₂ : (extChartAt I p₂).symm zTarget₂ = p₂ := by
      simpa [zTarget₂] using
        (extChartAt I p₂).left_inv (mem_extChartAt_source p₂)
    have hyTarget₂ :
        (extChartAt I p₂).symm zTarget₂ ∈
          (extChartAt I s.target).source := by
      rw [htargetSymm₂]
      exact d₂.target_mem_oldChart
    let targetCLM₂ : E →L[ℝ] E :=
      GeodesicTransport.chartTransitionMFDeriv
        (x₀ := p₂) (y₀ := s.target) zTarget₂
    have htargetInv₂ : targetCLM₂.IsInvertible := by
      dsimp [targetCLM₂, GeodesicTransport.chartTransitionMFDeriv]
      exact
        (isInvertible_mfderiv_extChartAt hyTarget₂).comp
          (isInvertible_mfderivWithin_extChartAt_symm hzTarget₂)
    let T₂ : E ≃L[ℝ] E :=
      InducedAlignment.continuousLinearEquivOfInvertible targetCLM₂ htargetInv₂
    have hT₂coe : (T₂ : E →L[ℝ] E) = targetCLM₂ := by
      simpa [T₂, InducedAlignment.continuousLinearEquivOfInvertible] using
        Classical.choose_spec htargetInv₂
    have htargetCLM : targetCLM₁ = targetCLM₂ := by
      change
        GeodesicTransport.chartTransitionMFDeriv
            (x₀ := p₁) (y₀ := s.target) (extChartAt I p₁ p₁) =
          GeodesicTransport.chartTransitionMFDeriv
            (x₀ := p₂) (y₀ := s.target) (extChartAt I p₂ p₂)
      exact congrArg
        (fun p : RoundSphere3 ↦
          GeodesicTransport.chartTransitionMFDeriv
            (x₀ := p) (y₀ := s.target) (extChartAt I p p)) hp
    have hT : T₁ = T₂ := by
      apply ContinuousLinearEquiv.coe_injective
      exact hT₁coe.trans (htargetCLM.trans hT₂coe.symm)
    apply ContinuousLinearMap.ext
    intro u
    simp only [Data.alignment,
      CartanTargetExponential.inducedTangentAlignmentOfCoordinatePullback]
    change T₁.symm
        (((d₁.A.symm.trans s.alignment.toContinuousLinearEquiv).trans d₁.B)
          (S u)) =
      T₂.symm
        (((d₂.A.symm.trans s.alignment.toContinuousLinearEquiv).trans d₂.B)
          (S u))
    rw [hA, hB, hT]
  exact tangentAlignment_heq_of_target_eq_of_clm_eq
    d₁.alignment d₂.alignment hmap hclm

/-- Fieldwise equality constructor for the legacy chain-state structure. -/
private theorem chainState_eq_of_target_eq_of_alignment_heq
    {g : ClosedSmoothRiemannianMetric 3 M} {x : M}
    {p₁ p₂ : RoundSphere3}
    {L₁ : CartanMap.TangentAlignment g x p₁}
    {L₂ : CartanMap.TangentAlignment g x p₂}
    (hp : p₁ = p₂) (hL : HEq L₁ L₂) :
    (CartanChain.ChainState.mk x p₁ L₁ : CartanChain.ChainState g) =
      CartanChain.ChainState.mk x p₂ L₂ := by
  subst p₂
  cases hL
  rfl

/-- A canonical successor datum together with its retained generic successor
comparison. -/
structure TransferredSuccessorPackage
    {g : ClosedSmoothRiemannianMetric 3 M}
    (s : CartanChain.ChainState g) (z : M) where
  canonicalData : Data canonicalFamily (ChainState.retarget canonicalFamily s) z
  comparison : GenericSuccessorComparison canonicalData

/-- One canonical step with the generic comparison indexed directly by its
actual canonical predecessor state. -/
structure CanonicalComparedStep
    {g : ClosedSmoothRiemannianMetric 3 M}
    (s : ChainState canonicalFamily g) (z : M) where
  canonicalData : Data canonicalFamily s z
  comparison : GenericSuccessorComparison canonicalData

/-- Reindex a transferred package from the rebuilt canonical state to the
actual canonical state whose geometric fields it forgets. -/
def TransferredSuccessorPackage.toCanonicalComparedStep
    {g : ClosedSmoothRiemannianMetric 3 M}
    {s : ChainState canonicalFamily g} {z : M}
    (package : TransferredSuccessorPackage (canonicalToGenericState s) z) :
    CanonicalComparedStep s z := by
  cases s
  exact
    { canonicalData := package.canonicalData
      comparison := package.comparison }

/-- Transfer one generic differential datum to the canonical family while
retaining all information needed to compare the induced successors. -/
def transferDataWithProvenance
    {g : ClosedSmoothRiemannianMetric 3 M}
    {s : CartanChain.ChainState g} {z : M}
    (d : DifferentialInducedSuccessor.Data s z)
    (htargetCanonical :
      s.alignment d.v ∈ (canonicalFamily.chart s.target).source)
    (hchart :
      (genericFamily.chart s.target : E → E) =ᶠ[nhds (s.alignment d.v)]
        (canonicalFamily.chart s.target : E → E)) :
    TransferredSuccessorPackage s z := by
  let canonicalData :
      Data canonicalFamily (ChainState.retarget canonicalFamily s) z :=
    transferData d htargetCanonical hchart
  let chart : GenericChartGermProvenance canonicalData :=
    { target_vector_mem := by
        exact d.target_vector_mem
      chart_eventuallyEq := by
        exact hchart.symm }
  let genericSupplied : Data genericFamily (ChainState.ofGeneric s) z :=
    Data.ofGeneric d
  have hmap :
      (ChainState.retarget canonicalFamily s).map z = s.map z := by
    simpa [canonicalToGenericState, ChainState.retarget] using chart.map_eq
  have hcanonicalGeneric : HEq canonicalData.alignment genericSupplied.alignment := by
    exact retarget_alignment_heq canonicalData genericSupplied hmap rfl rfl
  have halignment : HEq canonicalData.alignment d.alignment :=
    hcanonicalGeneric.trans (heq_of_eq (ofGeneric_alignment_eq d))
  have hsuccessor :
      canonicalToGenericState canonicalData.successor = d.successor := by
    exact chainState_eq_of_target_eq_of_alignment_heq hmap halignment
  exact
    { canonicalData := canonicalData
      comparison :=
        { chart := chart
          genericData := by
            simpa [canonicalToGenericState, ChainState.retarget] using d
          successor_eq := by
            simpa [canonicalToGenericState, ChainState.retarget] using hsuccessor } }

/-- Ball-form provenance-retaining transfer. -/
def transferDataWithProvenance_of_aligned_norm_lt
    {g : ClosedSmoothRiemannianMetric 3 M}
    {s : CartanChain.ChainState g} {z : M}
    (d : DifferentialInducedSuccessor.Data s z)
    {r : ℝ}
    (hEq : ∀ v : E, ‖v‖ < r →
      genericFamily.chart s.target v = canonicalFamily.chart s.target v)
    (hsource : Metric.ball (0 : E) r ⊆
      (canonicalFamily.chart s.target).source)
    (haligned : ‖s.alignment d.v‖ < r) :
    TransferredSuccessorPackage s z :=
  transferDataWithProvenance d
    (hsource (by
      simpa [Metric.mem_ball, dist_eq_norm] using haligned))
    (genericFamily_chart_eventuallyEq_canonicalFamily_of_norm_lt
      hEq haligned)

section Curvature

variable [T2Space M] [CompactSpace M] [ConnectedSpace M]

/-- Constant curvature supplies a metric neighborhood in which every
canonical successor is produced together with the generic datum and exact
successor comparison from which it arose. -/
theorem exists_metric_transferredSuccessorPackage_radius_all_alignments_fixed_anchors_of_curvature
    (g : ClosedSmoothRiemannianMetric 3 M)
    (hcurv : HasConstantSectionalCurvature3 g 1)
    (x : M) (p : RoundSphere3) :
    letI : MetricSpace M := g.toMetricSpace
    ∃ epsilon > (0 : ℝ),
      ∀ (L : CartanMap.TangentAlignment g x p) (z : M),
        dist z x < epsilon →
          Nonempty
            (TransferredSuccessorPackage
              (CartanChain.ChainState.mk x p L) z) := by
  letI : MetricSpace M := g.toMetricSpace
  rcases
      CartanAtlasRootedPathCurvatureSuccessorRadius.exists_metric_successor_data_radius_all_alignments_fixed_anchors_of_curvature
        g hcurv x p with
    ⟨genericRadius, hgenericRadius, hgenericData⟩
  rcases exists_genericFamily_chart_eq_canonicalFamily_on_ball p with
    ⟨equalityRadius, hequalityRadius, hchartEq⟩
  rcases RoundSphereCanonicalExponential.exists_uniform_source_target_ball with
    ⟨canonicalRadius, hcanonicalRadius, hcanonicalBalls⟩
  let targetRadius : ℝ := min equalityRadius canonicalRadius
  have htargetRadius : 0 < targetRadius :=
    lt_min hequalityRadius hcanonicalRadius
  have hchartEqTarget : ∀ v : E, ‖v‖ < targetRadius →
      genericFamily.chart p v = canonicalFamily.chart p v := by
    intro v hv
    exact hchartEq v (hv.trans_le (min_le_left _ _))
  have hcanonicalSource : Metric.ball (0 : E) targetRadius ⊆
      (canonicalFamily.chart p).source := by
    intro v hv
    have hv' : v ∈ Metric.ball (0 : E) canonicalRadius :=
      Metric.ball_subset_ball (min_le_right _ _) hv
    simpa [canonicalFamily] using (hcanonicalBalls p).1 hv'
  rcases
      RoundSphereTargetAnchorUniformity.exists_pos_uniform_tangentAlignment_operatorNorm_bound_all_targets
        g x with
    ⟨C, hC, hoperator⟩
  let vectorRadius : ℝ := targetRadius / C
  have hvectorRadius : 0 < vectorRadius := div_pos htargetRadius hC
  let eM :=
    GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x
  let normalCoordinate : M → E := fun z ↦ eM.symm ((chartAt E x) z)
  have htarget : (chartAt E x) x ∈ eM.target := by
    simpa [eM, extChartAt_coe] using
      GeodesicTransport.expAt_base_mem_expAtChartOpenPartialHomeomorph_target
        (g := g) x
  have hchart : ContinuousAt (fun z : M ↦ (chartAt E x) z) x := by
    simpa [extChartAt_coe] using
      continuousAt_extChartAt («I» := I) x
  have hnormalContinuous : ContinuousAt normalCoordinate x :=
    (eM.continuousAt_symm htarget).comp hchart
  have hnormalZero : normalCoordinate x = (0 : E) := by
    simpa [normalCoordinate, eM] using
      CartanMap.expAtChartOpenPartialHomeomorph_symm_chart_anchor_eq_zero g x
  have hnormalNhds :
      normalCoordinate ⁻¹' Metric.ball (0 : E) vectorRadius ∈ nhds x := by
    apply hnormalContinuous.preimage_mem_nhds
    rw [hnormalZero]
    exact Metric.ball_mem_nhds (0 : E) hvectorRadius
  rcases Metric.mem_nhds_iff.mp hnormalNhds with
    ⟨coordinateRadius, hcoordinateRadius, hcoordinate⟩
  let epsilon : ℝ := min genericRadius coordinateRadius
  have hepsilon : 0 < epsilon :=
    lt_min hgenericRadius hcoordinateRadius
  refine ⟨epsilon, hepsilon, ?_⟩
  intro L z hdist
  have hgenericDist : dist z x < genericRadius :=
    hdist.trans_le (min_le_left _ _)
  rcases hgenericData L z hgenericDist with ⟨d⟩
  have hzCoordinateBall : z ∈ Metric.ball x coordinateRadius := by
    rw [Metric.mem_ball]
    exact hdist.trans_le (min_le_right _ _)
  have hnormalBall :
      normalCoordinate z ∈ Metric.ball (0 : E) vectorRadius :=
    hcoordinate hzCoordinateBall
  have hnormalNorm : ‖normalCoordinate z‖ < vectorRadius := by
    simpa [Metric.mem_ball, dist_eq_norm] using hnormalBall
  have hsourceCoordinate : (chartAt E x) z = eM d.v := by
    simpa [eM, extChartAt_coe] using d.source_coordinate
  have hdv : d.v = normalCoordinate z := by
    calc
      d.v = eM.symm (eM d.v) := (eM.left_inv d.source_vector_mem).symm
      _ = eM.symm ((chartAt E x) z) := by rw [hsourceCoordinate]
      _ = normalCoordinate z := rfl
  have hdvNorm : ‖d.v‖ < vectorRadius := by
    rw [hdv]
    exact hnormalNorm
  let A : E →L[ℝ] E :=
    L.toContinuousLinearEquiv.toContinuousLinearMap
  have haligned : ‖L d.v‖ < targetRadius := by
    calc
      ‖L d.v‖ = ‖A d.v‖ := rfl
      _ ≤ ‖A‖ * ‖d.v‖ := A.le_opNorm d.v
      _ ≤ C * ‖d.v‖ := by
        exact mul_le_mul_of_nonneg_right (hoperator p L) (norm_nonneg d.v)
      _ < C * vectorRadius := mul_lt_mul_of_pos_left hdvNorm hC
      _ = targetRadius := by
        dsimp only [vectorRadius]
        exact mul_div_cancel₀ targetRadius (ne_of_gt hC)
  exact ⟨transferDataWithProvenance_of_aligned_norm_lt
    d hchartEqTarget hcanonicalSource haligned⟩

end Curvature

end CartanCanonicalFamilySuccessorProvenance
end Poincare
