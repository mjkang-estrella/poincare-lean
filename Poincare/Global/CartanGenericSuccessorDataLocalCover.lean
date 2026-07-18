import Poincare.Global.CartanCanonicalRootedDirectGenericNeighborhoodRecognition
import Poincare.Global.CartanSourceExponentialLocalFamilyTransport

/-!
# Chart-local cover for the generic Cartan successor-data locus

The direct rooted recognition theorem only consumes the legacy generic
`UniversalSuccessorDataNeighborhood`.  Passing through the canonical target
family and then postulating a canonical-to-generic bridge is therefore not
intrinsic to that consumer.

This file records the exact chart-local output that constructs the generic
neighborhood directly.  Near each source/target anchor pair `(x₀, p₀)` it
asks for

* one open, jointly continuous source-normal `LocalFamily` around `x₀`;
* one open target neighborhood around `p₀`; and
* one positive normal radius on which every tangent alignment carries actual
  legacy generic successor data.

Allowing the target neighborhood and radius to depend on `(x₀, p₀)` is
important: the global neighborhood consumer needs only a local cover of the
complete diagonal, not one radius valid for every sphere target in a fixed
source chart.

The fixed-chart specialization uses the raw product inverse supplied by the
parameterized inverse-function theorem.  It mentions neither the preferred
generic source normal nor any joint continuity of independently chosen
preferred charts.  Constant curvature already discharges the complete
fixed-anchor vertical slice, by the existing interval/naturality theorem.
The sole residual is persistence of that data while the source and target
anchors move in the displayed fixed-chart family.
-/

noncomputable section

set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 180000
set_option linter.unusedSectionVars false

open Filter Function Metric Set
open scoped Manifold ContDiff Topology RealInnerProductSpace NNReal

namespace Poincare
namespace CartanGenericSuccessorDataLocalCover

universe u

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M]
variable [ChartedSpace E M]
variable [IsManifold I ∞ M]

open CartanSourceExponential
open CartanSourceExponentialLocalFamilyTransport
open CartanAtlasRootedPathCurvatureSuccessorRadius
open CartanCanonicalRootedDirectGenericNeighborhoodRecognition

/-! ## Target-local controlled loci -/

/-- Restrict a chart-local controlled successor locus to an open set of
sphere target anchors. -/
def controlledGenericSuccessorLocusOn
    {g : ClosedSmoothRiemannianMetric 3 M}
    (A : LocalFamily g) (targets : Set RoundSphere3) (radius : ℝ) :
    Set ((M × RoundSphere3) × M) :=
  A.controlledSuccessorLocus radius ∩
    (fun q : (M × RoundSphere3) × M ↦ q.1.2) ⁻¹' targets

/-- The target-local controlled successor locus is open whenever its target
set is open. -/
theorem isOpen_controlledGenericSuccessorLocusOn
    {g : ClosedSmoothRiemannianMetric 3 M}
    (A : LocalFamily g) {targets : Set RoundSphere3}
    (htargets : IsOpen targets) (radius : ℝ) :
    IsOpen (controlledGenericSuccessorLocusOn A targets radius) := by
  exact (A.isOpen_controlledSuccessorLocus radius).inter
    (htargets.preimage (continuous_snd.comp continuous_fst))

/-- Restrict both the moving-anchor patch and the endpoint patch of a local
family.  Requiring anchors to lie in the endpoint patch preserves the whole
restricted diagonal. -/
def restrictAnchorEndpointPatches
    {g : ClosedSmoothRiemannianMetric 3 M}
    (A : LocalFamily g)
    (sourcePatch endpointPatch : Set M)
    (hsourcePatch : IsOpen sourcePatch)
    (hendpointPatch : IsOpen endpointPatch) : LocalFamily g where
  anchors := A.anchors ∩ sourcePatch ∩ endpointPatch
  isOpen_anchors :=
    (A.isOpen_anchors.inter hsourcePatch).inter hendpointPatch
  sourceLocus :=
    A.sourceLocus ∩ ((sourcePatch ∩ endpointPatch) ×ˢ endpointPatch)
  isOpen_sourceLocus :=
    A.isOpen_sourceLocus.inter
      ((hsourcePatch.inter hendpointPatch).prod hendpointPatch)
  sourceLocus_fst q hq :=
    ⟨⟨A.sourceLocus_fst q hq.1, hq.2.1.1⟩, hq.2.1.2⟩
  normal := A.normal
  continuousOn_normal := A.continuousOn_normal.mono (fun _q hq ↦ hq.1)
  diagonal_mem x hx :=
    ⟨A.diagonal_mem x hx.1.1, ⟨⟨hx.1.2, hx.2⟩, hx.2⟩⟩
  normal_diagonal x hx := A.normal_diagonal x hx.1.1

@[simp]
theorem restrictAnchorEndpointPatches_anchors
    {g : ClosedSmoothRiemannianMetric 3 M}
    (A : LocalFamily g)
    (sourcePatch endpointPatch : Set M)
    (hsourcePatch : IsOpen sourcePatch)
    (hendpointPatch : IsOpen endpointPatch) :
    (restrictAnchorEndpointPatches A sourcePatch endpointPatch
        hsourcePatch hendpointPatch).anchors =
      A.anchors ∩ sourcePatch ∩ endpointPatch :=
  rfl

@[simp]
theorem restrictAnchorEndpointPatches_sourceLocus
    {g : ClosedSmoothRiemannianMetric 3 M}
    (A : LocalFamily g)
    (sourcePatch endpointPatch : Set M)
    (hsourcePatch : IsOpen sourcePatch)
    (hendpointPatch : IsOpen endpointPatch) :
    (restrictAnchorEndpointPatches A sourcePatch endpointPatch
        hsourcePatch hendpointPatch).sourceLocus =
      A.sourceLocus ∩
        ((sourcePatch ∩ endpointPatch) ×ˢ endpointPatch) :=
  rfl

@[simp]
theorem restrictAnchorEndpointPatches_normal
    {g : ClosedSmoothRiemannianMetric 3 M}
    (A : LocalFamily g)
    (sourcePatch endpointPatch : Set M)
    (hsourcePatch : IsOpen sourcePatch)
    (hendpointPatch : IsOpen endpointPatch) (q : M × M) :
    (restrictAnchorEndpointPatches A sourcePatch endpointPatch
        hsourcePatch hendpointPatch).normal q = A.normal q :=
  rfl

/-- Uniform legacy generic successor data on one chart-local source family
and one target-anchor patch. -/
def LocalUniformNormalGenericSuccessorDataOn
    {g : ClosedSmoothRiemannianMetric 3 M}
    (A : LocalFamily g) (targets : Set RoundSphere3) : Prop :=
  ∃ radius > (0 : ℝ),
    ∀ (x : M) (p : RoundSphere3), p ∈ targets →
      ∀ (L : CartanMap.TangentAlignment g x p) (z : M),
        (x, z) ∈ A.sourceLocus →
        ‖A.normal (x, z)‖ < radius →
          Nonempty
            (DifferentialInducedSuccessor.Data
              (CartanChain.ChainState.mk x p L) z)

/-- A target-local normal-data producer puts its controlled open locus inside
the legacy generic universal data locus. -/
theorem controlledGenericSuccessorLocusOn_subset_universalData
    {g : ClosedSmoothRiemannianMetric 3 M}
    (A : LocalFamily g) (targets : Set RoundSphere3) {radius : ℝ}
    (hdata :
      ∀ (x : M) (p : RoundSphere3), p ∈ targets →
        ∀ (L : CartanMap.TangentAlignment g x p) (z : M),
          (x, z) ∈ A.sourceLocus →
          ‖A.normal (x, z)‖ < radius →
            Nonempty
              (DifferentialInducedSuccessor.Data
                (CartanChain.ChainState.mk x p L) z)) :
    controlledGenericSuccessorLocusOn A targets radius ⊆
      CartanAtlasRootedPathCurvatureSuccessorRadius.UniversalSuccessorDataLocus
        g := by
  rintro ⟨⟨x, p⟩, z⟩ ⟨hz, hp⟩ L
  exact hdata x p hp L z hz.1 (by
    simpa [LocalFamily.controlledSourceLocus, Metric.mem_ball, dist_eq_norm]
      using hz.2)

/-- Locus-inclusion characterization of target-local uniform generic data. -/
theorem localUniformNormalGenericSuccessorDataOn_iff_controlledLocus_subset
    {g : ClosedSmoothRiemannianMetric 3 M}
    (A : LocalFamily g) (targets : Set RoundSphere3) :
    LocalUniformNormalGenericSuccessorDataOn A targets ↔
      ∃ radius > (0 : ℝ),
        controlledGenericSuccessorLocusOn A targets radius ⊆
          CartanAtlasRootedPathCurvatureSuccessorRadius.UniversalSuccessorDataLocus
            g := by
  constructor
  · rintro ⟨radius, hradius, hdata⟩
    exact ⟨radius, hradius,
      controlledGenericSuccessorLocusOn_subset_universalData
        A targets hdata⟩
  · rintro ⟨radius, hradius, hsubset⟩
    refine ⟨radius, hradius, ?_⟩
    intro x p hp L z hzSource hzNorm
    have hmem : ((x, p), z) ∈
        controlledGenericSuccessorLocusOn A targets radius := by
      refine ⟨⟨hzSource, ?_⟩, hp⟩
      simpa [LocalFamily.controlledSourceLocus, Metric.mem_ball,
        dist_eq_norm] using hzNorm
    exact hsubset hmem L

/-! ## The exact local generic-data cover -/

/--
The exact local cover of the generic successor-data locus.

Both geometric point parameters are localized, while tangent alignments stay
under the dependent universal quantifier.  This is strictly weaker than
requiring one source chart and one radius to work for every sphere target.
-/
def LocalGenericSuccessorDataCover
    (g : ClosedSmoothRiemannianMetric 3 M) : Prop :=
  ∀ (x₀ : M) (p₀ : RoundSphere3),
    ∃ (A : LocalFamily g) (targets : Set RoundSphere3),
      x₀ ∈ A.anchors ∧ IsOpen targets ∧ p₀ ∈ targets ∧
        LocalUniformNormalGenericSuccessorDataOn A targets

/-- Fully expanded controlled-locus characterization of the exact local
cover. -/
theorem localGenericSuccessorDataCover_iff_controlledLocusCover
    (g : ClosedSmoothRiemannianMetric 3 M) :
    LocalGenericSuccessorDataCover g ↔
      ∀ (x₀ : M) (p₀ : RoundSphere3),
        ∃ (A : LocalFamily g) (targets : Set RoundSphere3),
          x₀ ∈ A.anchors ∧ IsOpen targets ∧ p₀ ∈ targets ∧
            ∃ radius > (0 : ℝ),
              controlledGenericSuccessorLocusOn A targets radius ⊆
                CartanAtlasRootedPathCurvatureSuccessorRadius.UniversalSuccessorDataLocus
                  g := by
  constructor
  · intro hcover x₀ p₀
    rcases hcover x₀ p₀ with
      ⟨A, targets, hx₀, hopen, hp₀, hdata⟩
    rcases
        (localUniformNormalGenericSuccessorDataOn_iff_controlledLocus_subset
          A targets).mp hdata with
      ⟨radius, hradius, hsubset⟩
    exact ⟨A, targets, hx₀, hopen, hp₀,
      radius, hradius, hsubset⟩
  · intro hcover x₀ p₀
    rcases hcover x₀ p₀ with
      ⟨A, targets, hx₀, hopen, hp₀,
        radius, hradius, hsubset⟩
    refine ⟨A, targets, hx₀, hopen, hp₀, ?_⟩
    exact
      (localUniformNormalGenericSuccessorDataOn_iff_controlledLocus_subset
        A targets).mpr ⟨radius, hradius, hsubset⟩

/-- The exact local cover directly supplies the legacy generic
diagonal-neighborhood contract. -/
theorem LocalGenericSuccessorDataCover.toUniversalSuccessorDataNeighborhood
    {g : ClosedSmoothRiemannianMetric 3 M}
    (hcover : LocalGenericSuccessorDataCover g) :
    CartanAtlasRootedPathCurvatureSuccessorRadius.UniversalSuccessorDataNeighborhood
      g := by
  rw [CartanAtlasRootedPathCurvatureSuccessorRadius.UniversalSuccessorDataNeighborhood]
  apply mem_nhdsSet_iff_forall.mpr
  intro graphPoint hgraphPoint
  rcases hgraphPoint with ⟨⟨x, p⟩, _hxp, rfl⟩
  rcases hcover x p with
    ⟨A, targets, hxA, hopenTargets, hpTargets, hlocal⟩
  rcases hlocal with ⟨radius, hradius, hdata⟩
  let W : Set ((M × RoundSphere3) × M) :=
    controlledGenericSuccessorLocusOn A targets radius
  have hopenW : IsOpen W :=
    isOpen_controlledGenericSuccessorLocusOn A hopenTargets radius
  have hgraphW : ((x, p), x) ∈ W := by
    refine ⟨⟨A.diagonal_mem x hxA, ?_⟩, hpTargets⟩
    change A.normal (x, x) ∈ Metric.ball (0 : E) radius
    rw [A.normal_diagonal x hxA]
    exact Metric.mem_ball_self hradius
  have hWsubset : W ⊆
      CartanAtlasRootedPathCurvatureSuccessorRadius.UniversalSuccessorDataLocus
        g :=
    controlledGenericSuccessorLocusOn_subset_universalData A targets hdata
  exact Filter.mem_of_superset (hopenW.mem_nhds hgraphW) hWsubset

/-- Conversely, every legacy generic diagonal neighborhood has a cover of
the displayed fixed-chart form.  The proof takes a product neighborhood at
each diagonal point, restricts an arbitrary raw fixed-chart inverse to its
source and endpoint patches, and uses any positive normal radius. -/
theorem localGenericSuccessorDataCover_of_universalSuccessorDataNeighborhood
    {g : ClosedSmoothRiemannianMetric 3 M}
    (hneighborhood :
      CartanAtlasRootedPathCurvatureSuccessorRadius.UniversalSuccessorDataNeighborhood
        g) :
    LocalGenericSuccessorDataCover g := by
  rw [localGenericSuccessorDataCover_iff_controlledLocusCover]
  intro x₀ p₀
  let graphPoint : (M × RoundSphere3) × M := ((x₀, p₀), x₀)
  have hgraphPoint : graphPoint ∈
      CartanAtlasRootedPathCurvatureSuccessorRadius.successorParameterDiagonal
        (M := M) :=
    ⟨(x₀, p₀), Set.mem_univ _, rfl⟩
  have hdataNhds :
      CartanAtlasRootedPathCurvatureSuccessorRadius.UniversalSuccessorDataLocus
          g ∈ nhds graphPoint :=
    mem_nhdsSet_iff_forall.mp hneighborhood graphPoint hgraphPoint
  rcases mem_nhds_prod_iff.mp hdataNhds with
    ⟨sourceTargetSet, hsourceTargetSet,
      endpointSet, hendpointSet, hproductData⟩
  rcases mem_nhds_prod_iff.mp hsourceTargetSet with
    ⟨sourceSet, hsourceSet, targetSet, htargetSet,
      hsourceTargetProduct⟩
  rcases _root_.mem_nhds_iff.mp hsourceSet with
    ⟨sourcePatch, hsourcePatchSubset, hopenSourcePatch,
      hx₀SourcePatch⟩
  rcases _root_.mem_nhds_iff.mp htargetSet with
    ⟨targetPatch, htargetPatchSubset, hopenTargetPatch,
      hp₀TargetPatch⟩
  rcases _root_.mem_nhds_iff.mp hendpointSet with
    ⟨endpointPatch, hendpointPatchSubset, hopenEndpointPatch,
      hx₀EndpointPatch⟩
  rcases exists_fixedChartAnchorEndpointPackage g x₀ with ⟨C⟩
  let A : LocalFamily g :=
    restrictAnchorEndpointPatches C.rawLocalFamily
      sourcePatch endpointPatch hopenSourcePatch hopenEndpointPatch
  have hx₀A : x₀ ∈ A.anchors := by
    exact ⟨⟨C.center_mem_rawLocalFamily_anchors,
      hx₀SourcePatch⟩, hx₀EndpointPatch⟩
  refine ⟨A, targetPatch, hx₀A, hopenTargetPatch,
    hp₀TargetPatch, 1, by norm_num, ?_⟩
  rintro ⟨⟨x, p⟩, z⟩ hcontrolled
  have hpTargetPatch : p ∈ targetPatch := hcontrolled.2
  have hxzSource : (x, z) ∈ A.sourceLocus := hcontrolled.1.1
  have hxSourcePatch : x ∈ sourcePatch := hxzSource.2.1.1
  have hzEndpointPatch : z ∈ endpointPatch := hxzSource.2.2
  have hxpSourceTarget : (x, p) ∈ sourceTargetSet :=
    hsourceTargetProduct
      ⟨hsourcePatchSubset hxSourcePatch,
        htargetPatchSubset hpTargetPatch⟩
  exact hproductData
    ⟨hxpSourceTarget, hendpointPatchSubset hzEndpointPatch⟩

/-- The chart-local cover is therefore logically equivalent to the legacy
generic diagonal-neighborhood contract. -/
theorem localGenericSuccessorDataCover_iff_universalSuccessorDataNeighborhood
    (g : ClosedSmoothRiemannianMetric 3 M) :
    LocalGenericSuccessorDataCover g ↔
      CartanAtlasRootedPathCurvatureSuccessorRadius.UniversalSuccessorDataNeighborhood
        g := by
  constructor
  · exact LocalGenericSuccessorDataCover.toUniversalSuccessorDataNeighborhood
  · exact localGenericSuccessorDataCover_of_universalSuccessorDataNeighborhood

/-- The former canonical-neighborhood plus existence-only bridge projects to
the single exact local generic-data cover.  No selected successor comparison
is retained. -/
theorem localGenericSuccessorDataCover_of_canonicalNeighborhood_genericBridge
    {g : ClosedSmoothRiemannianMetric 3 M}
    (hcanonical :
      CartanTargetExponential.UniversalSuccessorDataNeighborhood
        CartanTargetExponential.canonicalFamily g)
    (hbridge : CanonicalDataNeighborhoodToGenericDataNeighborhood g) :
    LocalGenericSuccessorDataCover g :=
  localGenericSuccessorDataCover_of_universalSuccessorDataNeighborhood
    (hbridge hcanonical)

/-! ## The fixed-chart residual -/

/--
The direct fixed-chart generic-data persistence contract.

The product inverse-function package already supplies the open moving-source
family and its continuous raw inverse velocity.  The only remaining request
is a target-local positive controlled locus consisting of actual legacy
generic successor data.  No comparison with a preferred source chart and no
canonical-family datum occur in the statement.
-/
def FixedChartLocalGenericDataPersistence
    (g : ClosedSmoothRiemannianMetric 3 M) : Prop :=
  ∀ (x₀ : M) (p₀ : RoundSphere3),
    ∃ (C : FixedChartAnchorEndpointPackage g x₀)
        (targets : Set RoundSphere3),
      IsOpen targets ∧ p₀ ∈ targets ∧
        ∃ radius > (0 : ℝ),
          controlledGenericSuccessorLocusOn C.rawLocalFamily
              targets radius ⊆
            CartanAtlasRootedPathCurvatureSuccessorRadius.UniversalSuccessorDataLocus
              g

/-- Fixed-chart persistence gives the exact local generic-data cover. -/
theorem FixedChartLocalGenericDataPersistence.toLocalGenericSuccessorDataCover
    {g : ClosedSmoothRiemannianMetric 3 M}
    (hfixed : FixedChartLocalGenericDataPersistence g) :
    LocalGenericSuccessorDataCover g := by
  rw [localGenericSuccessorDataCover_iff_controlledLocusCover]
  intro x₀ p₀
  rcases hfixed x₀ p₀ with
    ⟨C, targets, hopen, hp₀, radius, hradius, hsubset⟩
  exact ⟨C.rawLocalFamily, targets,
    C.center_mem_rawLocalFamily_anchors, hopen, hp₀,
    radius, hradius, hsubset⟩

/-- Direct global-neighborhood consumer for the fixed-chart residual. -/
theorem universalSuccessorDataNeighborhood_of_fixedChartLocalGenericDataPersistence
    {g : ClosedSmoothRiemannianMetric 3 M}
    (hfixed : FixedChartLocalGenericDataPersistence g) :
    CartanAtlasRootedPathCurvatureSuccessorRadius.UniversalSuccessorDataNeighborhood
      g :=
  hfixed.toLocalGenericSuccessorDataCover.toUniversalSuccessorDataNeighborhood

/-! ## What constant curvature already proves -/

section Curvature

variable [T2Space M] [CompactSpace M] [ConnectedSpace M]

/-- Constant-curvature interval naturality already gives an open endpoint
patch at each *fixed* source/target anchor pair, simultaneously for every
tangent alignment. -/
theorem exists_open_vertical_genericSuccessorDataPatch_of_curvature
    (g : ClosedSmoothRiemannianMetric 3 M)
    (hcurv : HasConstantSectionalCurvature3 g 1)
    (x : M) (p : RoundSphere3) :
    letI : MetricSpace M := g.toMetricSpace
    ∃ endpoints : Set M,
      IsOpen endpoints ∧ x ∈ endpoints ∧
        ∀ (L : CartanMap.TangentAlignment g x p) (z : M),
          z ∈ endpoints →
            Nonempty
              (DifferentialInducedSuccessor.Data
                (CartanChain.ChainState.mk x p L) z) := by
  letI : MetricSpace M := g.toMetricSpace
  rcases
      exists_metric_successor_data_radius_all_alignments_fixed_anchors_of_curvature
        g hcurv x p with
    ⟨radius, hradius, hdata⟩
  refine ⟨Metric.ball x radius, Metric.isOpen_ball,
    Metric.mem_ball_self hradius, ?_⟩
  intro L z hz
  exact hdata L z (by simpa [Metric.mem_ball] using hz)

/-- The fixed-chart product inverse and the curvature construction jointly
give a center-endpoint patch at every fixed target.  Thus the residual in
`FixedChartLocalGenericDataPersistence` is exactly persistence under moving
source and target anchors, not another center-slice existence theorem. -/
theorem exists_open_fixedChartCenter_genericSuccessorDataPatch_of_curvature
    (g : ClosedSmoothRiemannianMetric 3 M)
    (hcurv : HasConstantSectionalCurvature3 g 1)
    (x₀ : M) (p₀ : RoundSphere3) :
    ∃ (C : FixedChartAnchorEndpointPackage g x₀)
        (endpoints : Set M),
      IsOpen endpoints ∧ x₀ ∈ endpoints ∧
        (∀ z ∈ endpoints,
          (x₀, z) ∈ C.rawLocalFamily.sourceLocus) ∧
        ∀ (L : CartanMap.TangentAlignment g x₀ p₀) (z : M),
          z ∈ endpoints →
            Nonempty
              (DifferentialInducedSuccessor.Data
                (CartanChain.ChainState.mk x₀ p₀ L) z) := by
  letI : MetricSpace M := g.toMetricSpace
  rcases exists_fixedChartAnchorEndpointPackage g x₀ with ⟨C⟩
  rcases
      exists_open_vertical_genericSuccessorDataPatch_of_curvature
        g hcurv x₀ p₀ with
    ⟨dataEndpoints, hopenData, hx₀Data, hdata⟩
  let sourceEndpoints : Set M :=
    (fun z : M ↦ (x₀, z)) ⁻¹' C.rawLocalFamily.sourceLocus
  have hopenSource : IsOpen sourceEndpoints :=
    C.rawLocalFamily.isOpen_sourceLocus.preimage (by fun_prop)
  have hx₀Source : x₀ ∈ sourceEndpoints :=
    C.rawLocalFamily.diagonal_mem x₀
      C.center_mem_rawLocalFamily_anchors
  let endpoints : Set M := sourceEndpoints ∩ dataEndpoints
  refine ⟨C, endpoints, hopenSource.inter hopenData,
    ⟨hx₀Source, hx₀Data⟩, ?_, ?_⟩
  · intro z hz
    exact hz.1
  · intro L z hz
    exact hdata L z hz.2

end Curvature

/-! ## Direct recognition adapters -/

section Recognition

variable [T2Space M] [CompactSpace M] [ConnectedSpace M]

/-- The local generic-data cover feeds direct rooted recognition without a
canonical-family neighborhood or a canonical-to-generic bridge. -/
theorem unitConstantCurvatureSphereRecognition3_of_localGenericSuccessorDataCover_jointEqualityNeighborhood
    [SecondCountableTopology M] [SimplyConnectedSpace M]
    (dataStability : ∀ (g : ClosedSmoothRiemannianMetric 3 M),
      HasConstantSectionalCurvature3 g 1 →
        LocalGenericSuccessorDataCover g)
    (equalityStability : ∀ (g : ClosedSmoothRiemannianMetric 3 M),
      HasConstantSectionalCurvature3 g 1 →
        DifferentialSuccessorJointEqualityNeighborhood.UniversalSuccessorEqualityNeighborhood
          g) :
    UnitConstantCurvatureSphereRecognition3 M := by
  apply
    unitConstantCurvatureSphereRecognition3_of_genericDataNeighborhood_jointEqualityNeighborhood
  · intro g hcurv
    exact
      (dataStability g hcurv).toUniversalSuccessorDataNeighborhood
  · exact equalityStability

/-- Fixed-chart specialization of the direct local-cover recognition
adapter. -/
theorem unitConstantCurvatureSphereRecognition3_of_fixedChartLocalGenericDataPersistence_jointEqualityNeighborhood
    [SecondCountableTopology M] [SimplyConnectedSpace M]
    (dataStability : ∀ (g : ClosedSmoothRiemannianMetric 3 M),
      HasConstantSectionalCurvature3 g 1 →
        FixedChartLocalGenericDataPersistence g)
    (equalityStability : ∀ (g : ClosedSmoothRiemannianMetric 3 M),
      HasConstantSectionalCurvature3 g 1 →
        DifferentialSuccessorJointEqualityNeighborhood.UniversalSuccessorEqualityNeighborhood
          g) :
    UnitConstantCurvatureSphereRecognition3 M := by
  apply
    unitConstantCurvatureSphereRecognition3_of_localGenericSuccessorDataCover_jointEqualityNeighborhood
  · intro g hcurv
    exact
      (dataStability g hcurv).toLocalGenericSuccessorDataCover
  · exact equalityStability

end Recognition

end CartanGenericSuccessorDataLocalCover
end Poincare
