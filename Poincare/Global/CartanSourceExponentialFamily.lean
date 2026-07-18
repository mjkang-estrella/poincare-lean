import Poincare.Global.CartanTargetExponentialFamily

/-!
# Joint source normal-coordinate families for Cartan continuation

`CartanTargetExponentialFamily` removes the independently chosen exponential
from the round-sphere target side.  The source side still uses
`GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x`, chosen
separately at every source anchor `x`.

This module isolates exactly the remaining source-anchor boundary.  A source
family is expressed intrinsically as a varying normal-coordinate partial
homeomorphism `normal x : M ⇄ E`, rather than as another family of preferred
charts.  Joint regularity says that its varying domains are open and that its
forward and inverse evaluations are continuous on those domains.

The current generic source exponential is provided as an adapter, but no
joint-regularity theorem is claimed for it.  A compactness theorem shows that
a jointly regular source family uniformly controls both membership and the
normal-vector norm near the complete source diagonal.  Combining that result
with an explicit uniform normal-coordinate Data producer yields the supplied
target-family `UniversalSuccessorDataNeighborhood`, and hence the complete
rooted prescribed-mesh consumer from the target-family module.
-/

noncomputable section

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 90000

open Filter Metric Set
open scoped Manifold ContDiff Topology RealInnerProductSpace unitInterval

namespace Poincare
namespace CartanSourceExponential

universe u

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M]
variable [ChartedSpace E M]
variable [IsManifold I ∞ M]

/--
A varying source normal-coordinate chart.  Its forward map sends manifold
points near `x` to tangent-model vectors, so the anchor maps to zero.
-/
structure Family (g : ClosedSmoothRiemannianMetric 3 M) where
  normal : M → OpenPartialHomeomorph M E
  anchor_mem_source : ∀ x, x ∈ (normal x).source
  normal_anchor : ∀ x, normal x x = (0 : E)

/-- Joint locus on which the varying source normal coordinate is defined. -/
def Family.sourceLocus {g : ClosedSmoothRiemannianMetric 3 M}
    (S : Family g) : Set (M × M) :=
  {q | q.2 ∈ (S.normal q.1).source}

/-- Joint target locus of the varying source normal coordinate. -/
def Family.targetLocus {g : ClosedSmoothRiemannianMetric 3 M}
    (S : Family g) : Set (M × E) :=
  {q | q.2 ∈ (S.normal q.1).target}

/-- Forward evaluation in joint anchor-point parameters. -/
def Family.eval {g : ClosedSmoothRiemannianMetric 3 M}
    (S : Family g) (q : M × M) : E :=
  S.normal q.1 q.2

/-- Inverse evaluation in joint anchor-vector parameters. -/
def Family.symmEval {g : ClosedSmoothRiemannianMetric 3 M}
    (S : Family g) (q : M × E) : M :=
  (S.normal q.1).symm q.2

/--
Joint source-anchor regularity.  This is strictly stronger than having one
unrelated open partial homeomorphism for every fixed anchor.
-/
structure Family.JointlyRegular {g : ClosedSmoothRiemannianMetric 3 M}
    (S : Family g) : Prop where
  isOpen_sourceLocus : IsOpen S.sourceLocus
  isOpen_targetLocus : IsOpen S.targetLocus
  continuousOn_eval : ContinuousOn S.eval S.sourceLocus
  continuousOn_symmEval : ContinuousOn S.symmEval S.targetLocus

/--
The intrinsic source normal coordinate carried by the current generic
exponential choice.
-/
def genericFamily (g : ClosedSmoothRiemannianMetric 3 M) : Family g where
  normal x :=
    (chartAt E x).trans
      (GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x).symm
  anchor_mem_source x := by
    let eM := GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x
    change x ∈ (chartAt E x).source ∩ (chartAt E x) ⁻¹' eM.target
    refine ⟨mem_chart_source E x, ?_⟩
    simpa [eM, extChartAt_coe] using
      GeodesicTransport.expAt_base_mem_expAtChartOpenPartialHomeomorph_target
        (g := g) x
  normal_anchor x := by
    simpa using
      CartanMap.expAtChartOpenPartialHomeomorph_symm_chart_anchor_eq_zero g x

@[simp]
theorem genericFamily_apply
    (g : ClosedSmoothRiemannianMetric 3 M) (x z : M) :
    (genericFamily g).normal x z =
      (GeodesicTransport.expAtChartOpenPartialHomeomorph
        (g := g) x).symm ((chartAt E x) z) :=
  rfl

/--
The exact unproved source-anchor regularity statement for the current generic
source exponential choices.
-/
def GenericJointRegularity (g : ClosedSmoothRiemannianMetric 3 M) : Prop :=
  (genericFamily g).JointlyRegular

/-- The complete source diagonal in joint anchor-point parameters. -/
def sourceParameterDiagonal : Set (M × M) :=
  (fun x : M ↦ (x, x)) '' Set.univ

/-- Normal coordinates controlled by a specified vector radius. -/
def Family.controlledSourceLocus
    {g : ClosedSmoothRiemannianMetric 3 M}
    (S : Family g) (rho : ℝ) : Set (M × M) :=
  S.sourceLocus ∩ S.eval ⁻¹' Metric.ball (0 : E) rho

/-- Joint regularity makes every positive-radius controlled locus open. -/
theorem Family.JointlyRegular.isOpen_controlledSourceLocus
    {g : ClosedSmoothRiemannianMetric 3 M}
    {S : Family g} (hS : S.JointlyRegular) (rho : ℝ) :
    IsOpen (S.controlledSourceLocus rho) := by
  exact hS.continuousOn_eval.isOpen_inter_preimage
    hS.isOpen_sourceLocus Metric.isOpen_ball

/-- The source diagonal is compact on a compact manifold. -/
theorem isCompact_sourceParameterDiagonal [CompactSpace M] :
    IsCompact (sourceParameterDiagonal (M := M)) := by
  exact isCompact_univ.image (continuous_id.prodMk continuous_id)

/-- Every positive controlled locus contains the complete source diagonal. -/
theorem sourceParameterDiagonal_subset_controlledSourceLocus
    {g : ClosedSmoothRiemannianMetric 3 M}
    (S : Family g) {rho : ℝ} (hrho : 0 < rho) :
    sourceParameterDiagonal (M := M) ⊆ S.controlledSourceLocus rho := by
  rintro _q ⟨x, _hx, rfl⟩
  constructor
  · exact S.anchor_mem_source x
  · change S.normal x x ∈ Metric.ball (0 : E) rho
    rw [S.normal_anchor]
    exact Metric.mem_ball_self hrho

/--
Joint source regularity turns any positive normal-vector radius into one
ordinary metric radius uniform over every source anchor.  Points closer than
that metric radius lie in the correct anchor's normal source and have normal
coordinate norm below `rho`.
-/
theorem exists_uniform_metric_radius_controlled_by_normalRadius
    [T2Space M] [CompactSpace M] [ConnectedSpace M]
    {g : ClosedSmoothRiemannianMetric 3 M}
    (S : Family g) (hS : S.JointlyRegular)
    {rho : ℝ} (hrho : 0 < rho) :
    letI : MetricSpace M := g.toMetricSpace
    ∃ epsilon > (0 : ℝ), ∀ x z : M, dist z x < epsilon →
      z ∈ (S.normal x).source ∧ ‖S.normal x z‖ < rho := by
  letI : MetricSpace M := g.toMetricSpace
  have hopen : IsOpen (S.controlledSourceLocus rho) :=
    hS.isOpen_controlledSourceLocus rho
  have hdiag :
      sourceParameterDiagonal (M := M) ⊆ S.controlledSourceLocus rho :=
    sourceParameterDiagonal_subset_controlledSourceLocus S hrho
  rcases
      (isCompact_sourceParameterDiagonal (M := M)).exists_cthickening_subset_open
        hopen hdiag with
    ⟨epsilon, hepsilon, hthick⟩
  refine ⟨epsilon, hepsilon, ?_⟩
  intro x z hdist
  have hgraph : (x, x) ∈ sourceParameterDiagonal (M := M) :=
    ⟨x, Set.mem_univ x, rfl⟩
  have hmem : (x, z) ∈
      Metric.cthickening epsilon (sourceParameterDiagonal (M := M)) := by
    apply Metric.mem_cthickening_of_dist_le
      ((x, z) : M × M) (x, x) epsilon
        (sourceParameterDiagonal (M := M)) hgraph
    simpa [Prod.dist_eq, dist_comm] using le_of_lt hdist
  have hcontrolled := hthick hmem
  refine ⟨hcontrolled.1, ?_⟩
  simpa [Family.controlledSourceLocus, Family.eval,
    Metric.mem_ball, dist_eq_norm] using hcontrolled.2

/--
The curvature/Data producer needed after source and target chart regularity
have been separated.  It asks for one normal-vector radius, uniform in source
anchor, target anchor, and tangent alignment, on which supplied-family Data
exist.  This is stronger than the existing fixed-`(x,p)` curvature radius and
is kept as an explicit proof-bearing contract.
-/
def UniformNormalSuccessorData
    {g : ClosedSmoothRiemannianMetric 3 M}
    (S : Family g) (F : CartanTargetExponential.Family) : Prop :=
  ∃ rho > (0 : ℝ),
    ∀ (x : M) (p : RoundSphere3)
      (L : CartanMap.TangentAlignment g x p) (z : M),
      z ∈ (S.normal x).source →
      ‖S.normal x z‖ < rho →
        Nonempty
          (CartanTargetExponential.Data F
            (CartanTargetExponential.ChainState.mk x p L) z)

/--
A chart-local source normal family.  This is the natural interface for a
single parameterized inverse-function construction: it only needs a jointly
open anchor-endpoint locus and a jointly continuous normal-vector evaluation.
-/
structure LocalFamily (g : ClosedSmoothRiemannianMetric 3 M) where
  anchors : Set M
  isOpen_anchors : IsOpen anchors
  sourceLocus : Set (M × M)
  isOpen_sourceLocus : IsOpen sourceLocus
  sourceLocus_fst : ∀ q ∈ sourceLocus, q.1 ∈ anchors
  normal : M × M → E
  continuousOn_normal : ContinuousOn normal sourceLocus
  diagonal_mem : ∀ x ∈ anchors, (x, x) ∈ sourceLocus
  normal_diagonal : ∀ x ∈ anchors, normal (x, x) = (0 : E)

/-- The part of a local source family controlled by a normal-vector radius. -/
def LocalFamily.controlledSourceLocus
    {g : ClosedSmoothRiemannianMetric 3 M}
    (A : LocalFamily g) (rho : ℝ) : Set (M × M) :=
  A.sourceLocus ∩ A.normal ⁻¹' Metric.ball (0 : E) rho

theorem LocalFamily.isOpen_controlledSourceLocus
    {g : ClosedSmoothRiemannianMetric 3 M}
    (A : LocalFamily g) (rho : ℝ) :
    IsOpen (A.controlledSourceLocus rho) := by
  exact A.continuousOn_normal.isOpen_inter_preimage
    A.isOpen_sourceLocus Metric.isOpen_ball

/-- Lift a local controlled source locus into full Cartan successor parameters. -/
def LocalFamily.controlledSuccessorLocus
    {g : ClosedSmoothRiemannianMetric 3 M}
    (A : LocalFamily g) (rho : ℝ) :
    Set ((M × RoundSphere3) × M) :=
  {q | (q.1.1, q.2) ∈ A.controlledSourceLocus rho}

theorem LocalFamily.isOpen_controlledSuccessorLocus
    {g : ClosedSmoothRiemannianMetric 3 M}
    (A : LocalFamily g) (rho : ℝ) :
    IsOpen (A.controlledSuccessorLocus rho) := by
  exact A.isOpen_controlledSourceLocus rho |>.preimage (by fun_prop)

/--
Uniform Data production on one chart-local source family.  The radius is
uniform over all anchors in that local joint source, all sphere targets, and
all tangent alignments.
-/
def LocalUniformNormalSuccessorData
    {g : ClosedSmoothRiemannianMetric 3 M}
    (A : LocalFamily g) (F : CartanTargetExponential.Family) : Prop :=
  ∃ rho > (0 : ℝ),
    ∀ (x : M) (p : RoundSphere3)
      (L : CartanMap.TangentAlignment g x p) (z : M),
      (x, z) ∈ A.sourceLocus →
      ‖A.normal (x, z)‖ < rho →
        Nonempty
          (CartanTargetExponential.Data F
            (CartanTargetExponential.ChainState.mk x p L) z)

/-- Every controlled local successor locus lies in the universal Data locus. -/
theorem LocalFamily.controlledSuccessorLocus_subset_universalData
    {g : ClosedSmoothRiemannianMetric 3 M}
    (A : LocalFamily g) (F : CartanTargetExponential.Family)
    {rho : ℝ}
    (hdata :
      ∀ (x : M) (p : RoundSphere3)
        (L : CartanMap.TangentAlignment g x p) (z : M),
        (x, z) ∈ A.sourceLocus →
        ‖A.normal (x, z)‖ < rho →
          Nonempty
            (CartanTargetExponential.Data F
              (CartanTargetExponential.ChainState.mk x p L) z)) :
    A.controlledSuccessorLocus rho ⊆
      CartanTargetExponential.UniversalSuccessorDataLocus F g := by
  rintro ⟨⟨x, p⟩, z⟩ hz
  intro L
  exact hdata x p L z hz.1 (by
    simpa [LocalFamily.controlledSourceLocus, Metric.mem_ball, dist_eq_norm]
      using hz.2)

/--
`LocalUniformNormalSuccessorData` is exactly a controlled-locus inclusion.
In particular, its downstream use does not require the local normal vector to
be equal to the normal vector selected by the generic exponential.  Such an
identification is only one possible way of proving the inclusion on the
right-hand side.
-/
theorem localUniformNormalSuccessorData_iff_controlledLocus_subset
    {g : ClosedSmoothRiemannianMetric 3 M}
    (A : LocalFamily g) (F : CartanTargetExponential.Family) :
    LocalUniformNormalSuccessorData A F ↔
      ∃ rho > (0 : ℝ),
        A.controlledSuccessorLocus rho ⊆
          CartanTargetExponential.UniversalSuccessorDataLocus F g := by
  constructor
  · rintro ⟨rho, hrho, hdata⟩
    exact ⟨rho, hrho,
      A.controlledSuccessorLocus_subset_universalData F hdata⟩
  · rintro ⟨rho, hrho, hsubset⟩
    refine ⟨rho, hrho, ?_⟩
    intro x p L z hzSource hzNorm
    have hdata := hsubset (show ((x, p), z) ∈
        A.controlledSuccessorLocus rho from
      ⟨hzSource, by
        simpa [LocalFamily.controlledSourceLocus, Metric.mem_ball,
          dist_eq_norm] using hzNorm⟩)
    exact hdata L

/--
The weakest normal-coordinate comparison that transfers an already proved
generic-source Data estimate to a chart-local normal family.  Equality of the
two normal vectors is sufficient for this property, but not necessary: only
source membership and control of the generic normal norm are consumed.
-/
def LocalFamily.ControlsGenericNormal
    {g : ClosedSmoothRiemannianMetric 3 M}
    (A : LocalFamily g) (localRadius genericRadius : ℝ) : Prop :=
  ∀ (x z : M), (x, z) ∈ A.sourceLocus →
    ‖A.normal (x, z)‖ < localRadius →
      z ∈ ((genericFamily g).normal x).source ∧
      ‖(genericFamily g).normal x z‖ < genericRadius

/--
The endpoint-level agreement needed to identify a chart-local inverse with
the hardcoded generic normal coordinate.  For a fixed-chart ODE selector, the
displayed local vector is expected to be the selector's inverse velocity
after applying the fixed-chart-to-anchor-chart transition derivative.

No derivative agreement is included: membership in the generic exponential
source and equality of the endpoint coordinate already let the inverse law
identify the two normal vectors.  Germ agreement is only needed later if one
wants to construct the strict-derivative fields of `Data` directly.
-/
structure LocalFamily.GenericEndpointAgreement
    {g : ClosedSmoothRiemannianMetric 3 M}
    (A : LocalFamily g) (radius : ℝ) : Prop where
  point_mem_anchorChart :
    ∀ (x z : M), (x, z) ∈ A.sourceLocus →
      ‖A.normal (x, z)‖ < radius →
        z ∈ (chartAt E x).source
  vector_mem_genericExpSource :
    ∀ (x z : M), (x, z) ∈ A.sourceLocus →
      ‖A.normal (x, z)‖ < radius →
        A.normal (x, z) ∈
          (GeodesicTransport.expAtChartOpenPartialHomeomorph
            (g := g) x).source
  endpoint_coordinate :
    ∀ (x z : M), (x, z) ∈ A.sourceLocus →
      ‖A.normal (x, z)‖ < radius →
        (chartAt E x) z =
          GeodesicTransport.expAtChartOpenPartialHomeomorph
            (g := g) x (A.normal (x, z))

/-- Endpoint agreement identifies the local normal with the generic normal. -/
theorem LocalFamily.GenericEndpointAgreement.normal_eq_generic
    {g : ClosedSmoothRiemannianMetric 3 M}
    {A : LocalFamily g} {radius : ℝ}
    (h : A.GenericEndpointAgreement radius)
    {x z : M} (hzSource : (x, z) ∈ A.sourceLocus)
    (hzNorm : ‖A.normal (x, z)‖ < radius) :
    A.normal (x, z) = (genericFamily g).normal x z := by
  let eM :=
    GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x
  have hvSource : A.normal (x, z) ∈ eM.source :=
    h.vector_mem_genericExpSource x z hzSource hzNorm
  have hcoordinate : (chartAt E x) z = eM (A.normal (x, z)) :=
    h.endpoint_coordinate x z hzSource hzNorm
  change A.normal (x, z) = eM.symm ((chartAt E x) z)
  rw [hcoordinate, eM.left_inv hvSource]

/--
The endpoint agreement contract is a concrete sufficient instance of the
minimal generic-normal control relation, with no loss in normal radius.
-/
theorem LocalFamily.GenericEndpointAgreement.controlsGenericNormal
    {g : ClosedSmoothRiemannianMetric 3 M}
    {A : LocalFamily g} {radius : ℝ}
    (h : A.GenericEndpointAgreement radius) :
    A.ControlsGenericNormal radius radius := by
  intro x z hzSource hzNorm
  let eM :=
    GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x
  have hvSource : A.normal (x, z) ∈ eM.source :=
    h.vector_mem_genericExpSource x z hzSource hzNorm
  have hcoordinate : (chartAt E x) z = eM (A.normal (x, z)) :=
    h.endpoint_coordinate x z hzSource hzNorm
  have hzGenericSource : z ∈ ((genericFamily g).normal x).source := by
    change z ∈ (chartAt E x).source ∩ (chartAt E x) ⁻¹' eM.target
    exact ⟨h.point_mem_anchorChart x z hzSource hzNorm, by
      change (chartAt E x) z ∈ eM.target
      rw [hcoordinate]
      exact eM.map_source hvSource⟩
  refine ⟨hzGenericSource, ?_⟩
  rw [← h.normal_eq_generic hzSource hzNorm]
  exact hzNorm

/--
Transfer a generic-source normal-radius Data theorem through the minimal
normal-coordinate control relation.  This lemma makes the source-family
mismatch explicit: a fixed-chart inverse only has to control the hardcoded
generic normal appearing in `CartanTargetExponential.Data`; it need not be
definitionally the same function.
-/
theorem localUniformNormalSuccessorData_of_controlsGenericNormal
    {g : ClosedSmoothRiemannianMetric 3 M}
    (A : LocalFamily g) (F : CartanTargetExponential.Family)
    {localRadius genericRadius : ℝ}
    (hlocalRadius : 0 < localRadius)
    (hcontrol : A.ControlsGenericNormal localRadius genericRadius)
    (hgenericData :
      ∀ (x : M), x ∈ A.anchors →
        ∀ (p : RoundSphere3)
          (L : CartanMap.TangentAlignment g x p) (z : M),
          z ∈ ((genericFamily g).normal x).source →
          ‖(genericFamily g).normal x z‖ < genericRadius →
            Nonempty
              (CartanTargetExponential.Data F
                (CartanTargetExponential.ChainState.mk x p L) z)) :
    LocalUniformNormalSuccessorData A F := by
  refine ⟨localRadius, hlocalRadius, ?_⟩
  intro x p L z hzSource hzNorm
  rcases hcontrol x z hzSource hzNorm with
    ⟨hzGenericSource, hzGenericNorm⟩
  exact hgenericData x (A.sourceLocus_fst (x, z) hzSource)
    p L z hzGenericSource hzGenericNorm

/--
An open cover by chart-local source families, each carrying a uniform normal
Data producer, proves the global supplied-family diagonal neighborhood.  This
is the finite-atlas/parameterized-IFT assembly boundary needed by fixed-chart
constructions; no globally selected source exponential family is required.
-/
theorem universalSuccessorDataNeighborhood_of_localSourceFamilyCover
    {g : ClosedSmoothRiemannianMetric 3 M}
    (F : CartanTargetExponential.Family)
    (hcover : ∀ x : M,
      ∃ A : LocalFamily g,
        x ∈ A.anchors ∧ LocalUniformNormalSuccessorData A F) :
    CartanTargetExponential.UniversalSuccessorDataNeighborhood F g := by
  classical
  choose A hxA hlocal using hcover
  choose rho hrho hdata using hlocal
  let W : Set ((M × RoundSphere3) × M) :=
    ⋃ x : M, (A x).controlledSuccessorLocus (rho x)
  have hopenW : IsOpen W := by
    exact isOpen_iUnion fun x => (A x).isOpen_controlledSuccessorLocus (rho x)
  have hdiagW :
      CartanTargetExponential.successorParameterDiagonal (M := M) ⊆ W := by
    rintro _q ⟨⟨x, p⟩, _hxp, rfl⟩
    refine Set.mem_iUnion.2 ⟨x, ?_⟩
    change (x, x) ∈ (A x).sourceLocus ∧
      (A x).normal (x, x) ∈ Metric.ball (0 : E) (rho x)
    constructor
    · exact (A x).diagonal_mem x (hxA x)
    · rw [(A x).normal_diagonal x (hxA x)]
      exact Metric.mem_ball_self (hrho x)
  have hWdata :
      W ⊆ CartanTargetExponential.UniversalSuccessorDataLocus F g := by
    intro q hq
    rcases Set.mem_iUnion.mp hq with ⟨x, hx⟩
    exact
      (A x).controlledSuccessorLocus_subset_universalData F (hdata x) hx
  exact Filter.mem_of_superset
    (hopenW.mem_nhdsSet.mpr hdiagW) hWdata

/--
Minimal logical bridge: joint source regularity plus a uniform normal Data
producer makes the supplied successor-data locus a neighborhood of the full
source-target diagonal.
-/
theorem universalSuccessorDataNeighborhood_of_jointSource_and_uniformNormalData
    [T2Space M] [CompactSpace M] [ConnectedSpace M]
    {g : ClosedSmoothRiemannianMetric 3 M}
    (S : Family g) (hS : S.JointlyRegular)
    (F : CartanTargetExponential.Family)
    (hdata : UniformNormalSuccessorData S F) :
    CartanTargetExponential.UniversalSuccessorDataNeighborhood F g := by
  letI : MetricSpace M := g.toMetricSpace
  rcases hdata with ⟨rho, hrho, hnormalData⟩
  rcases exists_uniform_metric_radius_controlled_by_normalRadius
      S hS hrho with
    ⟨epsilon, hepsilon, hcontrolled⟩
  let U : Set ((M × RoundSphere3) × M) :=
    {q | dist q.2 q.1.1 < epsilon}
  have hopenU : IsOpen U := by
    dsimp [U]
    exact isOpen_lt (by fun_prop) continuous_const
  have hdiagU :
      CartanTargetExponential.successorParameterDiagonal (M := M) ⊆ U := by
    rintro _q ⟨⟨x, p⟩, _hxp, rfl⟩
    simpa [U] using hepsilon
  have hUdata :
      U ⊆ CartanTargetExponential.UniversalSuccessorDataLocus F g := by
    rintro ⟨⟨x, p⟩, z⟩ hz
    intro L
    have hclose : dist z x < epsilon := hz
    rcases hcontrolled x z hclose with ⟨hzSource, hzNorm⟩
    exact hnormalData x p L z hzSource hzNorm
  exact Filter.mem_of_superset
    (hopenU.mem_nhdsSet.mpr hdiagU) hUdata

/--
Full source-target-curvature bundle.  Target regularity and its identity
derivative are recorded because they are the inputs from which the uniform
normal Data producer is expected to be proved; the downstream neighborhood
argument itself uses the producer and joint source regularity.
-/
structure ProofBearingJointContract
    {g : ClosedSmoothRiemannianMetric 3 M}
    (S : Family g) (F : CartanTargetExponential.Family) : Prop where
  sourceRegular : S.JointlyRegular
  targetRegular : F.JointlyRegular
  targetIdentityDerivative : F.HasIdentityStrictDerivativeAtZero
  uniformNormalData : UniformNormalSuccessorData S F

/-- Package a joint source-target contract for the target-family consumer. -/
def ProofBearingJointContract.toTargetContract
    [T2Space M] [CompactSpace M] [ConnectedSpace M]
    {g : ClosedSmoothRiemannianMetric 3 M}
    {S : Family g} {F : CartanTargetExponential.Family}
    (C : ProofBearingJointContract S F) :
    CartanTargetExponential.ProofBearingSuccessorContract F g where
  targetRegular := C.targetRegular
  targetIdentityDerivative := C.targetIdentityDerivative
  dataNeighborhood :=
    universalSuccessorDataNeighborhood_of_jointSource_and_uniformNormalData
      S C.sourceRegular F C.uniformNormalData

/--
The exact remaining proof-bearing boundary for the current generic source and
the normalized round-sphere target.
-/
structure GenericSourceCanonicalTargetContract
    (g : ClosedSmoothRiemannianMetric 3 M) : Prop where
  sourceRegular : GenericJointRegularity g
  uniformNormalData :
    UniformNormalSuccessorData (genericFamily g)
      CartanTargetExponential.canonicalFamily

/-- Convert the remaining source boundary into the complete joint contract. -/
def GenericSourceCanonicalTargetContract.toJointContract
    {g : ClosedSmoothRiemannianMetric 3 M}
    (C : GenericSourceCanonicalTargetContract g) :
    ProofBearingJointContract (genericFamily g)
      CartanTargetExponential.canonicalFamily where
  sourceRegular := C.sourceRegular
  targetRegular := CartanTargetExponential.canonicalFamily_jointlyRegular
  targetIdentityDerivative :=
    CartanTargetExponential.canonicalFamily_hasIdentityStrictDerivativeAtZero
  uniformNormalData := C.uniformNormalData

/--
Once the explicit generic-source/canonical-target boundary is supplied, every
rooted Cartan path has a genuine canonical-family differential-successor chain
with any prescribed positive metric mesh.
-/
theorem GenericSourceCanonicalTargetContract.exists_rooted_realization
    [T2Space M] [CompactSpace M] [ConnectedSpace M]
    {g : ClosedSmoothRiemannianMetric 3 M}
    (C : GenericSourceCanonicalTargetContract g)
    (skeleton :
      CartanAtlasRootedPathSkeleton.RootedCartanPathSkeleton g)
    (mesh : ℝ) (hmesh : 0 < mesh) :
    letI : MetricSpace M := g.toMetricSpace
    ∃ realization :
        CartanTargetExponential.SuppliedRootedPathChainRealization
          CartanTargetExponential.canonicalFamily skeleton,
      (∀ x : M, 0 < realization.terminalIndex x) ∧
      (∀ x : M, Monotone (realization.nodeTime x)) ∧
      (∀ x : M, ∀ n ≥ realization.terminalIndex x,
        realization.nodeTime x n = 1) ∧
      ∀ (x : M) (n : ℕ),
        dist
          (skeleton.path x (realization.nodeTime x n))
          (skeleton.path x (realization.nodeTime x (n + 1))) < mesh :=
  C.toJointContract.toTargetContract
    |>.exists_suppliedRootedPathChainRealization_with_prescribed_mesh
      skeleton mesh hmesh

end CartanSourceExponential
end Poincare
