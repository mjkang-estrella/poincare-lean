import Poincare.Global.DifferentialUniformSuccessorMesh
import Poincare.Global.DifferentialSuccessorZero

/-!
# Joint neighborhoods for uniform differential-successor equality

`UniformSuccessorEqOnBall` asks for one radius that controls two movements:
the successor anchor moves away from its predecessor, and the evaluation point
moves away from the successor anchor.  This file combines those variables in
one finite-dimensional parameter space.

The equality locus quantifies over every tangent alignment and every actual
`DifferentialInducedSuccessor.Data` at the displayed successor anchor.  Its
compact diagonal consists of parameters with predecessor, successor, and
evaluation anchors all equal.  The zero-successor theorem puts that entire
diagonal in the equality locus.  A neighborhood of the diagonal then has one
compactness radius; halving it controls both metric movements and produces the
state-uniform equality ball required by the adaptive mesh argument.
-/

noncomputable section

open Filter Metric Set
open scoped Manifold ContDiff Topology RealInnerProductSpace

namespace Poincare
namespace DifferentialSuccessorJointEqualityNeighborhood

universe u

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace E M]
variable [IsManifold I ∞ M]

open DifferentialUniformSuccessorMesh

/-- Parameters for one predecessor anchor and round target, one successor
anchor, and one point where the predecessor and successor germs are compared. -/
abbrev JointSuccessorEqualityParameter3 (M : Type u) :=
  (((M × RoundSphere3) × M) × M)

/-- The locus where every actual differential-induced successor at the
displayed successor anchor agrees with its predecessor at the displayed
evaluation point.  No successor datum is selected or hidden: the equality is
required for every datum carrying the stated dependent indices. -/
def UniversalSuccessorEqualityLocus
    (g : ClosedSmoothRiemannianMetric 3 M) :
    Set (JointSuccessorEqualityParameter3 M) :=
  {q | ∀ (L : CartanMap.TangentAlignment g q.1.1.1 q.1.1.2)
      (d : DifferentialInducedSuccessor.Data
        (CartanChain.ChainState.mk q.1.1.1 q.1.1.2 L) q.1.2),
      (CartanChain.ChainState.mk q.1.1.1 q.1.1.2 L).germ q.2 =
        d.successor.germ q.2}

/-- The compact graph on which predecessor, successor, and evaluation anchors
all coincide. -/
def successorEqualityParameterDiagonal :
    Set (JointSuccessorEqualityParameter3 M) :=
  (fun xp : M × RoundSphere3 ↦ ((xp, xp.1), xp.1)) '' Set.univ

section Compact

variable [CompactSpace M] [ConnectedSpace M]

/-- Compactness of the target manifold makes the complete joint parameter
diagonal compact. -/
theorem isCompact_successorEqualityParameterDiagonal :
    IsCompact (successorEqualityParameterDiagonal (M := M)) := by
  exact isCompact_univ.image
    ((continuous_id.prodMk continuous_fst).prodMk continuous_fst)

/-- At a diagonal parameter every actual datum stores the zero source normal
vector, so its successor state is the predecessor state.  Hence the equality
holds without any local regularity assumption and at every diagonal
evaluation point. -/
theorem successorEqualityParameterDiagonal_subset_universalSuccessorEqualityLocus
    (g : ClosedSmoothRiemannianMetric 3 M) :
    successorEqualityParameterDiagonal (M := M) ⊆
      UniversalSuccessorEqualityLocus g := by
  rintro _q ⟨⟨x, p⟩, _hxp, rfl⟩
  intro L d
  let s : CartanChain.ChainState g :=
    CartanChain.ChainState.mk x p L
  have hdzero : d.v = 0 :=
    DifferentialSuccessorZero.data_vector_eq_zero_of_anchor_eq d rfl
  have hsuccessor : d.successor = s :=
    DifferentialSuccessorZero.successor_eq_of_vector_eq_zero d hdzero
  change s.germ x = d.successor.germ x
  rw [hsuccessor]

/-- The weakest joint stability contract for germ equality: the universal
actual-data equality locus is a neighborhood of the compact joint diagonal. -/
def UniversalSuccessorEqualityNeighborhood
    (g : ClosedSmoothRiemannianMetric 3 M) : Prop :=
  UniversalSuccessorEqualityLocus g ∈
    𝓝ˢ (successorEqualityParameterDiagonal (M := M))

/-- Openness of the universal actual-data equality locus is sufficient for
the joint neighborhood contract because zero successors supply the whole
diagonal. -/
theorem universalSuccessorEqualityNeighborhood_of_isOpen
    (g : ClosedSmoothRiemannianMetric 3 M)
    (hopen : IsOpen (UniversalSuccessorEqualityLocus g)) :
    UniversalSuccessorEqualityNeighborhood g :=
  hopen.mem_nhdsSet.mpr
    (successorEqualityParameterDiagonal_subset_universalSuccessorEqualityLocus
      g)

/-- Compact thickening of the joint diagonal supplies one positive radius
that simultaneously controls movement from predecessor anchor `x` to
successor anchor `z` and movement from `z` to the evaluation point `q`.

The factor `1/2` is the only loss: the triangle inequality gives
`dist q x < eta + eta = epsilon`, which puts the full joint parameter in the
`epsilon`-closed thickening selected by compactness. -/
theorem exists_uniform_jointSuccessorEquality_radius
    (g : ClosedSmoothRiemannianMetric 3 M)
    (hneighborhood : UniversalSuccessorEqualityNeighborhood g) :
    letI : MetricSpace M := g.toMetricSpace
    ∃ eta > (0 : ℝ),
      ∀ (x : M) (p : RoundSphere3)
        (L : CartanMap.TangentAlignment g x p) (z q : M)
        (d : DifferentialInducedSuccessor.Data
          (CartanChain.ChainState.mk x p L) z),
        dist z x < eta →
        dist q z < eta →
          (CartanChain.ChainState.mk x p L).germ q =
            d.successor.germ q := by
  letI : MetricSpace M := g.toMetricSpace
  rcases
      (Metric.hasBasis_nhdsSet_cthickening
        (isCompact_successorEqualityParameterDiagonal (M := M))).mem_iff.mp
        hneighborhood with
    ⟨epsilon, hepsilon, hthick⟩
  let eta : ℝ := epsilon / 2
  refine ⟨eta, half_pos hepsilon, ?_⟩
  intro x p L z q d hzx hqz
  let graphPoint : JointSuccessorEqualityParameter3 M :=
    (((x, p), x), x)
  have hgraphPoint :
      graphPoint ∈ successorEqualityParameterDiagonal (M := M) := by
    exact ⟨(x, p), Set.mem_univ _, rfl⟩
  have hzx_epsilon : dist z x < epsilon :=
    hzx.trans (half_lt_self hepsilon)
  have hqx_epsilon : dist q x < epsilon := by
    calc
      dist q x ≤ dist q z + dist z x := dist_triangle q z x
      _ < eta + eta := add_lt_add hqz hzx
      _ = epsilon := by simp [eta]
  have hfirst_epsilon :
      dist (((x, p), z) : (M × RoundSphere3) × M)
        (((x, p), x) : (M × RoundSphere3) × M) < epsilon := by
    simpa [Prod.dist_eq] using hzx_epsilon
  have hjoint_epsilon :
      dist ((((x, p), z), q) : JointSuccessorEqualityParameter3 M)
        graphPoint < epsilon := by
    rw [Prod.dist_eq]
    exact max_lt_iff.mpr ⟨hfirst_epsilon, hqx_epsilon⟩
  have hmem :
      ((((x, p), z), q) : JointSuccessorEqualityParameter3 M) ∈
        Metric.cthickening epsilon
          (successorEqualityParameterDiagonal (M := M)) := by
    apply Metric.mem_cthickening_of_dist_le
      ((((x, p), z), q) : JointSuccessorEqualityParameter3 M)
        graphPoint epsilon
        (successorEqualityParameterDiagonal (M := M)) hgraphPoint
    exact le_of_lt hjoint_epsilon
  exact (hthick hmem) L d

/-- The joint diagonal-neighborhood contract produces the raw uniform
successor-equality ball expected by the adaptive mesh consumer. -/
theorem exists_uniformSuccessorEqOnBall_of_jointNeighborhood
    (g : ClosedSmoothRiemannianMetric 3 M)
    (hneighborhood : UniversalSuccessorEqualityNeighborhood g) :
    ∃ eta > (0 : ℝ), UniformSuccessorEqOnBall g eta := by
  letI : MetricSpace M := g.toMetricSpace
  rcases exists_uniform_jointSuccessorEquality_radius g hneighborhood with
    ⟨eta, heta, hjoint⟩
  refine ⟨eta, heta, ?_⟩
  change ∀ (s : CartanChain.ChainState g) {z : M}
      (d : DifferentialInducedSuccessor.Data s z),
      dist z s.anchor < eta →
        EqOn s.germ d.successor.germ (Metric.ball z eta)
  intro s z d hzx q hq
  rw [Metric.mem_ball] at hq
  cases s with
  | mk x p L =>
      exact hjoint x p L z q d hzx hq

end Compact

end DifferentialSuccessorJointEqualityNeighborhood
end Poincare
