import Poincare.Global.CartanCanonicalRootedUniformSuccessorMeshRecognition
import Poincare.Global.DifferentialSuccessorStrictFactorInsertionTransport

/-!
# Strict-factor transport from uniform successor geometry

A genuinely uniform successor-data radius constructs every reached history in
a finite strict refinement directly from metric smallness.  A genuinely
state-uniform equality ball then transports each single insertion.  Thus no
row data, insertion chains, adaptive radius family, or terminal equality must
be stored: a strict factor map and two kinds of geometric edge bounds suffice.
-/

noncomputable section

open Metric Set
open scoped Manifold ContDiff Topology

namespace Poincare
namespace DifferentialUniformSuccessorStrictFactorGeometry

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

open CartanCanonicalRootedUniformSuccessorMeshRecognition
open DifferentialInducedSuccessor
open DifferentialInducedSuccessor.Chain
open DifferentialSuccessorFiniteInsertionRefinement
open DifferentialSuccessorReachableChainRefinement
open DifferentialSuccessorStrictFactorInsertionTransport

universe u

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace E M]
variable [IsManifold I ∞ M]
variable [CompactSpace M] [ConnectedSpace M]

variable {g : ClosedSmoothRiemannianMetric 3 M}

namespace JointUniformSuccessorRadiusCertificate

/-- Uniform successor data construct an actual reachable chain on every node
sequence whose adjacent edges are smaller than the joint mesh radius.  The
recursion asks for data only at the state actually reached at each index. -/
noncomputable def realizedChainOfMeshSmall
    (certificate : JointUniformSuccessorRadiusCertificate g)
    (nodes : ℕ → M) (initial : CartanChain.ChainState g)
    (hinitial : initial.anchor = nodes 0)
    (hsmall :
      letI : MetricSpace M := g.toMetricSpace
      ∀ n : ℕ, dist (nodes (n + 1)) (nodes n) < certificate.meshRadius) :
    ReachableChain nodes initial := by
  letI : MetricSpace M := g.toMetricSpace
  classical
  let stepData : ∀ (n : ℕ) (s : CartanChain.ChainState g),
      s.anchor = nodes n → Data s (nodes (n + 1)) := by
    intro n s hs
    apply Classical.choice
    apply certificate.successorData.data
    rw [hs]
    exact (hsmall n).trans certificate.meshRadius_lt_dataRadius
  let state : ∀ n : ℕ,
      {s : CartanChain.ChainState g // s.anchor = nodes n} := by
    intro n
    induction n with
    | zero => exact ⟨initial, hinitial⟩
    | succ n state_n =>
        let d := stepData n state_n.1 state_n.2
        exact ⟨d.successor, d.successor_anchor⟩
  exact
    { state := fun n ↦ (state n).1
      initial_eq := rfl
      data := fun n ↦ stepData n (state n).1 (state n).2
      successor_eq := fun _ ↦ rfl }

end JointUniformSuccessorRadiusCertificate

/-- Pure geometric input for one finite strict factorization.

`schedule_small` controls every adjacent edge in every intermediate
single-insertion history, so the uniform data radius constructs those
histories rather than receiving them as fields.  `insertion_opposite_small`
places the old next node in the uniform equality ball around the newly
inserted node. -/
structure UniformStrictFactorGeometry
    (certificate : JointUniformSuccessorRadiusCertificate g)
    (seed refined : ℕ → M) (initial : CartanChain.ChainState g)
    (length : ℕ) where
  factor : ℕ → ℕ
  factor_zero : factor 0 = 0
  factor_strict : ∀ n < length, factor n < factor (n + 1)
  factor_value : ∀ n ≤ length, refined (factor n) = seed n
  initial_anchor : initial.anchor = seed 0
  coarse_small :
    letI : MetricSpace M := g.toMetricSpace
    ∀ j : ℕ, dist (seed (j + 1)) (seed j) < certificate.meshRadius
  refined_small :
    letI : MetricSpace M := g.toMetricSpace
    ∀ j : ℕ, dist (refined (j + 1)) (refined j) < certificate.meshRadius
  schedule_zero : ∀ n i : ℕ,
    insertNodeListSchedule
      (factorRefinementStage seed refined factor n) (factor n)
      (factorGapNodes refined factor n) i 0 = seed 0
  schedule_small :
    letI : MetricSpace M := g.toMetricSpace
    ∀ n i j : ℕ,
      dist
          (insertNodeListSchedule
            (factorRefinementStage seed refined factor n) (factor n)
            (factorGapNodes refined factor n) i (j + 1))
          (insertNodeListSchedule
            (factorRefinementStage seed refined factor n) (factor n)
            (factorGapNodes refined factor n) i j) <
        certificate.meshRadius
  insertion_opposite_small :
    letI : MetricSpace M := g.toMetricSpace
    ∀ n < length, ∀ i < (factorGapNodes refined factor n).length,
      dist
          (insertNodeListSchedule
            (factorRefinementStage seed refined factor n) (factor n)
            (factorGapNodes refined factor n) i (factor n + i + 1))
          (insertNodeListSchedule
            (factorRefinementStage seed refined factor n) (factor n)
            (factorGapNodes refined factor n) (i + 1)
              (factor n + i + 1)) < certificate.equalityRadius

namespace UniformStrictFactorGeometry

variable {certificate : JointUniformSuccessorRadiusCertificate g}
variable {seed refined : ℕ → M}
variable {initial : CartanChain.ChainState g} {length : ℕ}

/-- The coarse history is derived from its mesh bound. -/
noncomputable def coarseChain
    (geometry : UniformStrictFactorGeometry certificate seed refined initial
      length) :
    ReachableChain seed initial :=
  JointUniformSuccessorRadiusCertificate.realizedChainOfMeshSmall
    certificate seed initial geometry.initial_anchor
    geometry.coarse_small

/-- The refined history is likewise derived, not retained. -/
noncomputable def refinedChain
    (geometry : UniformStrictFactorGeometry certificate seed refined initial
      length) :
    ReachableChain refined initial := by
  apply JointUniformSuccessorRadiusCertificate.realizedChainOfMeshSmall
    certificate refined initial
  · calc
      initial.anchor = seed 0 := geometry.initial_anchor
      _ = refined 0 := by
        rw [← geometry.factor_value 0 (Nat.zero_le length),
          geometry.factor_zero]
  · exact geometry.refined_small

/-- Every intermediate insertion history is reconstructed from the same
uniform data radius. -/
noncomputable def insertionChain
    (geometry : UniformStrictFactorGeometry certificate seed refined initial
      length)
    (n i : ℕ) :
    ReachableChain
      (insertNodeListSchedule
        (factorRefinementStage seed refined geometry.factor n)
        (geometry.factor n)
        (factorGapNodes refined geometry.factor n) i) initial :=
  JointUniformSuccessorRadiusCertificate.realizedChainOfMeshSmall
    certificate _ initial
    (geometry.initial_anchor.trans (geometry.schedule_zero n i).symm)
    (geometry.schedule_small n i)

/-- Uniform successor data and equality balls turn the geometric strict
factor into terminal state equality.

The proof applies the existing insertion-concatenation theorem.  For each
single insertion, prefix canonicity identifies the predecessor state, the
new chain datum supplies the actual successor, and the state-uniform equality
ball supplies the required open patch. -/
theorem coarse_state_eq_refined_state
    (geometry : UniformStrictFactorGeometry certificate seed refined initial
      length) :
    geometry.coarseChain.state length =
      geometry.refinedChain.state (geometry.factor length) := by
  letI : MetricSpace M := g.toMetricSpace
  have hUniform := certificate.successorEqOnBall
  change ∀ (s : CartanChain.ChainState g) {z : M}
      (d : Data s z), dist z s.anchor < certificate.equalityRadius →
        EqOn s.germ d.successor.germ
          (Metric.ball z certificate.equalityRadius) at hUniform
  apply ReachableChain.state_eq_of_strict_factor_of_gap_eqOn_open
    seed refined length geometry.factor geometry.factor_zero
      geometry.factor_strict geometry.factor_value geometry.coarseChain
      geometry.refinedChain geometry.insertionChain
      (fun n i ↦ Metric.ball
        (insertNodeListSchedule
          (factorRefinementStage seed refined geometry.factor n)
          (geometry.factor n) (factorGapNodes refined geometry.factor n)
          (i + 1) (geometry.factor n + i + 1))
        certificate.equalityRadius)
  · intro _n _hn _i _hi
    exact Metric.isOpen_ball
  · intro n hn i hi
    rw [Metric.mem_ball]
    exact geometry.insertion_opposite_small n hn i hi
  · intro n hn i hi
    let p := geometry.factor n + i
    have hprefix :
        (geometry.insertionChain n i).state p =
          (geometry.insertionChain n (i + 1)).state p := by
      apply ReachableChain.state_eq_of_prefix_nodes
      intro j hj
      exact
        (insertNodeListSchedule_succ_eq_of_le
          (factorRefinementStage seed refined geometry.factor n)
          (geometry.factor n) (factorGapNodes refined geometry.factor n)
          i (j + 1) hi (by dsimp [p] at hj ⊢; omega)).symm
    rw [hprefix, (geometry.insertionChain n (i + 1)).state_succ p]
    apply hUniform
    rw [(geometry.insertionChain n (i + 1)).state_anchor_eq_node
      (geometry.initial_anchor.trans
        (geometry.schedule_zero n (i + 1)).symm) p]
    exact
      (geometry.schedule_small n (i + 1) p).trans_le
        certificate.meshRadius_le_equalityRadius

end UniformStrictFactorGeometry

end DifferentialUniformSuccessorStrictFactorGeometry
end Poincare
