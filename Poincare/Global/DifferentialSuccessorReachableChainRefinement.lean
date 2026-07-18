import Poincare.Global.DifferentialSuccessorFiniteAnchorRadius

/-!
# Refinement invariance for realized differential-successor chains

Changing a finite subdivision changes the type of a realized chain, so the
fixed-node canonicity theorem cannot compare the two histories directly.  The
lemmas here isolate the missing combinatorics.  Equal prefixes give equal
reached states; equal shifted tails propagate any one equality of reached
states; consequently a single inserted node does not change any later state
once the old history and the inserted history agree locally at the first old
node after the insertion.

This is the refinement mechanism used by adaptive Cartan grids.  Its local
germ-agreement premise is precisely the geometric premise supplied by a
curvature equality patch; there is no data policy at counterfactual states.
-/

noncomputable section

open Set
open scoped Manifold ContDiff Topology

namespace Poincare
namespace DifferentialSuccessorReachableChainRefinement

universe u

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace E M]
variable [IsManifold I ∞ M]

open DifferentialInducedSuccessor
open DifferentialInducedSuccessor.Chain
open DifferentialSuccessorAdjacentContinuation

/-- Successor canonicity with both the predecessor and the new anchor
identified propositionally. -/
theorem Data.successor_eq_of_state_eq_of_anchor_eq
    {g : ClosedSmoothRiemannianMetric 3 M}
    {s₁ s₂ : CartanChain.ChainState g} {x₁ x₂ : M}
    (hstate : s₁ = s₂) (hanchor : x₁ = x₂)
    (d₁ : Data s₁ x₁) (d₂ : Data s₂ x₂) :
    d₁.successor = d₂.successor := by
  subst s₂
  subst x₂
  exact d₁.successor_eq d₂

/-- An open equality patch gives cross-history agreement even when the two
data packages spell the common anchor by propositionally equal terms. -/
theorem crossHistorySuccessorAgreement_of_eqOn_open_of_anchor_eq
    {g : ClosedSmoothRiemannianMetric 3 M}
    {s₁ s₂ : CartanChain.ChainState g} {q₁ q₂ : M}
    (hanchor : q₁ = q₂)
    (d₁ : Data s₁ q₁) (d₂ : Data s₂ q₂)
    {U : Set M} (hU : IsOpen U) (hq : q₁ ∈ U)
    (hEq : EqOn s₁.germ s₂.germ U) :
    CrossHistorySuccessorAgreement s₁ s₂ q₁ := by
  subst q₂
  exact crossHistorySuccessorAgreement_of_eqOn_open d₁ d₂ hU hq hEq

/-- Consume cross-history agreement when the second data package uses a
propositionally equal spelling of the common anchor. -/
theorem successor_eq_of_crossHistoryAgreement_of_anchor_eq
    {g : ClosedSmoothRiemannianMetric 3 M}
    {s₁ s₂ : CartanChain.ChainState g} {q₁ q₂ : M}
    (hanchor : q₁ = q₂)
    (h : CrossHistorySuccessorAgreement s₁ s₂ q₁)
    (d₁ : Data s₁ q₁) (d₂ : Data s₂ q₂) :
    d₁.successor = d₂.successor := by
  subst q₂
  exact successor_eq_of_crossHistoryAgreement h d₁ d₂

/-- Realized chains with equal node prefixes reach the same state at the end
of that prefix.  The two node sequences may differ after the displayed
index. -/
theorem ReachableChain.state_eq_of_prefix_nodes
    {g : ClosedSmoothRiemannianMetric 3 M}
    {nodes₁ nodes₂ : ℕ → M} {initial : CartanChain.ChainState g}
    (chain₁ : ReachableChain nodes₁ initial)
    (chain₂ : ReachableChain nodes₂ initial)
    (p : ℕ)
    (hnodes : ∀ j < p, nodes₁ (j + 1) = nodes₂ (j + 1)) :
    chain₁.state p = chain₂.state p := by
  induction p with
  | zero => exact chain₁.initial_eq.trans chain₂.initial_eq.symm
  | succ p ih =>
      have hprefix : ∀ j < p, nodes₁ (j + 1) = nodes₂ (j + 1) := by
        intro j hj
        exact hnodes j (Nat.lt_succ_of_lt hj)
      have hstate : chain₁.state p = chain₂.state p := ih hprefix
      have hnode : nodes₁ (p + 1) = nodes₂ (p + 1) :=
        hnodes p (Nat.lt_succ_self p)
      calc
        chain₁.state (p + 1) = (chain₁.data p).successor :=
          chain₁.state_succ p
        _ = (chain₂.data p).successor :=
          Data.successor_eq_of_state_eq_of_anchor_eq
            hstate hnode (chain₁.data p) (chain₂.data p)
        _ = chain₂.state (p + 1) := (chain₂.state_succ p).symm

/-- Once two realized histories reach the same state and their future nodes
agree after an index shift, all of their later reached states agree. -/
theorem ReachableChain.state_eq_of_shifted_tail
    {g : ClosedSmoothRiemannianMetric 3 M}
    {nodes₁ nodes₂ : ℕ → M}
    {initial₁ initial₂ : CartanChain.ChainState g}
    (chain₁ : ReachableChain nodes₁ initial₁)
    (chain₂ : ReachableChain nodes₂ initial₂)
    (i₁ i₂ : ℕ)
    (hstate : chain₁.state i₁ = chain₂.state i₂)
    (hnodes : ∀ r : ℕ,
      nodes₁ (i₁ + r + 1) = nodes₂ (i₂ + r + 1)) :
    ∀ r : ℕ, chain₁.state (i₁ + r) = chain₂.state (i₂ + r) := by
  intro r
  induction r with
  | zero => simpa using hstate
  | succ r ih =>
      have hnode :
          nodes₁ ((i₁ + r) + 1) = nodes₂ ((i₂ + r) + 1) := by
        simpa [Nat.add_assoc] using hnodes r
      calc
        chain₁.state (i₁ + r.succ) =
            chain₁.state ((i₁ + r) + 1) := by congr 1
        _ = (chain₁.data (i₁ + r)).successor :=
          chain₁.state_succ (i₁ + r)
        _ = (chain₂.data (i₂ + r)).successor :=
          Data.successor_eq_of_state_eq_of_anchor_eq ih hnode
            (chain₁.data (i₁ + r)) (chain₂.data (i₂ + r))
        _ = chain₂.state ((i₂ + r) + 1) :=
          (chain₂.state_succ (i₂ + r)).symm
        _ = chain₂.state (i₂ + r.succ) := by congr 1

/-- A single inserted subdivision node preserves every later reached state.

The prefix equality identifies the histories before the insertion.  At the
first old node after it, an equality patch between the old reached germ and
the inserted reached germ identifies their canonical differential successors.
The shifted-tail theorem then propagates that equality through the entire
common tail. -/
theorem ReachableChain.state_eq_after_single_insertion_of_eqOn_open
    {g : ClosedSmoothRiemannianMetric 3 M}
    {nodes coarse : ℕ → M} {initial : CartanChain.ChainState g}
    (refinedChain : ReachableChain nodes initial)
    (coarseChain : ReachableChain coarse initial)
    (p : ℕ)
    (hprefix : ∀ j < p, coarse (j + 1) = nodes (j + 1))
    (hshift : ∀ r : ℕ, coarse (p + r + 1) = nodes (p + r + 2))
    {U : Set M} (hU : IsOpen U)
    (hq : coarse (p + 1) ∈ U)
    (hEq : EqOn (coarseChain.state p).germ
      (refinedChain.state (p + 1)).germ U) :
    (coarseChain.state p = refinedChain.state p) ∧
      ∀ r : ℕ,
        coarseChain.state (p + r + 1) =
          refinedChain.state (p + r + 2) := by
  have hprefixState : coarseChain.state p = refinedChain.state p :=
    ReachableChain.state_eq_of_prefix_nodes
      coarseChain refinedChain p hprefix
  have hfirstNode : coarse (p + 1) = nodes (p + 2) := by
    simpa using hshift 0
  have hcross : CrossHistorySuccessorAgreement
      (coarseChain.state p) (refinedChain.state (p + 1))
      (coarse (p + 1)) := by
    exact crossHistorySuccessorAgreement_of_eqOn_open_of_anchor_eq
      hfirstNode (coarseChain.data p) (refinedChain.data (p + 1))
        hU hq hEq
  have hfirst : coarseChain.state (p + 1) =
      refinedChain.state (p + 2) := by
    calc
      coarseChain.state (p + 1) = (coarseChain.data p).successor :=
        coarseChain.state_succ p
      _ = (refinedChain.data (p + 1)).successor :=
        successor_eq_of_crossHistoryAgreement_of_anchor_eq
          hfirstNode hcross (coarseChain.data p)
            (refinedChain.data (p + 1))
      _ = refinedChain.state (p + 2) := by
        simpa using (refinedChain.state_succ (p + 1)).symm
  refine ⟨hprefixState, ?_⟩
  have htailNodes : ∀ r : ℕ,
      coarse (p + 1 + r + 1) = nodes (p + 2 + r + 1) := by
    intro r
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      hshift (r + 1)
  intro r
  simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    (ReachableChain.state_eq_of_shifted_tail coarseChain refinedChain
      (p + 1) (p + 2) hfirst htailNodes r)

/-- Constant curvature supplies the two honest radii needed for one adaptive
insertion.  The first radius is chosen before testing the inserted node.  Once
the actual differential successor at that node is known, the second radius is
chosen around it; if the next coarse node lies in that equality ball, every
later state of the refined chain agrees with the corresponding coarse state.

This theorem crosses the fixed-node boundary without asserting a radius that
is uniform over unrealized histories. -/
theorem exists_radii_state_eq_after_single_insertion_of_curvature
    [CompactSpace M] [ConnectedSpace M]
    {g : ClosedSmoothRiemannianMetric 3 M}
    (hcurv : HasConstantSectionalCurvature3 g 1)
    {nodes coarse : ℕ → M} {initial : CartanChain.ChainState g}
    (refinedChain : ReachableChain nodes initial)
    (coarseChain : ReachableChain coarse initial)
    (p : ℕ)
    (hprefix : ∀ j < p, coarse (j + 1) = nodes (j + 1))
    (hshift : ∀ r : ℕ, coarse (p + r + 1) = nodes (p + r + 2)) :
    letI : MetricSpace M := g.toMetricSpace
    ∃ epsilon > (0 : ℝ),
      dist (nodes (p + 1)) (refinedChain.state p).anchor < epsilon →
        ∃ radius > (0 : ℝ),
          dist (coarse (p + 1)) (nodes (p + 1)) < radius →
            (coarseChain.state p = refinedChain.state p) ∧
              ∀ r : ℕ,
                coarseChain.state (p + r + 1) =
                  refinedChain.state (p + r + 2) := by
  classical
  letI : MetricSpace M := g.toMetricSpace
  let s := refinedChain.state p
  let x : Unit → M := fun _ ↦ s.anchor
  let target : Unit → RoundSphere3 := fun _ ↦ s.target
  rcases
      DifferentialSuccessorFiniteAnchorRadius.exists_uniform_distance_radius_with_datum_eqOn_ball_on_finite_family
        g hcurv x target with
    ⟨epsilon, hepsilon, hlocal⟩
  refine ⟨epsilon, hepsilon, ?_⟩
  intro hinsert
  have heta : CartanChain.ChainState.mk s.anchor s.target s.alignment = s := by
    cases s
    rfl
  let d : Data
      (CartanChain.ChainState.mk s.anchor s.target s.alignment)
      (nodes (p + 1)) := by
    rw [heta]
    exact refinedChain.data p
  have hsmall : dist (nodes (p + 1)) (x ()) < epsilon := by
    simpa [x, s] using hinsert
  rcases hlocal () s.alignment d hsmall with
    ⟨radius, hradius, hEq⟩
  have hsuccessor : d.successor = refinedChain.state (p + 1) := by
    calc
      d.successor = (refinedChain.data p).successor :=
        Data.successor_eq_of_state_eq_of_anchor_eq heta rfl d
          (refinedChain.data p)
      _ = refinedChain.state (p + 1) :=
        (refinedChain.state_succ p).symm
  have hEqRefined : EqOn (refinedChain.state p).germ
      (refinedChain.state (p + 1)).germ
      (Metric.ball (nodes (p + 1)) radius) := by
    simpa [s, heta, hsuccessor] using hEq
  have hprefixState : coarseChain.state p = refinedChain.state p :=
    ReachableChain.state_eq_of_prefix_nodes
      coarseChain refinedChain p hprefix
  have hEqCoarse : EqOn (coarseChain.state p).germ
      (refinedChain.state (p + 1)).germ
      (Metric.ball (nodes (p + 1)) radius) := by
    simpa [hprefixState] using hEqRefined
  refine ⟨radius, hradius, ?_⟩
  intro hnext
  apply ReachableChain.state_eq_after_single_insertion_of_eqOn_open
    refinedChain coarseChain p hprefix hshift Metric.isOpen_ball
  · simpa only [Metric.mem_ball] using hnext
  · exact hEqCoarse

end DifferentialSuccessorReachableChainRefinement
end Poincare
