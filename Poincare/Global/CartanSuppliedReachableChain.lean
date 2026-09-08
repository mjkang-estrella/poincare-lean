import Poincare.Global.CartanSuppliedDifferentialTransfer

/-!
# Reachable chains for state-dependent supplied interpretations

The policy is external to the geometric state. A realized chain stores
differential data only at reached states. Existence uses an explicit supply
at node-anchored states; no geometric mesh or patch covering is asserted here.
-/

noncomputable section
open Filter Metric Set
open scoped Manifold ContDiff Topology NNReal unitInterval
namespace Poincare
universe u
local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3
variable {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold I ∞ M]
variable {g : ClosedSmoothRiemannianMetric 3 M}

namespace CartanSuppliedReachableChain
open CartanSuppliedDifferentialSuccessor

structure ReachableChain (Q : ℕ → CartanChain.ChainState g → Interpretation g) (nodes : ℕ → M)
    (initial : CartanChain.ChainState g) where
  state : ℕ → CartanChain.ChainState g
  initial_eq : state 0 = initial
  data : ∀ n, Data (Q n (state n)) (state n) (nodes (n + 1))
  successor_eq : ∀ n, state (n + 1) = (data n).successor

def StepAvailable (Q : ℕ → CartanChain.ChainState g → Interpretation g) (nodes : ℕ → M) : Prop :=
  ∀ (n : ℕ) (s : CartanChain.ChainState g), s.anchor = nodes n →
    Nonempty (Data (Q n s) s (nodes (n + 1)))

/-- Dependent recursion retains the anchor equation needed to obtain each next datum. -/
theorem exists_reachableChain :
  ∀ (Q : ℕ → CartanChain.ChainState g → Interpretation g) (nodes : ℕ → M)
    (initial : CartanChain.ChainState g),
    initial.anchor = nodes 0 → StepAvailable Q nodes → Nonempty (ReachableChain Q nodes initial) := by
  intro Q nodes initial hinitial step
  let reached : ∀ n, {s : CartanChain.ChainState g // s.anchor = nodes n} :=
    Nat.rec ⟨initial, hinitial⟩ (fun n s =>
      ⟨(Classical.choice (step n s.1 s.2)).successor, rfl⟩)
  exact ⟨{
    state := fun n => (reached n).1
    initial_eq := rfl
    data := fun n => Classical.choice (step n (reached n).1 (reached n).2)
    successor_eq := fun _ => rfl
  }⟩

/-- Every reached state is anchored at its corresponding node. -/
theorem state_anchor_eq_node :
  ∀ (Q : ℕ → CartanChain.ChainState g → Interpretation g) (nodes : ℕ → M)
    (initial : CartanChain.ChainState g) (c : ReachableChain Q nodes initial),
    initial.anchor = nodes 0 → ∀ n, (c.state n).anchor = nodes n := by
  intro Q nodes initial c hinitial n
  cases n with
  | zero => exact (congrArg CartanChain.ChainState.anchor c.initial_eq).trans hinitial
  | succ n =>
      rw [c.successor_eq n]
      rfl

/-- Each next node lies in the actual supplied source of its reached predecessor. -/
theorem node_mem_predecessor_source :
  ∀ (Q : ℕ → CartanChain.ChainState g → Interpretation g) (nodes : ℕ → M)
    (initial : CartanChain.ChainState g) (c : ReachableChain Q nodes initial) (n : ℕ),
    nodes (n + 1) ∈ (germ (Q n (c.state n)) (c.state n)).source := by
  intro Q nodes initial c n
  exact (c.data n).source_mem

/-- Equal reached states feed the same policy, and differential witness choice is irrelevant. -/
theorem state_eq :
  ∀ (Q : ℕ → CartanChain.ChainState g → Interpretation g) (nodes : ℕ → M)
    (initial : CartanChain.ChainState g) (c e : ReachableChain Q nodes initial),
    ∀ n, c.state n = e.state n := by
  intro Q nodes initial c e n
  induction n with
  | zero => exact c.initial_eq.trans e.initial_eq.symm
  | succ n ih =>
      rw [c.successor_eq n, e.successor_eq n]
      have compare : ∀ (s t : CartanChain.ChainState g), s = t →
          ∀ (d : Data (Q n s) s (nodes (n + 1)))
            (f : Data (Q n t) t (nodes (n + 1))), d.successor = f.successor := by
        intro s t h d f
        subst t
        exact CartanSuppliedDifferentialTransfer.successor_eq (Q n s) s
          (nodes (n + 1)) d f
      exact compare (c.state n) (e.state n) ih (c.data n) (e.data n)

end CartanSuppliedReachableChain
end Poincare
