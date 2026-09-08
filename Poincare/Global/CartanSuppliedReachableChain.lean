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

end CartanSuppliedReachableChain
end Poincare
