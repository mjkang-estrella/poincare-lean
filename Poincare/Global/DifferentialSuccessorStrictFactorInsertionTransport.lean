import Poincare.Global.DifferentialSuccessorFiniteInsertionRefinement

/-!
# Turning a strict refinement factor into realized single-node insertions

Suppose a finite refined subdivision `refined` retains the displayed coarse
nodes `seed 0, ..., seed k` through a strictly increasing index map `e`.
This file turns that factorization into an explicit insertion construction.

Between `e n` and `e (n+1)` we insert the finite list of refined nodes lying
strictly between the two retained coarse nodes.  Iterating those blocks gives
a sequence whose prefix through `e n` is the refined prefix and whose tail is
the unprocessed coarse tail.  Each block is itself the prefix-by-prefix
single-node schedule from
`DifferentialSuccessorFiniteInsertionRefinement`.

The final theorem consumes equality patches on those actual intermediate
histories and identifies the coarse reached state at `k` with the refined
reached state at `K`.  No counterfactual differential-data policy is used.
-/

noncomputable section

open Set
open scoped Manifold ContDiff Topology

namespace Poincare
namespace DifferentialSuccessorStrictFactorInsertionTransport

universe u v

open DifferentialInducedSuccessor
open DifferentialInducedSuccessor.Chain
open DifferentialSuccessorFiniteInsertionRefinement
open DifferentialSuccessorReachableChainRefinement

/-- The refined nodes strictly between two consecutive retained coarse
nodes. -/
def factorGapNodes {X : Type v} (refined : ℕ → X) (e : ℕ → ℕ)
    (n : ℕ) : List X :=
  List.ofFn fun i : Fin (e (n + 1) - e n - 1) ↦
    refined (e n + 1 + i)

@[simp]
theorem factorGapNodes_length {X : Type v} (refined : ℕ → X)
    (e : ℕ → ℕ) (n : ℕ) :
    (factorGapNodes refined e n).length = e (n + 1) - e n - 1 := by
  simp [factorGapNodes]

@[simp]
theorem factorGapNodes_get {X : Type v} (refined : ℕ → X)
    (e : ℕ → ℕ) (n : ℕ)
    (i : Fin (factorGapNodes refined e n).length) :
    (factorGapNodes refined e n).get i = refined (e n + 1 + i) := by
  simp [factorGapNodes]

/-- Strictness makes the retained right endpoint occur immediately after the
whole interstitial block. -/
theorem factorGapNodes_endpoint {X : Type v} (refined : ℕ → X)
    (e : ℕ → ℕ) (n : ℕ) (hstrict : e n < e (n + 1)) :
    e n + 1 + (factorGapNodes refined e n).length = e (n + 1) := by
  simp only [factorGapNodes_length]
  omega

/-- A strictly increasing factor map starting at zero cannot place its
`n`-th retained node before index `n`. -/
theorem strictFactorIndex_le (e : ℕ → ℕ) (k : ℕ)
    (heZero : e 0 = 0) (heStrict : ∀ n < k, e n < e (n + 1)) :
    ∀ n ≤ k, n ≤ e n := by
  intro n
  induction n with
  | zero =>
      intro _hn
      simp [heZero]
  | succ n ih =>
      intro hn
      have hnlt : n < k := by omega
      have hprev := ih (Nat.le_of_lt hnlt)
      have hstep := heStrict n hnlt
      omega

/-- Insert the interstitial refined block in each coarse gap, from left to
right. -/
def factorRefinementStage {X : Type v} (seed refined : ℕ → X)
    (e : ℕ → ℕ) : ℕ → ℕ → X
  | 0 => seed
  | n + 1 =>
      insertNodeList (factorRefinementStage seed refined e n) (e n)
        (factorGapNodes refined e n)

@[simp]
theorem factorRefinementStage_zero {X : Type v} (seed refined : ℕ → X)
    (e : ℕ → ℕ) :
    factorRefinementStage seed refined e 0 = seed :=
  rfl

@[simp]
theorem factorRefinementStage_succ {X : Type v} (seed refined : ℕ → X)
    (e : ℕ → ℕ) (n : ℕ) :
    factorRefinementStage seed refined e (n + 1) =
      insertNodeList (factorRefinementStage seed refined e n) (e n)
        (factorGapNodes refined e n) :=
  rfl

/-- Inside one factor gap, the explicit schedule advances by one genuine
`insertNodeSequence` operation. -/
theorem factorGapSchedule_succ {X : Type v} (seed refined : ℕ → X)
    (e : ℕ → ℕ) (n i : ℕ)
    (hi : i < (factorGapNodes refined e n).length) :
    insertNodeListSchedule (factorRefinementStage seed refined e n) (e n)
        (factorGapNodes refined e n) (i + 1) =
      insertNodeSequence
        (insertNodeListSchedule (factorRefinementStage seed refined e n)
          (e n) (factorGapNodes refined e n) i)
        (e n + i) (factorGapNodes refined e n)[i] := by
  exact insertNodeListSchedule_succ _ _ _ i hi

/-- After processing the first `n` gaps, the prefix through the retained node
`e n` is exactly the refined prefix, while the entire remaining tail is the
coarse tail shifted so that `seed n` sits at `e n`. -/
theorem factorRefinementStage_prefix_tail {X : Type v}
    (seed refined : ℕ → X) (e : ℕ → ℕ) (k : ℕ)
    (heZero : e 0 = 0)
    (heStrict : ∀ n < k, e n < e (n + 1))
    (heValue : ∀ n ≤ k, refined (e n) = seed n) :
    ∀ n ≤ k,
      (∀ j ≤ e n, factorRefinementStage seed refined e n j = refined j) ∧
      (∀ q, factorRefinementStage seed refined e n (e n + q) =
        seed (n + q)) := by
  intro n hn
  induction n with
  | zero =>
      constructor
      · intro j hj
        have hjZero : j = 0 := by omega
        subst j
        simpa [heZero] using (heValue 0 (Nat.zero_le k)).symm
      · intro q
        simp [heZero]
  | succ n ih =>
      have hnlt : n < k := by omega
      have hstrict : e n < e (n + 1) := heStrict n hnlt
      have hendpoint :
          e n + 1 + (factorGapNodes refined e n).length = e (n + 1) :=
        factorGapNodes_endpoint refined e n hstrict
      rcases ih (Nat.le_of_lt hnlt) with ⟨hprefix, htail⟩
      constructor
      · intro j hj
        by_cases hjLeft : j ≤ e n
        · calc
            factorRefinementStage seed refined e (n + 1) j =
                factorRefinementStage seed refined e n j := by
              exact insertNodeList_eq_of_le _ _ _ hjLeft
            _ = refined j := hprefix j hjLeft
        · by_cases hjRight : j = e (n + 1)
          · subst j
            have hshift := insertNodeList_shifted
              (factorRefinementStage seed refined e n) (e n) 0
              (factorGapNodes refined e n)
            have htailOne := htail 1
            calc
              factorRefinementStage seed refined e (n + 1) (e (n + 1)) =
                  factorRefinementStage seed refined e n (e n + 1) := by
                rw [factorRefinementStage_succ]
                rw [← hendpoint]
                simpa only [Nat.add_zero] using hshift
              _ = seed (n + 1) := by simpa using htailOne
              _ = refined (e (n + 1)) :=
                (heValue (n + 1) hn).symm
          · have hjLower : e n + 1 ≤ j := by omega
            have hjUpper : j < e (n + 1) := by omega
            let iVal := j - (e n + 1)
            have hiBound : iVal < (factorGapNodes refined e n).length := by
              dsimp [iVal]
              rw [factorGapNodes_length]
              omega
            let i : Fin (factorGapNodes refined e n).length :=
              ⟨iVal, hiBound⟩
            have hindex : e n + 1 + (i : ℕ) = j := by
              dsimp [i, iVal]
              omega
            calc
              factorRefinementStage seed refined e (n + 1) j =
                  insertNodeList (factorRefinementStage seed refined e n)
                    (e n) (factorGapNodes refined e n)
                    (e n + 1 + (i : ℕ)) := by
                rw [factorRefinementStage_succ, hindex]
              _ = (factorGapNodes refined e n).get i :=
                insertNodeList_get _ _ _ i
              _ = refined (e n + 1 + (i : ℕ)) :=
                factorGapNodes_get refined e n i
              _ = refined j := by rw [hindex]
      · intro q
        have hshift := insertNodeList_shifted
          (factorRefinementStage seed refined e n) (e n) q
          (factorGapNodes refined e n)
        have htailNext := htail (q + 1)
        calc
          factorRefinementStage seed refined e (n + 1)
              (e (n + 1) + q) =
              factorRefinementStage seed refined e n (e n + q + 1) := by
            rw [factorRefinementStage_succ]
            rw [← hendpoint]
            simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
              hshift
          _ = seed (n + (q + 1)) := by
            simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
              htailNext
          _ = seed (n + 1 + q) := by
            congr 1
            omega

/-- At the last retained coarse node, the staged construction agrees with the
whole refined prefix through its factor index. -/
theorem factorRefinementStage_factor_prefix {X : Type v}
    (seed refined : ℕ → X) (e : ℕ → ℕ) (k : ℕ)
    (heZero : e 0 = 0)
    (heStrict : ∀ n < k, e n < e (n + 1))
    (heValue : ∀ n ≤ k, refined (e n) = seed n) :
    ∀ j ≤ e k, factorRefinementStage seed refined e k j = refined j := by
  intro j hj
  exact (factorRefinementStage_prefix_tail seed refined e k heZero heStrict
    heValue k le_rfl).1 j hj

/-- If the last retained factor index is named `K`, the factor-prefix theorem
may be stated using that terminal name. -/
theorem factorRefinementStage_terminal_prefix {X : Type v}
    (seed refined : ℕ → X) (e : ℕ → ℕ) (k K : ℕ)
    (heZero : e 0 = 0)
    (heStrict : ∀ n < k, e n < e (n + 1))
    (heTerminal : e k = K)
    (heValue : ∀ n ≤ k, refined (e n) = seed n) :
    ∀ j ≤ K, factorRefinementStage seed refined e k j = refined j := by
  rw [← heTerminal]
  exact factorRefinementStage_factor_prefix seed refined e k heZero heStrict
    heValue

/-- The number of inserted nodes in the first `n` factor gaps is exactly
`e n - n`. -/
theorem factorRefinementStage_insertedCount (e : ℕ → ℕ) (k : ℕ)
    (heZero : e 0 = 0) (heStrict : ∀ n < k, e n < e (n + 1)) :
    ∀ n ≤ k,
      (∑ i ∈ Finset.range n, (e (i + 1) - e i - 1)) = e n - n := by
  intro n hn
  induction n with
  | zero => simp [heZero]
  | succ n ih =>
      have hnlt : n < k := by omega
      have hstrict := heStrict n hnlt
      have hen : n ≤ e n :=
        strictFactorIndex_le e k heZero heStrict n (Nat.le_of_lt hnlt)
      rw [Finset.sum_range_succ, ih (Nat.le_of_lt hnlt)]
      omega

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace E M]
variable [IsManifold I ∞ M]

/-- A strict finite factorization transports realized differential-successor
states from the coarse terminal node to the refined terminal node.

For each coarse gap, `chain n i` is the actual realized history after the
first `i` interstitial nodes of that gap have been inserted.  The local
`EqOn` premise is therefore attached only to realized predecessor and
successor histories. -/
theorem ReachableChain.state_eq_of_strict_factor_of_gap_eqOn_open
    {g : ClosedSmoothRiemannianMetric 3 M}
    (seed refined : ℕ → M) {initial : CartanChain.ChainState g}
    (k : ℕ) (e : ℕ → ℕ)
    (heZero : e 0 = 0)
    (heStrict : ∀ n < k, e n < e (n + 1))
    (heValue : ∀ n ≤ k, refined (e n) = seed n)
    (coarseChain : ReachableChain seed initial)
    (refinedChain : ReachableChain refined initial)
    (chain : ∀ n i : ℕ,
      ReachableChain
        (insertNodeListSchedule
          (factorRefinementStage seed refined e n) (e n)
          (factorGapNodes refined e n) i) initial)
    (U : ℕ → ℕ → Set M)
    (hU : ∀ n < k, ∀ i < (factorGapNodes refined e n).length,
      IsOpen (U n i))
    (hq : ∀ n < k, ∀ i < (factorGapNodes refined e n).length,
      insertNodeListSchedule
          (factorRefinementStage seed refined e n) (e n)
          (factorGapNodes refined e n) i (e n + i + 1) ∈ U n i)
    (hEq : ∀ n < k, ∀ i < (factorGapNodes refined e n).length,
      EqOn ((chain n i).state (e n + i)).germ
        ((chain n (i + 1)).state (e n + i + 1)).germ (U n i)) :
    coarseChain.state k = refinedChain.state (e k) := by
  have hstage : ∀ n ≤ k,
      coarseChain.state k =
        (chain n 0).state (k + (e n - n)) := by
    intro n hn
    induction n with
    | zero =>
        have hnodes : ∀ j < k,
            seed (j + 1) =
              insertNodeListSchedule
                (factorRefinementStage seed refined e 0) (e 0)
                (factorGapNodes refined e 0) 0 (j + 1) := by
          intro j hj
          simp [heZero]
        simpa [heZero] using
          ReachableChain.state_eq_of_prefix_nodes
            coarseChain (chain 0 0) k hnodes
    | succ n ih =>
        have hnlt : n < k := by omega
        have hstrict : e n < e (n + 1) := heStrict n hnlt
        let gap := factorGapNodes refined e n
        let L := k + (e n - n)
        have hterminalGap : e n + 1 ≤ L := by
          dsimp [L]
          have hen : n ≤ e n :=
            strictFactorIndex_le e k heZero heStrict n
              (Nat.le_of_lt hnlt)
          omega
        have hblock :
            (chain n 0).state L =
              (chain n gap.length).state (L + gap.length) := by
          apply ReachableChain.state_eq_after_insertNodeList_of_eqOn_open
            (coarse := factorRefinementStage seed refined e n)
            (p := e n) (zs := gap) (chain := chain n)
            (L := L) hterminalGap (U := U n)
          · intro i hi
            exact hU n hnlt i hi
          · intro i hi
            exact hq n hnlt i hi
          · intro i hi
            exact hEq n hnlt i hi
        have hendpointNodes : ∀ j < L + gap.length,
            insertNodeListSchedule
                (factorRefinementStage seed refined e n) (e n) gap
                gap.length (j + 1) =
              insertNodeListSchedule
                (factorRefinementStage seed refined e (n + 1)) (e (n + 1))
                (factorGapNodes refined e (n + 1)) 0 (j + 1) := by
          intro j hj
          dsimp [gap]
          simp only [insertNodeListSchedule_length,
            insertNodeListSchedule_zero]
        have hconnect := ReachableChain.state_eq_of_prefix_nodes
          (chain n gap.length) (chain (n + 1) 0)
          (L + gap.length) hendpointNodes
        have hindex : L + gap.length =
            k + (e (n + 1) - (n + 1)) := by
          have hen : n ≤ e n :=
            strictFactorIndex_le e k heZero heStrict n
              (Nat.le_of_lt hnlt)
          dsimp [L, gap]
          rw [factorGapNodes_length]
          omega
        calc
          coarseChain.state k = (chain n 0).state L := ih (Nat.le_of_lt hnlt)
          _ = (chain n gap.length).state (L + gap.length) := hblock
          _ = (chain (n + 1) 0).state (L + gap.length) := hconnect
          _ = (chain (n + 1) 0).state
                (k + (e (n + 1) - (n + 1))) := by
            rw [hindex]
  have hcoarseToTerminal := hstage k le_rfl
  have hkIndex : k ≤ e k :=
    strictFactorIndex_le e k heZero heStrict k le_rfl
  have hcount : k + (e k - k) = e k := by omega
  have hterminalPrefix := factorRefinementStage_factor_prefix
    seed refined e k heZero heStrict heValue
  have hfinalNodes : ∀ j < e k,
      insertNodeListSchedule
          (factorRefinementStage seed refined e k) (e k)
          (factorGapNodes refined e k) 0 (j + 1) = refined (j + 1) := by
    intro j hj
    simp only [insertNodeListSchedule_zero]
    exact hterminalPrefix (j + 1) (by omega)
  have hterminalToRefined := ReachableChain.state_eq_of_prefix_nodes
    (chain k 0) refinedChain (e k) hfinalNodes
  rw [hcount] at hcoarseToTerminal
  exact hcoarseToTerminal.trans hterminalToRefined

/-- Named-terminal corollary of
`state_eq_of_strict_factor_of_gap_eqOn_open`. -/
theorem ReachableChain.state_eq_of_strict_factor_of_gap_eqOn_open_at_terminal
    {g : ClosedSmoothRiemannianMetric 3 M}
    (seed refined : ℕ → M) {initial : CartanChain.ChainState g}
    (k K : ℕ) (e : ℕ → ℕ)
    (heZero : e 0 = 0)
    (heStrict : ∀ n < k, e n < e (n + 1))
    (heTerminal : e k = K)
    (heValue : ∀ n ≤ k, refined (e n) = seed n)
    (coarseChain : ReachableChain seed initial)
    (refinedChain : ReachableChain refined initial)
    (chain : ∀ n i : ℕ,
      ReachableChain
        (insertNodeListSchedule
          (factorRefinementStage seed refined e n) (e n)
          (factorGapNodes refined e n) i) initial)
    (U : ℕ → ℕ → Set M)
    (hU : ∀ n < k, ∀ i < (factorGapNodes refined e n).length,
      IsOpen (U n i))
    (hq : ∀ n < k, ∀ i < (factorGapNodes refined e n).length,
      insertNodeListSchedule
          (factorRefinementStage seed refined e n) (e n)
          (factorGapNodes refined e n) i (e n + i + 1) ∈ U n i)
    (hEq : ∀ n < k, ∀ i < (factorGapNodes refined e n).length,
      EqOn ((chain n i).state (e n + i)).germ
        ((chain n (i + 1)).state (e n + i + 1)).germ (U n i)) :
    coarseChain.state k = refinedChain.state K := by
  rw [← heTerminal]
  exact ReachableChain.state_eq_of_strict_factor_of_gap_eqOn_open
    seed refined k e heZero heStrict heValue coarseChain refinedChain chain U
    hU hq hEq

end DifferentialSuccessorStrictFactorInsertionTransport
end Poincare
