import Poincare.Global.DifferentialSuccessorFiniteSubdivisionRefinement

/-!
# Finite iteration of differential-successor insertion invariance

`DifferentialSuccessorReachableChainRefinement` proves that one inserted node
shifts every sufficiently late reached state by one index.  This file iterates
that statement through an arbitrary finite family of realized refinements.

The cutoff for the `i`-th insertion is allowed to depend on `i`.  Thus no
global history-independent radius or counterfactual successor datum is hidden
in the result: every local equality patch belongs to the actual pair of
realized chains at that insertion step.
-/

noncomputable section

open Set
open scoped Manifold ContDiff Topology

namespace Poincare
namespace DifferentialSuccessorFiniteInsertionRefinement

universe u v

open DifferentialInducedSuccessor
open DifferentialInducedSuccessor.Chain
open DifferentialSuccessorAdjacentContinuation
open DifferentialSuccessorReachableChainRefinement

/-- Insert one node immediately after index `p` in a natural-number-indexed
sequence.  All later old nodes are shifted by one. -/
def insertNodeSequence {X : Type v}
    (coarse : ℕ → X) (p : ℕ) (z : X) : ℕ → X :=
  fun n ↦
    if n ≤ p then coarse n
    else if n = p + 1 then z
    else coarse (n - 1)

theorem insertNodeSequence_eq_of_le {X : Type v}
    (coarse : ℕ → X) (p : ℕ) (z : X) {n : ℕ} (hn : n ≤ p) :
    insertNodeSequence coarse p z n = coarse n := by
  simp [insertNodeSequence, hn]

@[simp]
theorem insertNodeSequence_inserted {X : Type v}
    (coarse : ℕ → X) (p : ℕ) (z : X) :
    insertNodeSequence coarse p z (p + 1) = z := by
  simp [insertNodeSequence]

/-- Every old tail node occurs one index later after a single insertion. -/
theorem insertNodeSequence_shifted {X : Type v}
    (coarse : ℕ → X) (p r : ℕ) (z : X) :
    insertNodeSequence coarse p z (p + r + 2) =
      coarse (p + r + 1) := by
  have hnotle : ¬p + r + 2 ≤ p := by omega
  have hnotinsert : p + r + 2 ≠ p + 1 := by omega
  simp only [insertNodeSequence, if_neg hnotle, if_neg hnotinsert]
  congr 1

/-- Insert a finite list of nodes, in list order, immediately after index
`p`. -/
def insertNodeList {X : Type v}
    (coarse : ℕ → X) (p : ℕ) : List X → (ℕ → X)
  | [] => coarse
  | z :: zs =>
      insertNodeList (insertNodeSequence coarse p z) (p + 1) zs

@[simp]
theorem insertNodeList_nil {X : Type v} (coarse : ℕ → X) (p : ℕ) :
    insertNodeList coarse p [] = coarse :=
  rfl

/-- Inserting a list after `p` leaves the entire prefix through `p`
unchanged. -/
theorem insertNodeList_eq_of_le {X : Type v}
    (coarse : ℕ → X) (p : ℕ) (zs : List X)
    {n : ℕ} (hn : n ≤ p) :
    insertNodeList coarse p zs n = coarse n := by
  induction zs generalizing coarse p with
  | nil => rfl
  | cons z zs ih =>
      change insertNodeList (insertNodeSequence coarse p z) (p + 1) zs n =
        coarse n
      exact (ih _ _ (by omega)).trans
        (insertNodeSequence_eq_of_le coarse p z hn)

/-- The inserted list occupies exactly the consecutive indices following
`p`. -/
theorem insertNodeList_get {X : Type v}
    (coarse : ℕ → X) (p : ℕ) (zs : List X) (i : Fin zs.length) :
    insertNodeList coarse p zs (p + 1 + i) = zs.get i := by
  induction zs generalizing coarse p with
  | nil => exact Fin.elim0 i
  | cons z zs ih =>
      refine Fin.cases ?_ (fun j ↦ ?_) i
      · change insertNodeList (insertNodeSequence coarse p z) (p + 1) zs
          (p + 1 + (0 : ℕ)) = z
        calc
          _ = insertNodeSequence coarse p z (p + 1) :=
            insertNodeList_eq_of_le _ _ _ (by omega)
          _ = z := insertNodeSequence_inserted coarse p z
      · change insertNodeList (insertNodeSequence coarse p z) (p + 1) zs
          (p + 1 + (j.succ : ℕ)) = zs.get j
        have h := ih (insertNodeSequence coarse p z) (p + 1) j
        rw [show p + 1 + (j.succ : ℕ) =
            (p + 1) + 1 + (j : ℕ) by
          simp only [Fin.val_succ]
          omega]
        exact h

/-- Every old tail node occurs `zs.length` indices later after inserting the
finite list. -/
theorem insertNodeList_shifted {X : Type v}
    (coarse : ℕ → X) (p r : ℕ) (zs : List X) :
    insertNodeList coarse p zs (p + r + 1 + zs.length) =
      coarse (p + r + 1) := by
  induction zs generalizing coarse p with
  | nil => simp [insertNodeList]
  | cons z zs ih =>
      change insertNodeList (insertNodeSequence coarse p z) (p + 1) zs
        (p + r + 1 + (z :: zs).length) = coarse (p + r + 1)
      have h := ih (insertNodeSequence coarse p z) (p + 1)
      have hidx : p + r + 1 + (z :: zs).length =
          (p + 1) + r + 1 + zs.length := by
        simp only [List.length_cons]
        omega
      calc
        _ = insertNodeList (insertNodeSequence coarse p z) (p + 1) zs
            ((p + 1) + r + 1 + zs.length) := by rw [hidx]
        _ = insertNodeSequence coarse p z ((p + 1) + r + 1) := h
        _ = coarse (p + r + 1) := by
          simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            insertNodeSequence_shifted coarse p r z

/-- Inserting two lists successively is the same as inserting their
concatenation.  The second insertion point is shifted by the length of the
first list, so its nodes continue immediately after the first block. -/
theorem insertNodeList_append {X : Type v}
    (coarse : ℕ → X) (p : ℕ) (as bs : List X) :
    insertNodeList coarse p (as ++ bs) =
      insertNodeList (insertNodeList coarse p as) (p + as.length) bs := by
  induction as generalizing coarse p with
  | nil => simp [insertNodeList]
  | cons z as ih =>
      change
        insertNodeList (insertNodeSequence coarse p z) (p + 1) (as ++ bs) =
          insertNodeList
            (insertNodeList (insertNodeSequence coarse p z) (p + 1) as)
            (p + (z :: as).length) bs
      have hindex : (p + 1) + as.length = p + (z :: as).length := by
        simp only [List.length_cons]
        omega
      calc
        _ = insertNodeList
              (insertNodeList (insertNodeSequence coarse p z) (p + 1) as)
              ((p + 1) + as.length) bs :=
            ih (insertNodeSequence coarse p z) (p + 1)
        _ = _ := by rw [hindex]

/-- The chain of intermediate node sequences obtained by inserting the first
`i` members of a finite list. -/
def insertNodeListSchedule {X : Type v}
    (coarse : ℕ → X) (p : ℕ) (zs : List X) (i : ℕ) : ℕ → X :=
  insertNodeList coarse p (zs.take i)

@[simp]
theorem insertNodeListSchedule_zero {X : Type v}
    (coarse : ℕ → X) (p : ℕ) (zs : List X) :
    insertNodeListSchedule coarse p zs 0 = coarse := by
  simp [insertNodeListSchedule]

/-- One step of the prefix schedule is literally a single-node insertion at
the next consecutive index. -/
theorem insertNodeListSchedule_succ {X : Type v}
    (coarse : ℕ → X) (p : ℕ) (zs : List X) (i : ℕ)
    (hi : i < zs.length) :
    insertNodeListSchedule coarse p zs (i + 1) =
      insertNodeSequence (insertNodeListSchedule coarse p zs i)
        (p + i) zs[i] := by
  change insertNodeList coarse p (zs.take (i + 1)) =
    insertNodeSequence (insertNodeList coarse p (zs.take i)) (p + i) zs[i]
  rw [show zs.take (i + 1) = zs.take i ++ [zs[i]] by
    exact List.take_succ_eq_append_getElem hi]
  rw [insertNodeList_append]
  simp only [List.length_take, Nat.min_eq_left hi.le, insertNodeList]

@[simp]
theorem insertNodeListSchedule_length {X : Type v}
    (coarse : ℕ → X) (p : ℕ) (zs : List X) :
    insertNodeListSchedule coarse p zs zs.length =
      insertNodeList coarse p zs := by
  simp [insertNodeListSchedule]

/-- At one genuine step of the prefix schedule, the old prefix through the
current insertion point is unchanged. -/
theorem insertNodeListSchedule_succ_eq_of_le {X : Type v}
    (coarse : ℕ → X) (p : ℕ) (zs : List X) (i n : ℕ)
    (hi : i < zs.length) (hn : n ≤ p + i) :
    insertNodeListSchedule coarse p zs (i + 1) n =
      insertNodeListSchedule coarse p zs i n := by
  rw [insertNodeListSchedule_succ coarse p zs i hi]
  exact insertNodeSequence_eq_of_le _ _ _ hn

/-- At one genuine step of the prefix schedule, every old tail node occurs
one index later. -/
theorem insertNodeListSchedule_succ_shifted {X : Type v}
    (coarse : ℕ → X) (p : ℕ) (zs : List X) (i r : ℕ)
    (hi : i < zs.length) :
    insertNodeListSchedule coarse p zs (i + 1) (p + i + r + 2) =
      insertNodeListSchedule coarse p zs i (p + i + r + 1) := by
  rw [insertNodeListSchedule_succ coarse p zs i hi]
  exact insertNodeSequence_shifted _ _ _ _

/-- The new node at schedule step `i` is the `i`-th member of the insertion
list. -/
theorem insertNodeListSchedule_succ_inserted {X : Type v}
    (coarse : ℕ → X) (p : ℕ) (zs : List X) (i : ℕ)
    (hi : i < zs.length) :
    insertNodeListSchedule coarse p zs (i + 1) (p + i + 1) = zs[i] := by
  rw [insertNodeListSchedule_succ coarse p zs i hi]
  exact insertNodeSequence_inserted _ _ _

/-- Iterate finitely many tail equalities, each of which shifts the second
index by one.  This is the arithmetic core of finite insertion invariance. -/
theorem eq_after_finite_unit_shifts {S : Type v}
    (state : ℕ → ℕ → S) (cutoff : ℕ → ℕ) (N L : ℕ)
    (hstep : ∀ i < N, ∀ q ≥ cutoff i,
      state i q = state (i + 1) (q + 1))
    (hcutoff : ∀ i < N, cutoff i ≤ L + i) :
    state 0 L = state N (L + N) := by
  have hind : ∀ i ≤ N, state 0 L = state i (L + i) := by
    intro i hi
    induction i with
    | zero => simp
    | succ i ih =>
        have hiN : i < N := Nat.lt_of_succ_le hi
        calc
          state 0 L = state i (L + i) := ih hiN.le
          _ = state (i + 1) (L + i + 1) :=
            hstep i hiN (L + i) (hcutoff i hiN)
          _ = state (i + 1) (L + (i + 1)) := by rw [Nat.add_assoc]
  exact hind N le_rfl

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace E M]
variable [IsManifold I ∞ M]

/-- A one-insertion equality patch gives the tail-shift equality at every
index at or beyond the first old node following the insertion. -/
theorem ReachableChain.state_eq_tail_of_single_insertion_of_eqOn_open
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
    ∀ q ≥ p + 1,
      coarseChain.state q = refinedChain.state (q + 1) := by
  rcases ReachableChain.state_eq_after_single_insertion_of_eqOn_open
      refinedChain coarseChain p hprefix hshift hU hq hEq with
    ⟨_hprefixState, htail⟩
  intro q hqLower
  let r := q - (p + 1)
  have hleft : p + r + 1 = q := by
    dsimp [r]
    omega
  have hright : p + r + 2 = q + 1 := by omega
  simpa only [hleft, hright] using htail r

/-- Specialized tail invariance for the explicit `insertNodeSequence`
constructor. -/
theorem ReachableChain.state_eq_tail_of_insertNodeSequence_of_eqOn_open
    {g : ClosedSmoothRiemannianMetric 3 M}
    {coarse : ℕ → M} {initial : CartanChain.ChainState g}
    (p : ℕ) (z : M)
    (refinedChain : ReachableChain (insertNodeSequence coarse p z) initial)
    (coarseChain : ReachableChain coarse initial)
    {U : Set M} (hU : IsOpen U) (hq : coarse (p + 1) ∈ U)
    (hEq : EqOn (coarseChain.state p).germ
      (refinedChain.state (p + 1)).germ U) :
    ∀ q ≥ p + 1,
      coarseChain.state q = refinedChain.state (q + 1) := by
  apply ReachableChain.state_eq_tail_of_single_insertion_of_eqOn_open
    refinedChain coarseChain p
  · intro j hj
    exact (insertNodeSequence_eq_of_le coarse p z
      (n := j + 1) (by omega)).symm
  · intro r
    exact (insertNodeSequence_shifted coarse p r z).symm
  · exact hU
  · exact hq
  · exact hEq

/-- An arbitrary finite succession of actual single-node refinements preserves
the reached state after accounting for the number of inserted nodes.

At step `i`, `nodes (i+1)` inserts one node into `nodes i` immediately before
the old node at index `p i + 1`.  The local `EqOn` premise is attached to the
two actual realized histories at that step.  If the terminal index `L+i` lies
past that insertion, the final state after `N` insertions is the original
state shifted by exactly `N` indices. -/
theorem ReachableChain.state_eq_after_finite_insertions_of_eqOn_open
    {g : ClosedSmoothRiemannianMetric 3 M}
    (nodes : ℕ → ℕ → M) {initial : CartanChain.ChainState g}
    (chain : ∀ i : ℕ, ReachableChain (nodes i) initial)
    (p : ℕ → ℕ) (N L : ℕ)
    (hprefix : ∀ i < N, ∀ j < p i,
      nodes i (j + 1) = nodes (i + 1) (j + 1))
    (hshift : ∀ i < N, ∀ r : ℕ,
      nodes i (p i + r + 1) = nodes (i + 1) (p i + r + 2))
    (U : ℕ → Set M)
    (hU : ∀ i < N, IsOpen (U i))
    (hq : ∀ i < N, nodes i (p i + 1) ∈ U i)
    (hEq : ∀ i < N,
      EqOn ((chain i).state (p i)).germ
        ((chain (i + 1)).state (p i + 1)).germ (U i))
    (hterminal : ∀ i < N, p i + 1 ≤ L + i) :
    (chain 0).state L = (chain N).state (L + N) := by
  apply eq_after_finite_unit_shifts
    (state := fun i q ↦ (chain i).state q)
    (cutoff := fun i ↦ p i + 1)
  · intro i hi q hiq
    exact ReachableChain.state_eq_tail_of_single_insertion_of_eqOn_open
      (chain (i + 1)) (chain i) (p i)
      (hprefix i hi) (hshift i hi) (hU i hi) (hq i hi)
      (hEq i hi) q hiq
  · exact hterminal

/-- A finite list inserted consecutively after one node has the same reached
state as the original history, shifted by the list length, provided each
realized one-node insertion has its local equality patch.

Unlike a statement merely comparing the endpoint node sequences, this theorem
records every intermediate realized history through `insertNodeListSchedule`.
Thus every equality premise is attached to the actual predecessor and
successor chains used at that insertion. -/
theorem ReachableChain.state_eq_after_insertNodeList_of_eqOn_open
    {g : ClosedSmoothRiemannianMetric 3 M}
    (coarse : ℕ → M) {initial : CartanChain.ChainState g}
    (p : ℕ) (zs : List M)
    (chain : ∀ i : ℕ,
      ReachableChain (insertNodeListSchedule coarse p zs i) initial)
    (L : ℕ) (hterminal : p + 1 ≤ L)
    (U : ℕ → Set M)
    (hU : ∀ i < zs.length, IsOpen (U i))
    (hq : ∀ i < zs.length,
      insertNodeListSchedule coarse p zs i (p + i + 1) ∈ U i)
    (hEq : ∀ i < zs.length,
      EqOn ((chain i).state (p + i)).germ
        ((chain (i + 1)).state (p + i + 1)).germ (U i)) :
    (chain 0).state L =
      (chain zs.length).state (L + zs.length) := by
  apply ReachableChain.state_eq_after_finite_insertions_of_eqOn_open
    (nodes := insertNodeListSchedule coarse p zs)
    (chain := chain) (p := fun i ↦ p + i)
    (N := zs.length) (L := L) (U := U)
  · intro i hi j hj
    have hj' : j < p + i := by simpa using hj
    exact (insertNodeListSchedule_succ_eq_of_le
      coarse p zs i (j + 1) hi (by omega)).symm
  · intro i hi r
    exact (insertNodeListSchedule_succ_shifted
      coarse p zs i r hi).symm
  · exact hU
  · exact hq
  · exact hEq
  · intro i hi
    omega

/-- Constant curvature supplies the radii needed by every insertion in a
finite realized refinement.

The quantifier order records the honest adaptive dependency.  First one
positive radius is selected at each already-realized predecessor state.  Once
the actual inserted nodes satisfy those bounds, the post-insertion equality
patches supply a second finite family of positive radii.  Closeness of the old
next nodes inside those second radii then identifies the terminal states. -/
theorem ReachableChain.exists_radii_state_eq_after_finite_insertions_of_curvature
    [CompactSpace M] [ConnectedSpace M]
    {g : ClosedSmoothRiemannianMetric 3 M}
    (hcurv : HasConstantSectionalCurvature3 g 1)
    (nodes : ℕ → ℕ → M) {initial : CartanChain.ChainState g}
    (chain : ∀ i : ℕ, ReachableChain (nodes i) initial)
    (p : ℕ → ℕ) (N L : ℕ)
    (hprefix : ∀ i < N, ∀ j < p i,
      nodes i (j + 1) = nodes (i + 1) (j + 1))
    (hshift : ∀ i < N, ∀ r : ℕ,
      nodes i (p i + r + 1) = nodes (i + 1) (p i + r + 2))
    (hterminal : ∀ i < N, p i + 1 ≤ L + i) :
    letI : MetricSpace M := g.toMetricSpace
    ∃ epsilon : Fin N → ℝ,
      (∀ i : Fin N, 0 < epsilon i) ∧
      ((∀ i : Fin N,
        dist (nodes (i + 1) (p i + 1))
          ((chain (i + 1)).state (p i)).anchor < epsilon i) →
        ∃ radius : Fin N → ℝ,
          (∀ i : Fin N, 0 < radius i) ∧
          ((∀ i : Fin N,
            dist (nodes i (p i + 1))
              (nodes (i + 1) (p i + 1)) < radius i) →
            (chain 0).state L = (chain N).state (L + N))) := by
  classical
  letI : MetricSpace M := g.toMetricSpace
  have hlocal : ∀ i : Fin N,
      ∃ epsilon > (0 : ℝ),
        dist (nodes (i + 1) (p i + 1))
            ((chain (i + 1)).state (p i)).anchor < epsilon →
          ∃ radius > (0 : ℝ),
            dist (nodes i (p i + 1))
                (nodes (i + 1) (p i + 1)) < radius →
              ((chain i).state (p i) =
                  (chain (i + 1)).state (p i)) ∧
                ∀ r : ℕ,
                  (chain i).state (p i + r + 1) =
                    (chain (i + 1)).state (p i + r + 2) := by
    intro i
    exact
      DifferentialSuccessorReachableChainRefinement.exists_radii_state_eq_after_single_insertion_of_curvature
        hcurv (chain (i + 1)) (chain i) (p i)
          (hprefix i i.isLt) (hshift i i.isLt)
  choose epsilon hepsilon hafterInsert using hlocal
  refine ⟨epsilon, hepsilon, ?_⟩
  intro hinsert
  have hsecond : ∀ i : Fin N,
      ∃ radius > (0 : ℝ),
        dist (nodes i (p i + 1))
            (nodes (i + 1) (p i + 1)) < radius →
          ((chain i).state (p i) =
              (chain (i + 1)).state (p i)) ∧
            ∀ r : ℕ,
              (chain i).state (p i + r + 1) =
                (chain (i + 1)).state (p i + r + 2) := by
    intro i
    exact hafterInsert i (hinsert i)
  choose radius hradius htail using hsecond
  refine ⟨radius, hradius, ?_⟩
  intro hnext
  have htailShift : ∀ i < N, ∀ q ≥ p i + 1,
      (chain i).state q = (chain (i + 1)).state (q + 1) := by
    intro i hi q hq
    let fi : Fin N := ⟨i, hi⟩
    have hrealized := (htail fi (hnext fi)).2
    let r := q - (p i + 1)
    have hleft : p i + r + 1 = q := by
      dsimp [r]
      omega
    have hright : p i + r + 2 = q + 1 := by omega
    simpa only [fi, hleft, hright] using hrealized r
  exact eq_after_finite_unit_shifts
    (state := fun i q ↦ (chain i).state q)
    (cutoff := fun i ↦ p i + 1) N L htailShift hterminal

/-- Constant curvature supplies the two adaptive finite radius families for
the concrete prefix-by-prefix insertion schedule of a list. -/
theorem ReachableChain.exists_radii_state_eq_after_insertNodeList_of_curvature
    [CompactSpace M] [ConnectedSpace M]
    {g : ClosedSmoothRiemannianMetric 3 M}
    (hcurv : HasConstantSectionalCurvature3 g 1)
    (coarse : ℕ → M) {initial : CartanChain.ChainState g}
    (p : ℕ) (zs : List M)
    (chain : ∀ i : ℕ,
      ReachableChain (insertNodeListSchedule coarse p zs i) initial)
    (L : ℕ) (hterminal : p + 1 ≤ L) :
    letI : MetricSpace M := g.toMetricSpace
    ∃ epsilon : Fin zs.length → ℝ,
      (∀ i : Fin zs.length, 0 < epsilon i) ∧
      ((∀ i : Fin zs.length,
        dist
            (insertNodeListSchedule coarse p zs (i + 1)
              (p + i + 1))
            ((chain (i + 1)).state (p + i)).anchor < epsilon i) →
        ∃ radius : Fin zs.length → ℝ,
          (∀ i : Fin zs.length, 0 < radius i) ∧
          ((∀ i : Fin zs.length,
            dist
                (insertNodeListSchedule coarse p zs i (p + i + 1))
                (insertNodeListSchedule coarse p zs (i + 1)
                  (p + i + 1)) < radius i) →
            (chain 0).state L =
              (chain zs.length).state (L + zs.length))) := by
  letI : MetricSpace M := g.toMetricSpace
  apply ReachableChain.exists_radii_state_eq_after_finite_insertions_of_curvature
    (hcurv := hcurv)
    (nodes := insertNodeListSchedule coarse p zs)
    (chain := chain) (p := fun i ↦ p + i)
    (N := zs.length) (L := L)
  · intro i hi j hj
    have hj' : j < p + i := by simpa using hj
    exact (insertNodeListSchedule_succ_eq_of_le
      coarse p zs i (j + 1) hi (by omega)).symm
  · intro i hi r
    exact (insertNodeListSchedule_succ_shifted
      coarse p zs i r hi).symm
  · intro i hi
    omega

/-- For a nonempty finite insertion schedule, the two finite radius families
may each be replaced by one positive common radius.  The second common radius
is still selected only after the inserted nodes satisfy the first bound, which
preserves the genuine adaptive quantifier order. -/
theorem ReachableChain.exists_common_radii_state_eq_after_finite_insertions_of_curvature
    [CompactSpace M] [ConnectedSpace M]
    {g : ClosedSmoothRiemannianMetric 3 M}
    (hcurv : HasConstantSectionalCurvature3 g 1)
    (nodes : ℕ → ℕ → M) {initial : CartanChain.ChainState g}
    (chain : ∀ i : ℕ, ReachableChain (nodes i) initial)
    (p : ℕ → ℕ) (N L : ℕ) (hN : 0 < N)
    (hprefix : ∀ i < N, ∀ j < p i,
      nodes i (j + 1) = nodes (i + 1) (j + 1))
    (hshift : ∀ i < N, ∀ r : ℕ,
      nodes i (p i + r + 1) = nodes (i + 1) (p i + r + 2))
    (hterminal : ∀ i < N, p i + 1 ≤ L + i) :
    letI : MetricSpace M := g.toMetricSpace
    ∃ epsilon > (0 : ℝ),
      ((∀ i : Fin N,
        dist (nodes (i + 1) (p i + 1))
          ((chain (i + 1)).state (p i)).anchor < epsilon) →
        ∃ radius > (0 : ℝ),
          ((∀ i : Fin N,
            dist (nodes i (p i + 1))
              (nodes (i + 1) (p i + 1)) < radius) →
            (chain 0).state L = (chain N).state (L + N))) := by
  classical
  letI : MetricSpace M := g.toMetricSpace
  letI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  rcases
      ReachableChain.exists_radii_state_eq_after_finite_insertions_of_curvature
        hcurv nodes chain p N L hprefix hshift hterminal with
    ⟨epsilonAt, hepsilonAt, hafterInsert⟩
  let epsilon : ℝ :=
    Finset.univ.inf' Finset.univ_nonempty epsilonAt
  have hepsilon : 0 < epsilon := by
    dsimp [epsilon]
    apply (Finset.lt_inf'_iff _).2
    intro i _hi
    exact hepsilonAt i
  refine ⟨epsilon, hepsilon, ?_⟩
  intro hinsert
  have hinsertAt : ∀ i : Fin N,
      dist (nodes (i + 1) (p i + 1))
        ((chain (i + 1)).state (p i)).anchor < epsilonAt i := by
    intro i
    exact (hinsert i).trans_le
      (Finset.inf'_le epsilonAt (Finset.mem_univ i))
  rcases hafterInsert hinsertAt with
    ⟨radiusAt, hradiusAt, hafterNext⟩
  let radius : ℝ :=
    Finset.univ.inf' Finset.univ_nonempty radiusAt
  have hradius : 0 < radius := by
    dsimp [radius]
    apply (Finset.lt_inf'_iff _).2
    intro i _hi
    exact hradiusAt i
  refine ⟨radius, hradius, ?_⟩
  intro hnext
  apply hafterNext
  intro i
  exact (hnext i).trans_le
    (Finset.inf'_le radiusAt (Finset.mem_univ i))

end DifferentialSuccessorFiniteInsertionRefinement
end Poincare
