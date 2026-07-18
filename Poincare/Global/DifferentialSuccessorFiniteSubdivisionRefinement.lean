import Poincare.Global.DifferentialSuccessorReachableChainRefinement

/-!
# Common refinements of finite, eventually stationary subdivisions

The adaptive differential-successor construction may produce two different
finite subdivisions of the unit interval.  This file supplies the missing
order-theoretic comparison: the union of their finitely many values, sorted in
increasing order, is an eventually stationary monotone subdivision through
which both original subdivisions factor by monotone index maps.

Repeated subdivision values are harmless.  The common sequence contains each
nonzero value once, begins separately at zero, and is extended constantly by
one.  Consequently the factor maps are merely monotone, as they must be when
an original subdivision has stationary or repeated nodes.
-/

noncomputable section

open Set
open scoped unitInterval

namespace Poincare
namespace DifferentialSuccessorFiniteSubdivisionRefinement

/-- Enumerate a finite set of nonzero subdivision values in increasing order,
with a separate initial zero and a stationary tail equal to one. -/
def finiteSortedSequence (S : Finset unitInterval) : ℕ → unitInterval
  | 0 => 0
  | n + 1 =>
      if h : n < S.card then
        (S.orderIsoOfFin rfl ⟨n, h⟩ : S)
      else 1

@[simp]
theorem finiteSortedSequence_zero (S : Finset unitInterval) :
    finiteSortedSequence S 0 = 0 :=
  rfl

/-- The sorted finite enumeration, followed by its constant top tail, is
monotone. -/
theorem finiteSortedSequence_monotone (S : Finset unitInterval) :
    Monotone (finiteSortedSequence S) := by
  apply monotone_nat_of_le_succ
  intro n
  cases n with
  | zero =>
      exact (finiteSortedSequence S 1).property.1
  | succ n =>
      by_cases hnext : n + 1 < S.card
      · have hn : n < S.card :=
          Nat.lt_trans (Nat.lt_succ_self n) hnext
        simp only [finiteSortedSequence, dif_pos hn, dif_pos hnext]
        exact (S.orderIsoOfFin rfl).monotone (Nat.le_succ n)
      · simp only [finiteSortedSequence, dif_neg hnext]
        by_cases hn : n < S.card
        · rw [dif_pos hn]
          exact
            ((S.orderIsoOfFin rfl ⟨n, hn⟩ : S) : unitInterval).property.2
        · rw [dif_neg hn]

/-- The finite sorted enumeration is identically one from the first index
after all finite values have been displayed. -/
theorem finiteSortedSequence_eventually_one (S : Finset unitInterval) :
    ∀ n ≥ S.card + 1, finiteSortedSequence S n = 1 := by
  intro n hn
  cases n with
  | zero => omega
  | succ m =>
      have hm : ¬m < S.card := by omega
      simp only [finiteSortedSequence, dif_neg hm]

/-- The positive index occupied by a member of the finite sorted sequence. -/
def finiteSortedSequenceIndex (S : Finset unitInterval)
    (x : unitInterval) (hx : x ∈ S) : ℕ :=
  ((S.orderIsoOfFin rfl).symm ⟨x, hx⟩).val + 1

theorem finiteSortedSequenceIndex_le_card (S : Finset unitInterval)
    (x : unitInterval) (hx : x ∈ S) :
    finiteSortedSequenceIndex S x hx ≤ S.card := by
  exact Nat.succ_le_of_lt
    ((S.orderIsoOfFin rfl).symm ⟨x, hx⟩).isLt

/-- Looking up the sorted index of a finite value recovers that value. -/
theorem finiteSortedSequence_index (S : Finset unitInterval)
    (x : unitInterval) (hx : x ∈ S) :
    finiteSortedSequence S (finiteSortedSequenceIndex S x hx) = x := by
  let e : Fin S.card ≃o S := S.orderIsoOfFin rfl
  let q : Fin S.card := e.symm ⟨x, hx⟩
  change
    (if h : q.val < S.card then
        ((S.orderIsoOfFin rfl ⟨q.val, h⟩ : S) : unitInterval)
      else 1) = x
  rw [dif_pos q.isLt]
  exact congrArg Subtype.val (e.apply_symm_apply ⟨x, hx⟩)

/-- Sorted indices preserve the order of the represented values. -/
theorem finiteSortedSequenceIndex_mono (S : Finset unitInterval)
    {x y : unitInterval} (hx : x ∈ S) (hy : y ∈ S)
    (hxy : x ≤ y) :
    finiteSortedSequenceIndex S x hx ≤
      finiteSortedSequenceIndex S y hy := by
  apply Nat.add_le_add_right _ 1
  exact (S.orderIsoOfFin rfl).symm.monotone hxy

/-- There is no member of `S` strictly between two consecutive values of its
sorted enumeration.  Equivalently, any member strictly above the current
value bounds the next value from above. -/
theorem finiteSortedSequence_succ_le_of_lt_member
    (S : Finset unitInterval) {n : ℕ} {z : unitInterval}
    (hz : z ∈ S) (h : finiteSortedSequence S n < z) :
    finiteSortedSequence S (n + 1) ≤ z := by
  let j := finiteSortedSequenceIndex S z hz
  have hjval : finiteSortedSequence S j = z :=
    finiteSortedSequence_index S z hz
  have hnlt : n < j := by
    by_contra hn
    have hle := finiteSortedSequence_monotone S (Nat.le_of_not_gt hn)
    rw [hjval] at hle
    exact (not_le_of_gt h) hle
  have hle := finiteSortedSequence_monotone S
    (Nat.succ_le_iff.mpr hnlt)
  rwa [hjval] at hle

/-- If the finite prefix of an eventually-one sequence is represented in
`S`, then every adjacent interval of the sorted enumeration lies inside one
adjacent interval of that sequence.

No strictness assumption is needed: repeated source values simply give
degenerate containing intervals. -/
theorem exists_subdivision_bracket_of_prefix_values
    (S : Finset unitInterval) (c : ℕ → unitInterval)
    (hc0 : c 0 = 0) (k : ℕ) (hcone : ∀ n ≥ k, c n = 1)
    (hmem : ∀ i ≤ k, c i = 0 ∨ c i ∈ S) (n : ℕ) :
    ∃ j : ℕ, c j ≤ finiteSortedSequence S n ∧
      finiteSortedSequence S (n + 1) ≤ c (j + 1) := by
  let A := (Finset.range (k + 1)).filter
    (fun j ↦ c j ≤ finiteSortedSequence S n)
  have hzero : 0 ∈ A := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr (Nat.zero_lt_succ k), ?_⟩
    rw [hc0]
    exact (finiteSortedSequence S n).property.1
  have hA : A.Nonempty := ⟨0, hzero⟩
  let j := A.max' hA
  have hjmem : j ∈ A := Finset.max'_mem A hA
  have hjrange : j < k + 1 :=
    Finset.mem_range.mp (Finset.mem_filter.mp hjmem).1
  have hjle : c j ≤ finiteSortedSequence S n :=
    (Finset.mem_filter.mp hjmem).2
  refine ⟨j, hjle, ?_⟩
  by_cases hjk : j = k
  · rw [hcone (j + 1) (by omega)]
    exact (finiteSortedSequence S (n + 1)).property.2
  · have hjlt : j < k := by omega
    have hnextNot : ¬c (j + 1) ≤ finiteSortedSequence S n := by
      intro hnext
      have hnextMem : j + 1 ∈ A := by
        apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_range.mpr (by omega), hnext⟩
      have hlemax := Finset.le_max' A (j + 1) hnextMem
      change j + 1 ≤ j at hlemax
      omega
    have hxlt : finiteSortedSequence S n < c (j + 1) :=
      lt_of_not_ge hnextNot
    have hnextMemOr := hmem (j + 1) (by omega)
    have hnextMemS : c (j + 1) ∈ S := by
      rcases hnextMemOr with hzero' | hS
      · rw [hzero'] at hxlt
        exact
          (not_lt_of_ge (finiteSortedSequence S n).property.1 hxlt).elim
      · exact hS
    exact finiteSortedSequence_succ_le_of_lt_member S hnextMemS hxlt

/-- Embed either zero or a member of `S` into the finite support of the sorted
sequence.  Zero occupies index zero; the members of `S` occupy positive
indices. -/
def finiteSortedSequenceEmbedding (S : Finset unitInterval)
    (x : unitInterval) (hx : x = 0 ∨ x ∈ S) : Fin (S.card + 1) :=
  if hzero : x = 0 then
    ⟨0, Nat.zero_lt_succ _⟩
  else
    ⟨finiteSortedSequenceIndex S x (hx.resolve_left hzero),
      Nat.lt_succ_of_le
        (finiteSortedSequenceIndex_le_card S x
          (hx.resolve_left hzero))⟩

@[simp]
theorem finiteSortedSequenceEmbedding_zero (S : Finset unitInterval)
    (hzero : (0 : unitInterval) = 0 ∨ (0 : unitInterval) ∈ S) :
    finiteSortedSequenceEmbedding S 0 hzero =
      ⟨0, Nat.zero_lt_succ S.card⟩ := by
  apply Fin.ext
  simp [finiteSortedSequenceEmbedding]

/-- The finite embedding really selects the represented value. -/
theorem finiteSortedSequence_embedding_value (S : Finset unitInterval)
    (x : unitInterval) (hx : x = 0 ∨ x ∈ S) :
    finiteSortedSequence S (finiteSortedSequenceEmbedding S x hx) = x := by
  by_cases hzero : x = 0
  · subst x
    simp [finiteSortedSequenceEmbedding, finiteSortedSequence]
  · simp only [finiteSortedSequenceEmbedding, dif_neg hzero]
    exact finiteSortedSequence_index S x (hx.resolve_left hzero)

/-- The finite embeddings of two ordered represented values are ordered. -/
theorem finiteSortedSequenceEmbedding_mono (S : Finset unitInterval)
    {x y : unitInterval} (hx : x = 0 ∨ x ∈ S)
    (hy : y = 0 ∨ y ∈ S) (hxy : x ≤ y) :
    finiteSortedSequenceEmbedding S x hx ≤
      finiteSortedSequenceEmbedding S y hy := by
  by_cases hxzero : x = 0
  · subst x
    simp [finiteSortedSequenceEmbedding]
  · by_cases hyzero : y = 0
    · have hzero_le : (0 : unitInterval) ≤ x := x.property.1
      have : x = 0 :=
        le_antisymm (by simpa [hyzero] using hxy) hzero_le
      exact (hxzero this).elim
    · simp only [finiteSortedSequenceEmbedding, dif_neg hxzero,
        dif_neg hyzero]
      exact finiteSortedSequenceIndex_mono S
        (hx.resolve_left hxzero) (hy.resolve_left hyzero) hxy

/-- Extend a finite monotone index embedding by the constant terminal index. -/
def extendFiniteEmbedding {k K : ℕ}
    (e : Fin (k + 1) → Fin K) : ℕ → ℕ :=
  fun n ↦ if h : n ≤ k then e ⟨n, Nat.lt_succ_iff.mpr h⟩ else K

/-- A monotone finite embedding remains monotone after constant terminal
extension. -/
theorem extendFiniteEmbedding_monotone {k K : ℕ}
    {e : Fin (k + 1) → Fin K} (he : Monotone e) :
    Monotone (extendFiniteEmbedding e) := by
  apply monotone_nat_of_le_succ
  intro n
  by_cases hnext : n + 1 ≤ k
  · have hn : n ≤ k := le_trans (Nat.le_succ n) hnext
    simp only [extendFiniteEmbedding, dif_pos hn, dif_pos hnext]
    exact he (Nat.le_succ n)
  · simp only [extendFiniteEmbedding, dif_neg hnext]
    by_cases hn : n ≤ k
    · rw [dif_pos hn]
      exact Nat.le_of_lt (e ⟨n, Nat.lt_succ_iff.mpr hn⟩).isLt
    · rw [dif_neg hn]

/-- The finite set of values occurring in the displayed prefix of an
eventually stationary subdivision. -/
def finiteSubdivisionValues (t : ℕ → unitInterval) (k : ℕ) :
    Finset unitInterval :=
  Finset.image t (Finset.range (k + 1))

theorem mem_finiteSubdivisionValues (t : ℕ → unitInterval) (k i : ℕ)
    (hi : i ≤ k) : t i ∈ finiteSubdivisionValues t k := by
  exact Finset.mem_image.mpr
    ⟨i, Finset.mem_range.mpr (by omega), rfl⟩

/-- Two eventually stationary monotone unit-interval subdivisions admit a
common eventually stationary monotone refinement.

The monotone maps `e₁` and `e₂` are genuine factor maps on every natural
index, not merely membership witnesses for the finite sets of values.  Thus
the theorem can be iterated with the single-insertion invariance theorem for
realized differential-successor chains. -/
theorem exists_common_monotone_refinement
    (t₁ t₂ : ℕ → unitInterval)
    (ht₁zero : t₁ 0 = 0) (ht₂zero : t₂ 0 = 0)
    (ht₁mono : Monotone t₁) (ht₂mono : Monotone t₂)
    (k₁ k₂ : ℕ) (ht₁one : ∀ n ≥ k₁, t₁ n = 1)
    (ht₂one : ∀ n ≥ k₂, t₂ n = 1) :
    ∃ (r : ℕ → unitInterval) (K : ℕ) (e₁ e₂ : ℕ → ℕ),
      0 < K ∧ r 0 = 0 ∧ Monotone r ∧ (∀ n ≥ K, r n = 1) ∧
        Monotone e₁ ∧ Monotone e₂ ∧ e₁ 0 = 0 ∧ e₂ 0 = 0 ∧
        (∀ n, e₁ n ≤ K) ∧ (∀ n, e₂ n ≤ K) ∧
        (∀ n, r (e₁ n) = t₁ n) ∧ (∀ n, r (e₂ n) = t₂ n) ∧
        (∀ n, ∃ j, t₁ j ≤ r n ∧ r (n + 1) ≤ t₁ (j + 1)) ∧
        (∀ n, ∃ j, t₂ j ≤ r n ∧ r (n + 1) ≤ t₂ (j + 1)) := by
  classical
  let V :=
    finiteSubdivisionValues t₁ k₁ ∪ finiteSubdivisionValues t₂ k₂
  let S := V.erase 0
  let r := finiteSortedSequence S
  let K := S.card + 1
  have hK : 0 < K := by simp [K]
  have hmem₁ (i : Fin (k₁ + 1)) : t₁ i = 0 ∨ t₁ i ∈ S := by
    by_cases hzero : t₁ i = 0
    · exact Or.inl hzero
    · right
      apply Finset.mem_erase.mpr
      refine ⟨hzero, Finset.mem_union_left _ ?_⟩
      exact mem_finiteSubdivisionValues t₁ k₁ i (by omega)
  have hmem₂ (i : Fin (k₂ + 1)) : t₂ i = 0 ∨ t₂ i ∈ S := by
    by_cases hzero : t₂ i = 0
    · exact Or.inl hzero
    · right
      apply Finset.mem_erase.mpr
      refine ⟨hzero, Finset.mem_union_right _ ?_⟩
      exact mem_finiteSubdivisionValues t₂ k₂ i (by omega)
  let f₁ : Fin (k₁ + 1) → Fin K := fun i ↦
    finiteSortedSequenceEmbedding S (t₁ i) (hmem₁ i)
  let f₂ : Fin (k₂ + 1) → Fin K := fun i ↦
    finiteSortedSequenceEmbedding S (t₂ i) (hmem₂ i)
  have hf₁mono : Monotone f₁ := by
    intro i j hij
    exact finiteSortedSequenceEmbedding_mono S (hmem₁ i) (hmem₁ j)
      (ht₁mono hij)
  have hf₂mono : Monotone f₂ := by
    intro i j hij
    exact finiteSortedSequenceEmbedding_mono S (hmem₂ i) (hmem₂ j)
      (ht₂mono hij)
  let e₁ := extendFiniteEmbedding f₁
  let e₂ := extendFiniteEmbedding f₂
  refine ⟨r, K, e₁, e₂, hK, rfl,
    finiteSortedSequence_monotone S,
    finiteSortedSequence_eventually_one S,
    extendFiniteEmbedding_monotone hf₁mono,
    extendFiniteEmbedding_monotone hf₂mono,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [e₁, extendFiniteEmbedding, f₁, ht₁zero,
      finiteSortedSequenceEmbedding]
  · simp [e₂, extendFiniteEmbedding, f₂, ht₂zero,
      finiteSortedSequenceEmbedding]
  · intro n
    by_cases hn : n ≤ k₁
    · simp only [e₁, extendFiniteEmbedding, dif_pos hn]
      exact Nat.le_of_lt (f₁ ⟨n, Nat.lt_succ_iff.mpr hn⟩).isLt
    · simp [e₁, extendFiniteEmbedding, hn]
  · intro n
    by_cases hn : n ≤ k₂
    · simp only [e₂, extendFiniteEmbedding, dif_pos hn]
      exact Nat.le_of_lt (f₂ ⟨n, Nat.lt_succ_iff.mpr hn⟩).isLt
    · simp [e₂, extendFiniteEmbedding, hn]
  · intro n
    by_cases hn : n ≤ k₁
    · simp only [e₁, extendFiniteEmbedding, dif_pos hn]
      exact finiteSortedSequence_embedding_value S (t₁ n)
        (hmem₁ ⟨n, Nat.lt_succ_iff.mpr hn⟩)
    · have hkn : k₁ ≤ n := by omega
      rw [ht₁one n hkn]
      simp only [e₁, extendFiniteEmbedding, dif_neg hn]
      exact finiteSortedSequence_eventually_one S K le_rfl
  · intro n
    by_cases hn : n ≤ k₂
    · simp only [e₂, extendFiniteEmbedding, dif_pos hn]
      exact finiteSortedSequence_embedding_value S (t₂ n)
        (hmem₂ ⟨n, Nat.lt_succ_iff.mpr hn⟩)
    · have hkn : k₂ ≤ n := by omega
      rw [ht₂one n hkn]
      simp only [e₂, extendFiniteEmbedding, dif_neg hn]
      exact finiteSortedSequence_eventually_one S K le_rfl
  · intro n
    simpa only [r] using
      (exists_subdivision_bracket_of_prefix_values S t₁ ht₁zero k₁
        ht₁one (fun i hi ↦ hmem₁ ⟨i, Nat.lt_succ_iff.mpr hi⟩) n)
  · intro n
    simpa only [r] using
      (exists_subdivision_bracket_of_prefix_values S t₂ ht₂zero k₂
        ht₂one (fun i hi ↦ hmem₂ ⟨i, Nat.lt_succ_iff.mpr hi⟩) n)

/-- A monotone factor map is strictly increasing wherever the represented
source subdivision is strictly increasing.  Thus repeated factor indices are
not an obstruction on a genuinely nondegenerate finite subdivision prefix. -/
theorem factorMap_strict_step_of_strict_source
    {r seed : ℕ → unitInterval} {e : ℕ → ℕ}
    (heMono : Monotone e) (heValue : ∀ n, r (e n) = seed n)
    {n : ℕ} (hseed : seed n < seed (n + 1)) :
    e n < e (n + 1) := by
  have hle : e n ≤ e (n + 1) := heMono (Nat.le_succ n)
  exact lt_of_le_of_ne hle (fun heq ↦ by
    have hvalue : seed n = seed (n + 1) := by
      rw [← heValue n, ← heValue (n + 1), heq]
    exact (ne_of_lt hseed) hvalue)

/-- The common refinement construction has a strictly increasing factor map
through every strictly increasing displayed source prefix. -/
theorem exists_common_monotone_refinement_strict_factor
    (t₁ t₂ : ℕ → unitInterval)
    (ht₁zero : t₁ 0 = 0) (ht₂zero : t₂ 0 = 0)
    (ht₁mono : Monotone t₁) (ht₂mono : Monotone t₂)
    (k₁ k₂ : ℕ) (ht₁one : ∀ n ≥ k₁, t₁ n = 1)
    (ht₂one : ∀ n ≥ k₂, t₂ n = 1)
    (ht₁strict : ∀ n < k₁, t₁ n < t₁ (n + 1)) :
    ∃ (r : ℕ → unitInterval) (K : ℕ) (e₁ e₂ : ℕ → ℕ),
      0 < K ∧ r 0 = 0 ∧ Monotone r ∧ (∀ n ≥ K, r n = 1) ∧
        Monotone e₁ ∧ Monotone e₂ ∧ e₁ 0 = 0 ∧ e₂ 0 = 0 ∧
        (∀ n, e₁ n ≤ K) ∧ (∀ n, e₂ n ≤ K) ∧
        (∀ n, r (e₁ n) = t₁ n) ∧ (∀ n, r (e₂ n) = t₂ n) ∧
        (∀ n < k₁, e₁ n < e₁ (n + 1)) ∧
        (∀ n, ∃ j, t₁ j ≤ r n ∧ r (n + 1) ≤ t₁ (j + 1)) ∧
        (∀ n, ∃ j, t₂ j ≤ r n ∧ r (n + 1) ≤ t₂ (j + 1)) := by
  rcases exists_common_monotone_refinement t₁ t₂ ht₁zero ht₂zero
      ht₁mono ht₂mono k₁ k₂ ht₁one ht₂one with
    ⟨r, K, e₁, e₂, hK, hrZero, hrMono, hrOne,
      he₁Mono, he₂Mono, he₁Zero, he₂Zero, he₁Bound, he₂Bound,
      he₁Value, he₂Value, ht₁Bracket, ht₂Bracket⟩
  refine ⟨r, K, e₁, e₂, hK, hrZero, hrMono, hrOne,
    he₁Mono, he₂Mono, he₁Zero, he₂Zero, he₁Bound, he₂Bound,
    he₁Value, he₂Value, ?_, ht₁Bracket, ht₂Bracket⟩
  intro n hn
  exact factorMap_strict_step_of_strict_source he₁Mono he₁Value
    (ht₁strict n hn)

/-- An open cover of the parameter square admits a subordinate finite grid
which simultaneously refines any prescribed eventually stationary monotone
subdivision.

This strengthens the standard compact-square subdivision theorem by retaining
the old nodes.  It is the geometric ingredient needed by adaptive Cartan
continuation: after new local equality patches are known, the replacement grid
can be made cover-small without discarding the previously realized grid. -/
theorem exists_common_refinement_subordinate_to_open_cover_prod
    (seed : ℕ → unitInterval) (hseedZero : seed 0 = 0)
    (hseedMono : Monotone seed) (seedK : ℕ)
    (hseedOne : ∀ n ≥ seedK, seed n = 1)
    {ι : Type*} {c : ι → Set (unitInterval × unitInterval)}
    (hcOpen : ∀ i, IsOpen (c i)) (hcCover : univ ⊆ ⋃ i, c i) :
    ∃ (r : ℕ → unitInterval) (K : ℕ) (e : ℕ → ℕ),
      0 < K ∧ r 0 = 0 ∧ Monotone r ∧ (∀ n ≥ K, r n = 1) ∧
        Monotone e ∧ e 0 = 0 ∧ (∀ n, e n ≤ K) ∧
        (∀ n, r (e n) = seed n) ∧
        ∀ n m, ∃ i,
          Icc (r n) (r (n + 1)) ×ˢ Icc (r m) (r (m + 1)) ⊆ c i := by
  rcases exists_monotone_Icc_subset_open_cover_unitInterval_prod_self
      hcOpen hcCover with
    ⟨fine, hfineZero, hfineMono, ⟨fineK, hfineOne⟩, hfineCell⟩
  rcases exists_common_monotone_refinement
      seed fine hseedZero hfineZero hseedMono hfineMono
      seedK fineK hseedOne hfineOne with
    ⟨r, K, e, efine, hK, hrZero, hrMono, hrOne,
      heMono, _hefineMono, heZero, _hefineZero,
      heBound, _hefineBound, heValue, _hefineValue,
      _hseedBracket, hfineBracket⟩
  refine ⟨r, K, e, hK, hrZero, hrMono, hrOne, heMono, heZero,
    heBound, heValue, ?_⟩
  intro n m
  rcases hfineBracket n with ⟨jn, hjnLower, hjnUpper⟩
  rcases hfineBracket m with ⟨jm, hjmLower, hjmUpper⟩
  rcases hfineCell jn jm with ⟨i, hi⟩
  refine ⟨i, ?_⟩
  rintro ⟨s, u⟩ ⟨hs, hu⟩
  apply hi
  exact
    ⟨⟨hjnLower.trans hs.1, hs.2.trans hjnUpper⟩,
      ⟨hjmLower.trans hu.1, hu.2.trans hjmUpper⟩⟩

/-- Strictly increasing seed prefixes are retained by strictly increasing
index maps in the cover-subordinate common refinement. -/
theorem exists_common_refinement_subordinate_to_open_cover_prod_strict_factor
    (seed : ℕ → unitInterval) (hseedZero : seed 0 = 0)
    (hseedMono : Monotone seed) (seedK : ℕ)
    (hseedOne : ∀ n ≥ seedK, seed n = 1)
    (hseedStrict : ∀ n < seedK, seed n < seed (n + 1))
    {ι : Type*} {c : ι → Set (unitInterval × unitInterval)}
    (hcOpen : ∀ i, IsOpen (c i)) (hcCover : univ ⊆ ⋃ i, c i) :
    ∃ (r : ℕ → unitInterval) (K : ℕ) (e : ℕ → ℕ),
      0 < K ∧ r 0 = 0 ∧ Monotone r ∧ (∀ n ≥ K, r n = 1) ∧
        Monotone e ∧ e 0 = 0 ∧ (∀ n, e n ≤ K) ∧
        (∀ n, r (e n) = seed n) ∧
        (∀ n < seedK, e n < e (n + 1)) ∧
        ∀ n m, ∃ i,
          Icc (r n) (r (n + 1)) ×ˢ Icc (r m) (r (m + 1)) ⊆ c i := by
  rcases exists_common_refinement_subordinate_to_open_cover_prod
      seed hseedZero hseedMono seedK hseedOne hcOpen hcCover with
    ⟨r, K, e, hK, hrZero, hrMono, hrOne, heMono, heZero,
      heBound, heValue, hcell⟩
  refine ⟨r, K, e, hK, hrZero, hrMono, hrOne, heMono, heZero,
    heBound, heValue, ?_, hcell⟩
  intro n hn
  exact factorMap_strict_step_of_strict_source heMono heValue
    (hseedStrict n hn)

end DifferentialSuccessorFiniteSubdivisionRefinement
end Poincare
