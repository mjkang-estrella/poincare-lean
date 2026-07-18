import Poincare.Global.CartanCanonicalFamilyProvenanceRootedAssembly

/-!
# Compared rooted realizations with whole-cell metric control

The ordinary prescribed-mesh rooted realization controls only consecutive
sampled endpoints.  Strict-factor insertion transport needs more: every new
refinement node between two retained samples must remain close both to its
predecessor and to the retained right endpoint.

This file strengthens the construction by choosing the original rooted
subdivision subordinate to constant metric balls.  Consequently the entire
path image of each parameter cell has a caller-prescribed diameter.  The
canonical successor datum and its generic provenance comparison are still
selected together along the actually reached chain.
-/

noncomputable section

open Filter Metric Set
open scoped Manifold ContDiff Topology unitInterval

namespace Poincare
namespace CartanCanonicalFamilyComparedWholeCellRealization

set_option linter.unusedSectionVars false

universe u

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace E M]
variable [IsManifold I ∞ M]
variable [CompactSpace M] [ConnectedSpace M]

open CartanAtlasRootedPathAdaptiveMeshRealization
open CartanAtlasRootedPathSkeleton
open CartanCanonicalFamilyProvenanceRootedAssembly
open CartanCanonicalFamilySuccessorProvenance
open CartanCanonicalRootedRealizationTransfer
open CartanTargetExponential
open DifferentialSuccessorFiniteSubdivisionRefinement

/-- If a finite sorted subdivision contains the top endpoint but omits zero,
its first occurrence of `1` is exactly the cardinality index. -/
theorem finiteSortedSequence_eventually_one_from_card_of_one_mem_zero_not_mem
    (S : Finset unitInterval) (hone : (1 : unitInterval) ∈ S) :
    ∀ n ≥ S.card, finiteSortedSequence S n = 1 := by
  let e : Fin S.card ≃o S := S.orderIsoOfFin rfl
  let q : Fin S.card := e.symm ⟨1, hone⟩
  have hindexLower : S.card ≤ q.val + 1 := by
    by_contra hnot
    have hjlt : q.val + 1 < S.card := Nat.lt_of_not_ge hnot
    let j : Fin S.card := ⟨q.val + 1, hjlt⟩
    have hjle : j ≤ q := by
      apply (e.le_iff_le).mp
      have heq : e q = ⟨1, hone⟩ := by
        exact e.apply_symm_apply ⟨1, hone⟩
      rw [heq]
      exact ((e j : S) : unitInterval).property.2
    change q.val + 1 ≤ q.val at hjle
    omega
  have hindex : finiteSortedSequenceIndex S 1 hone = S.card := by
    apply le_antisymm
    · exact finiteSortedSequenceIndex_le_card S 1 hone
    · simpa [finiteSortedSequenceIndex, q, e] using hindexLower
  have hcardValue : finiteSortedSequence S S.card = 1 := by
    rw [← hindex]
    exact finiteSortedSequence_index S 1 hone
  intro n hn
  apply Subtype.ext
  apply le_antisymm (finiteSortedSequence S n).property.2
  have hmono := finiteSortedSequence_monotone S hn
  simpa only [hcardValue] using hmono

/-- Removing zero and retaining one makes the finite sorted sequence strictly
increasing exactly until its terminal cardinality index. -/
theorem finiteSortedSequence_strict_until_card_of_one_mem_zero_not_mem
    (S : Finset unitInterval) (hzero : (0 : unitInterval) ∉ S)
    (hone : (1 : unitInterval) ∈ S) :
    ∀ n < S.card,
      finiteSortedSequence S n < finiteSortedSequence S (n + 1) := by
  intro n hn
  cases n with
  | zero =>
      have hcard : 0 < S.card := Finset.card_pos.mpr ⟨1, hone⟩
      let first : S := S.orderIsoOfFin rfl ⟨0, hcard⟩
      have hfirstNe : (first : unitInterval) ≠ 0 := by
        intro h
        apply hzero
        simpa [h] using first.property
      have hfirstPos : (0 : unitInterval) < first :=
        lt_of_le_of_ne ((first : unitInterval).property.1) hfirstNe.symm
      simpa [finiteSortedSequence, first, hcard] using hfirstPos
  | succ n =>
      have hcurrent : n < S.card := (Nat.lt_succ_self n).trans hn
      have hnext : n + 1 < S.card := by simpa using hn
      simp only [finiteSortedSequence, dif_pos hcurrent, dif_pos hnext]
      exact (S.orderIsoOfFin rfl).strictMono (by simp)

/-- A uniform compared-successor radius realizes every rooted path while
controlling the diameter of the whole image of each selected parameter cell.

The diameter statement is quantified over every natural-number cell.  Beyond
the finite terminal index the subdivision is stationary, so those cells have
diameter zero. -/
theorem exists_comparedRootedRealization_with_prescribed_wholeCellMesh_of_uniformRadius
    {g : ClosedSmoothRiemannianMetric 3 M}
    (skeleton : RootedCartanPathSkeleton g)
    {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (hdata :
      letI : MetricSpace M := g.toMetricSpace
      ∀ (x : M) (p : RoundSphere3)
        (L : CartanMap.TangentAlignment g x p) (z : M),
        dist z x < epsilon →
          Nonempty
            (CanonicalComparedStep
              (ChainState.mk x p L) z))
    (mesh : ℝ) (hmesh : 0 < mesh) :
    letI : MetricSpace M := g.toMetricSpace
    ∃ realization :
        SuppliedRootedPathChainRealization canonicalFamily skeleton,
      ∃ _comparison : RootedRealizationComparison realization,
      (∀ x : M, 0 < realization.terminalIndex x) ∧
      (∀ x : M, Monotone (realization.nodeTime x)) ∧
      (∀ x : M, ∀ n < realization.terminalIndex x,
        realization.nodeTime x n < realization.nodeTime x (n + 1)) ∧
      (∀ x : M, ∀ n ≥ realization.terminalIndex x,
        realization.nodeTime x n = 1) ∧
      ∀ (x : M) (n : ℕ) (a b : unitInterval),
        a ∈ Icc (realization.nodeTime x n)
          (realization.nodeTime x (n + 1)) →
        b ∈ Icc (realization.nodeTime x n)
          (realization.nodeTime x (n + 1)) →
        dist (skeleton.path x a) (skeleton.path x b) < mesh := by
  classical
  letI : MetricSpace M := g.toMetricSpace
  let radius : ℝ := min epsilon mesh / 2
  have hradius : 0 < radius := half_pos (lt_min hepsilon hmesh)
  have hpath : ∀ x : M,
      ∃ (t : ℕ → unitInterval) (k : ℕ),
        0 < k ∧ t 0 = 0 ∧ Monotone t ∧
        (∀ n < k, t n < t (n + 1)) ∧
        (∀ n ≥ k, t n = 1) ∧
        (∀ (n : ℕ) (a b : unitInterval),
          a ∈ Icc (t n) (t (n + 1)) →
          b ∈ Icc (t n) (t (n + 1)) →
          dist (skeleton.path x a) (skeleton.path x b) < mesh) ∧
        Nonempty
          (ComparedReachableChain
            (fun n ↦ skeleton.path x (t n))
            (ChainState.retarget canonicalFamily skeleton.root)) := by
    intro x
    rcases exists_monotone_subdivision_subordinate_to_pointwise_path_balls
        (skeleton.path x).toContinuousMap (fun _ ↦ radius)
        (fun _ ↦ hradius) with
      ⟨t, k, center, _eta, htzero, htmono, htone, _heta,
        _hetaLower, hcell⟩
    have hk : 0 < k := by
      by_contra hk
      have hk0 : k = 0 := Nat.eq_zero_of_not_pos hk
      subst k
      have hone : t 0 = 1 := htone 0 le_rfl
      exact zero_ne_one (htzero.symm.trans hone)
    have hpairMin : ∀ (n : ℕ) (a b : unitInterval),
        a ∈ Icc (t n) (t (n + 1)) →
        b ∈ Icc (t n) (t (n + 1)) →
        dist (skeleton.path x a) (skeleton.path x b) <
          min epsilon mesh := by
      intro n a b ha hb
      by_cases hn : n ≤ k
      · let i : Fin (k + 1) := ⟨n, Nat.lt_succ_iff.2 hn⟩
        have haCenter := hcell i a (by simpa [i] using ha)
        have hbCenter := hcell i b (by simpa [i] using hb)
        calc
          dist (skeleton.path x a) (skeleton.path x b) ≤
              dist (skeleton.path x a) (skeleton.path x (center i)) +
                dist (skeleton.path x b)
                  (skeleton.path x (center i)) :=
            dist_triangle_right _ _ _
          _ < radius + radius := add_lt_add haCenter hbCenter
          _ = min epsilon mesh := by
            simp only [radius]
            ring
      · have hkn : k ≤ n := le_of_not_ge hn
        have htn : t n = 1 := htone n hkn
        have htnext : t (n + 1) = 1 :=
          htone (n + 1) (hkn.trans (Nat.le_succ n))
        have ha' : a ∈ Icc (1 : unitInterval) 1 := by
          simpa [htn, htnext] using ha
        have hb' : b ∈ Icc (1 : unitInterval) 1 := by
          simpa [htn, htnext] using hb
        have hab : a = b := by
          apply le_antisymm
          · exact ha'.2.trans hb'.1
          · exact hb'.2.trans ha'.1
        simpa [hab] using (lt_min hepsilon hmesh)
    let V : Finset unitInterval := finiteSubdivisionValues t k
    let S : Finset unitInterval := V.erase 0
    let r : ℕ → unitInterval := finiteSortedSequence S
    let K : ℕ := S.card
    have honeV : (1 : unitInterval) ∈ V := by
      have hmem := mem_finiteSubdivisionValues t k k le_rfl
      simpa [V, htone k le_rfl] using hmem
    have honeS : (1 : unitInterval) ∈ S := by
      exact Finset.mem_erase.mpr ⟨one_ne_zero, honeV⟩
    have hzeroS : (0 : unitInterval) ∉ S := by
      simp [S]
    have hK : 0 < K := by
      simpa [K] using Finset.card_pos.mpr ⟨1, honeS⟩
    have hrzero : r 0 = 0 := by
      exact finiteSortedSequence_zero S
    have hrmono : Monotone r := finiteSortedSequence_monotone S
    have hrstrict : ∀ n < K, r n < r (n + 1) := by
      exact
        finiteSortedSequence_strict_until_card_of_one_mem_zero_not_mem
          S hzeroS honeS
    have hrone : ∀ n ≥ K, r n = 1 := by
      exact
        finiteSortedSequence_eventually_one_from_card_of_one_mem_zero_not_mem
          S honeS
    have hmem : ∀ i ≤ k, t i = 0 ∨ t i ∈ S := by
      intro i hi
      by_cases hzero : t i = 0
      · exact Or.inl hzero
      · exact Or.inr (Finset.mem_erase.mpr
          ⟨hzero, by
            exact mem_finiteSubdivisionValues t k i hi⟩)
    have hbracket : ∀ n : ℕ, ∃ j : ℕ,
        t j ≤ r n ∧ r (n + 1) ≤ t (j + 1) := by
      intro n
      simpa only [r] using
        (exists_subdivision_bracket_of_prefix_values S t htzero k htone
          hmem n)
    have hrPairMin : ∀ (n : ℕ) (a b : unitInterval),
        a ∈ Icc (r n) (r (n + 1)) →
        b ∈ Icc (r n) (r (n + 1)) →
        dist (skeleton.path x a) (skeleton.path x b) <
          min epsilon mesh := by
      intro n a b ha hb
      rcases hbracket n with ⟨j, hjleft, hjright⟩
      exact hpairMin j a b
        ⟨hjleft.trans ha.1, ha.2.trans hjright⟩
        ⟨hjleft.trans hb.1, hb.2.trans hjright⟩
    have hwhole : ∀ (n : ℕ) (a b : unitInterval),
        a ∈ Icc (r n) (r (n + 1)) →
        b ∈ Icc (r n) (r (n + 1)) →
        dist (skeleton.path x a) (skeleton.path x b) < mesh := by
      intro n a b ha hb
      exact (hrPairMin n a b ha hb).trans_le (min_le_right _ _)
    have hstep : ∀ (n : ℕ) (s : ChainState canonicalFamily g),
        s.anchor = skeleton.path x (r n) →
          Nonempty
            (CanonicalComparedStep s (skeleton.path x (r (n + 1)))) := by
      intro n s hs
      have hmono : r n ≤ r (n + 1) := hrmono (Nat.le_succ n)
      have hleft : r n ∈ Icc (r n) (r (n + 1)) :=
        ⟨le_rfl, hmono⟩
      have hright : r (n + 1) ∈ Icc (r n) (r (n + 1)) :=
        ⟨hmono, le_rfl⟩
      have hdist :
          dist (skeleton.path x (r (n + 1))) s.anchor < epsilon := by
        rw [hs]
        simpa only [dist_comm] using
          (hrPairMin n (r n) (r (n + 1)) hleft hright).trans_le
            (min_le_left _ _)
      have package := hdata s.anchor s.target s.alignment
        (skeleton.path x (r (n + 1))) hdist
      have heta : ChainState.mk s.anchor s.target s.alignment = s := by
        cases s
        rfl
      exact heta ▸ package
    have hinitial :
        (ChainState.retarget canonicalFamily skeleton.root).anchor =
          skeleton.path x (r 0) := by
      rw [hrzero]
      simp
    exact ⟨r, K, hK, hrzero, hrmono, hrstrict, hrone, hwhole,
      ⟨comparedReachableChain_of_anchored_step_supply
        (fun n ↦ skeleton.path x (r n))
        (ChainState.retarget canonicalFamily skeleton.root)
        hinitial hstep⟩⟩
  choose t k hk htzero htmono htstrict htone hwhole hchain using hpath
  let realization : SuppliedRootedPathChainRealization
      canonicalFamily skeleton :=
    { nodeTime := t
      nodeTime_zero := htzero
      terminalIndex := k
      nodeTime_terminal := fun x ↦ htone x (k x) le_rfl
      chain := fun x ↦ (Classical.choice (hchain x)).chain }
  let comparison : RootedRealizationComparison realization :=
    { chain := fun x ↦ (Classical.choice (hchain x)).comparison }
  exact ⟨realization, comparison, hk, htmono, htstrict, htone, hwhole⟩

/-- An open compared-successor neighborhood gives the whole-cell controlled
rooted realization at every prescribed positive mesh. -/
theorem exists_comparedRootedRealization_with_prescribed_wholeCellMesh_of_neighborhood
    {g : ClosedSmoothRiemannianMetric 3 M}
    (skeleton : RootedCartanPathSkeleton g)
    (hneighborhood : UniversalComparedSuccessorLocus g ∈
      nhdsSet
        (CartanTargetExponential.successorParameterDiagonal (M := M)))
    (mesh : ℝ) (hmesh : 0 < mesh) :
    letI : MetricSpace M := g.toMetricSpace
    ∃ realization :
        SuppliedRootedPathChainRealization canonicalFamily skeleton,
      ∃ _comparison : RootedRealizationComparison realization,
      (∀ x : M, 0 < realization.terminalIndex x) ∧
      (∀ x : M, Monotone (realization.nodeTime x)) ∧
      (∀ x : M, ∀ n < realization.terminalIndex x,
        realization.nodeTime x n < realization.nodeTime x (n + 1)) ∧
      (∀ x : M, ∀ n ≥ realization.terminalIndex x,
        realization.nodeTime x n = 1) ∧
      ∀ (x : M) (n : ℕ) (a b : unitInterval),
        a ∈ Icc (realization.nodeTime x n)
          (realization.nodeTime x (n + 1)) →
        b ∈ Icc (realization.nodeTime x n)
          (realization.nodeTime x (n + 1)) →
        dist (skeleton.path x a) (skeleton.path x b) < mesh := by
  letI : MetricSpace M := g.toMetricSpace
  rcases exists_uniform_comparedSuccessor_radius hneighborhood with
    ⟨epsilon, hepsilon, hdata⟩
  exact
    exists_comparedRootedRealization_with_prescribed_wholeCellMesh_of_uniformRadius
      skeleton hepsilon hdata mesh hmesh

end CartanCanonicalFamilyComparedWholeCellRealization
end Poincare
