import Poincare.Global.CartanSuppliedPatchPolicy
import Poincare.Global.CartanAtlasRootedPathSkeleton
import Poincare.Global.CartanCanonicalRootedDirectGenericNeighborhoodRecognition

/-!
# Supplied chains on strict whole-cell subdivisions

Parameter cells are chosen geometrically before selecting any supplied data.
Realizations retain their actual preferred labels and reached differential chain.
-/

set_option autoImplicit false
noncomputable section
open Filter Metric Set
open scoped Manifold ContDiff Topology NNReal unitInterval
namespace Poincare
universe u
local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3
variable {M : Type u} [TopologicalSpace M] [inst : ChartedSpace E M]
  [IsManifold I ∞ M] [T2Space M] [CompactSpace M] [ConnectedSpace M]
variable {g : ClosedSmoothRiemannianMetric 3 M}
open CartanSuppliedDifferentialSuccessor CartanSuppliedReachableChain

namespace CartanSuppliedWholeCellRealization
open CartanSuppliedUniformPatchSwitch CartanSuppliedPatchPolicy
open CartanAtlasRootedPathAdaptiveMeshRealization
open CartanCanonicalFamilyComparedWholeCellRealization
open DifferentialSuccessorFiniteSubdivisionRefinement
structure Subdivision {x y : M} (p : Path x y) (r : ℝ) where
  time : ℕ → unitInterval
  terminal : ℕ
  zero : time 0 = 0
  mono : Monotone time
  strict : ∀ n < terminal, time n < time (n + 1)
  tail : ∀ n ≥ terminal, time n = 1
  wholeCell : letI : MetricSpace M := g.toMetricSpace
    ∀ n (a b : unitInterval), a ∈ Icc (time n) (time (n + 1)) →
      b ∈ Icc (time n) (time (n + 1)) → dist (p a) (p b) < r

structure Realization (S : System g) (initial : CartanChain.ChainState g)
    {y : M} (p : Path initial.anchor y) where
  subdivision : Subdivision (g := g) p S.mesh
  preferred : ℕ → S.cover.Label
  chain : ReachableChain (policy S.cover preferred)
    (fun n => p (subdivision.time n)) initial

def Realization.endpoint {S : System g} {initial : CartanChain.ChainState g}
    {y : M} {p : Path initial.anchor y} (R : Realization S initial p) :
    CartanChain.ChainState g := R.chain.state R.subdivision.terminal

structure RootedRealization (S : System g)
    (skeleton : CartanAtlasRootedPathSkeleton.RootedCartanPathSkeleton g) where
  realization : ∀ x : M, Realization S skeleton.root (skeleton.path x)

theorem endpoint_anchor : ∀ (S : System g) (initial : CartanChain.ChainState g)
    {y : M} (p : Path initial.anchor y) (R : Realization S initial p),
    R.endpoint.anchor = y := by
  intro S initial y p R
  have hinitial : initial.anchor = p (R.subdivision.time 0) := by
    simp [R.subdivision.zero]
  have h := state_anchor_eq_node _ _ initial R.chain hinitial R.subdivision.terminal
  simpa only [Realization.endpoint, R.subdivision.tail _ le_rfl, Path.target] using h

/-- Compact path geometry gives strict cells of any prescribed positive diameter. -/
theorem exists_subdivision : ∀ {x y : M} (p : Path x y) (r : ℝ),
    0 < r → Nonempty (Subdivision (g := g) p r) := by
  intro x y p r hr
  classical
  letI : MetricSpace M := g.toMetricSpace
  have hhalf : 0 < r / 2 := half_pos hr
  rcases exists_monotone_subdivision_subordinate_to_pointwise_path_balls
      p.toContinuousMap
      (fun _ ↦ r / 2) (fun _ ↦ hhalf) with
    ⟨t, k, center, _eta, htzero, htmono, htone, _heta,
      _hetaLower, hcell⟩
  let V : Finset unitInterval := finiteSubdivisionValues t k
  let S : Finset unitInterval := V.erase 0
  let times : ℕ → unitInterval := finiteSortedSequence S
  let K : ℕ := S.card
  have honeV : (1 : unitInterval) ∈ V := by
    have hmem := mem_finiteSubdivisionValues t k k le_rfl
    simpa [V, htone k le_rfl] using hmem
  have honeS : (1 : unitInterval) ∈ S :=
    Finset.mem_erase.mpr ⟨one_ne_zero, honeV⟩
  have hzeroS : (0 : unitInterval) ∉ S := by simp [S]
  have hrzero : times 0 = 0 := by
    exact finiteSortedSequence_zero S
  have hrmono : Monotone times := by
    simpa [times] using finiteSortedSequence_monotone S
  have hrstrict : ∀ n < K, times n < times (n + 1) := by
    simpa [times, K] using
      finiteSortedSequence_strict_until_card_of_one_mem_zero_not_mem
        S hzeroS honeS
  have hrone : ∀ n ≥ K, times n = 1 := by
    simpa [times, K] using
      finiteSortedSequence_eventually_one_from_card_of_one_mem_zero_not_mem
        S honeS
  have hmem : ∀ i ≤ k, t i = 0 ∨ t i ∈ S := by
    intro i hi
    by_cases hzero : t i = 0
    · exact Or.inl hzero
    · exact Or.inr <| Finset.mem_erase.mpr
        ⟨hzero, mem_finiteSubdivisionValues t k i hi⟩
  have hbracket : ∀ n : ℕ, ∃ j : ℕ,
      t j ≤ times n ∧ times (n + 1) ≤ t (j + 1) := by
    intro n
    simpa only [times] using
      (exists_subdivision_bracket_of_prefix_values S t htzero k htone
        hmem n)
  have hwhole : ∀ (n : ℕ) (a b : unitInterval),
      a ∈ Icc (times n) (times (n + 1)) →
      b ∈ Icc (times n) (times (n + 1)) →
      dist (p a) (p b) <
        r := by
    intro n a b ha hb
    rcases hbracket n with ⟨j, hjleft, hjright⟩
    by_cases hj : j ≤ k
    · let i : Fin (k + 1) := ⟨j, Nat.lt_succ_iff.mpr hj⟩
      have haCenter := hcell i a
        ⟨hjleft.trans ha.1, ha.2.trans hjright⟩
      have hbCenter := hcell i b
        ⟨hjleft.trans hb.1, hb.2.trans hjright⟩
      calc
        dist (p a) (p b) ≤
            dist (p a) (p (center i)) +
              dist (p b) (p (center i)) :=
          dist_triangle_right _ _ _
        _ < r / 2 +
              r / 2 :=
          add_lt_add haCenter hbCenter
        _ = r := by ring
    · have hkj : k ≤ j := le_of_not_ge hj
      have htj : t j = 1 := htone j hkj
      have htjnext : t (j + 1) = 1 :=
        htone (j + 1) (hkj.trans (Nat.le_succ j))
      have ha' : a ∈ Icc (1 : unitInterval) 1 := by
        exact ⟨(by simpa [htj] using (hjleft.trans ha.1)),
          (by simpa [htjnext] using (ha.2.trans hjright))⟩
      have hb' : b ∈ Icc (1 : unitInterval) 1 := by
        exact ⟨(by simpa [htj] using (hjleft.trans hb.1)),
          (by simpa [htjnext] using (hb.2.trans hjright))⟩
      have hab : a = b := by
        apply le_antisymm
        · exact ha'.2.trans hb'.1
        · exact hb'.2.trans ha'.1
      simpa [hab] using hr
  exact ⟨⟨times, K, hrzero, hrmono, hrstrict, hrone, hwhole⟩⟩

/-- Once the whole-cell subdivision is fixed, H1 supplies a sticky reached chain. -/
theorem exists_realization : ∀ (S : System g) (initial : CartanChain.ChainState g)
    {y : M} (p : Path initial.anchor y),
    ∃ R : Realization S initial p,
      Sticky S.cover R.preferred (fun n => p (R.subdivision.time n)) initial R.chain := by
  intro S initial y p
  obtain ⟨subdivision⟩ := exists_subdivision (g := g) p S.mesh (mesh_pos S)
  letI : MetricSpace M := g.toMetricSpace
  have hinitial : initial.anchor = p (subdivision.time 0) := by
    simp [subdivision.zero]
  have hsmall : ∀ n, dist (p (subdivision.time (n + 1)))
      (p (subdivision.time n)) < S.mesh := by
    intro n
    have hmono := subdivision.mono (Nat.le_succ n)
    exact subdivision.wholeCell n _ _ ⟨hmono, le_rfl⟩ ⟨le_rfl, hmono⟩
  obtain ⟨preferred, chain, _hzero, hsticky⟩ :=
    exists_sticky_chain S (fun n => p (subdivision.time n)) initial hinitial hsmall
  exact ⟨⟨subdivision, preferred, chain⟩, hsticky⟩

/-- Every path in the common rooted skeleton has an actual supplied realization. -/
theorem exists_rootedRealization_with_wholeCellMesh : ∀ (S : System g)
    (skeleton : CartanAtlasRootedPathSkeleton.RootedCartanPathSkeleton g),
    Nonempty (RootedRealization S skeleton) := by
  intro S skeleton
  exact ⟨⟨fun x => Classical.choose (exists_realization S skeleton.root (skeleton.path x))⟩⟩

end CartanSuppliedWholeCellRealization
end Poincare
