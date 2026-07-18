import Poincare.Global.DifferentialSuccessorFiniteRealizedHomotopyGrid

/-!
# Common radii for one fixed realized differential homotopy grid

Constant curvature supplies a predecessor radius and, after the actual
successor centers satisfy that bound, an equality radius separately for each
adjacent pair of rows in a fixed realized homotopy grid.  Because the row
support is finite, this file replaces those row-indexed radii by one positive
radius for the whole realized grid.

The quantifier order remains essential: the grid, its realized row chains,
and all cross-cell differential data are fixed first; the mesh bounds for the
common predecessor radius are assumed next; only then is the common equality
radius selected and its mesh bounds requested.  Nothing here chooses a grid
before its state-dependent radii are known.
-/

noncomputable section

open Set
open scoped Manifold ContDiff Topology unitInterval

namespace Poincare
namespace DifferentialSuccessorFiniteRealizedGridCommonRadius

universe u

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace E M]
variable [IsManifold I ∞ M]

open DifferentialSuccessorAdjacentContinuation
open DifferentialSuccessorFiniteRealizedHomotopyGrid

/--
One common positive predecessor radius and one common positive equality
radius suffice for all cells of a fixed finite realized homotopy grid.

The first two mesh hypotheses are exactly the horizontal and vertical edges
whose endpoints are the actual successor centers.  The initial-anchor and
`t 0 = 0` hypotheses identify the zeroth reached state in every row with the
left boundary of the homotopy, so no independent state-anchor bounds remain.
After those bounds, the second radius controls the opposite vertical and
horizontal edges used by the ladder comparison.
-/
theorem exists_common_patch_radii_for_fixed_realized_homotopyGrid_of_curvature
    [CompactSpace M] [ConnectedSpace M]
    {g : ClosedSmoothRiemannianMetric 3 M}
    (hcurv : HasConstantSectionalCurvature3 g 1)
    {x y : M} {p₀ p₁ : Path x y} (F : p₀.Homotopy p₁)
    (initial : CartanChain.ChainState g) (hinitial : initial.anchor = x)
    (t : ℕ → unitInterval) (htzero : t 0 = 0)
    (k : ℕ) (htone : ∀ n ≥ k, t n = 1)
    (rowChain : ∀ m : Fin (k + 2),
      DifferentialInducedSuccessor.Chain.ReachableChain
        (homotopyGridRow F t m) initial)
    (rungData : ∀ m : Fin (k + 1), ∀ j : Fin (k + 1),
      DifferentialInducedSuccessor.Data
        ((rowChain m.castSucc).state (j + 1))
        (homotopyGridRow F t (m + 1) (j + 1)))
    (bottomAtUpper : ∀ m : Fin (k + 1), ∀ j : Fin (k + 1),
      DifferentialInducedSuccessor.Data
        ((rowChain m.castSucc).state j)
        (homotopyGridRow F t (m + 1) (j + 1)))
    (rungAtNext : ∀ m : Fin (k + 1), ∀ j : Fin k,
      DifferentialInducedSuccessor.Data
        (rungData m j.castSucc).successor
        (homotopyGridRow F t (m + 1) (j + 2))) :
    letI : MetricSpace M := g.toMetricSpace
    ∃ epsilon > (0 : ℝ),
      (∀ m : Fin (k + 1), ∀ j : Fin (k + 1),
        dist (homotopyGridRow F t m (j + 1))
          (homotopyGridRow F t m j) < epsilon) →
      (∀ m : Fin (k + 1), ∀ j : Fin k,
        dist (homotopyGridRow F t (m + 1) (j + 1))
          (homotopyGridRow F t m (j + 1)) < epsilon) →
      ∃ radius > (0 : ℝ),
        (∀ m : Fin (k + 1), ∀ j : Fin (k + 1),
          dist (homotopyGridRow F t (m + 1) (j + 1))
            (homotopyGridRow F t m (j + 1)) < radius) →
        (∀ m : Fin (k + 1), ∀ j : Fin k,
          dist (homotopyGridRow F t (m + 1) (j + 2))
            (homotopyGridRow F t (m + 1) (j + 1)) < radius) →
        (rowChain 0).state (k + 1) =
          (rowChain (Fin.last (k + 1))).state (k + 1) := by
  classical
  letI : MetricSpace M := g.toMetricSpace
  rcases
      exists_perRow_patch_radii_for_realized_homotopyGrid_of_curvature
        hcurv F initial t k htone rowChain rungData bottomAtUpper rungAtNext with
    ⟨epsilon, hepsilon, hafterEpsilon⟩
  let epsilonCommon : ℝ :=
    Finset.univ.inf' Finset.univ_nonempty epsilon
  have hepsilonCommon : 0 < epsilonCommon := by
    dsimp [epsilonCommon]
    apply (Finset.lt_inf'_iff _).2
    intro m _hm
    exact hepsilon m
  have hepsilonCommon_le : ∀ m : Fin (k + 1),
      epsilonCommon ≤ epsilon m := by
    intro m
    dsimp [epsilonCommon]
    exact Finset.inf'_le epsilon (Finset.mem_univ m)
  refine ⟨epsilonCommon, hepsilonCommon, ?_⟩
  intro hhorizontal hvertical
  have hrowZero : ∀ m : Fin (k + 2),
      initial.anchor = homotopyGridRow F t m 0 := by
    intro m
    simpa [homotopyGridRow, htzero] using hinitial
  have hbottomSmall : ∀ m : Fin (k + 1), ∀ j : Fin (k + 1),
      dist (homotopyGridRow F t m (j + 1))
        ((rowChain m.castSucc).state j).anchor < epsilon m := by
    intro m j
    have hanchor :=
      (rowChain m.castSucc).state_anchor_eq_node
        (hrowZero m.castSucc) j
    rw [hanchor]
    exact (hhorizontal m j).trans_le (hepsilonCommon_le m)
  have hrungSmall : ∀ m : Fin (k + 1), ∀ j : Fin k,
      dist (homotopyGridRow F t (m + 1) (j + 1))
        ((rowChain m.castSucc).state (j + 1)).anchor < epsilon m := by
    intro m j
    have hanchor :=
      (rowChain m.castSucc).state_anchor_eq_node
        (hrowZero m.castSucc) (j + 1)
    rw [hanchor]
    exact (hvertical m j).trans_le (hepsilonCommon_le m)
  rcases hafterEpsilon hbottomSmall hrungSmall with
    ⟨radius, hradius, hafterRadius⟩
  let radiusCommon : ℝ :=
    Finset.univ.inf' Finset.univ_nonempty radius
  have hradiusCommon : 0 < radiusCommon := by
    dsimp [radiusCommon]
    apply (Finset.lt_inf'_iff _).2
    intro m _hm
    exact hradius m
  have hradiusCommon_le : ∀ m : Fin (k + 1),
      radiusCommon ≤ radius m := by
    intro m
    dsimp [radiusCommon]
    exact Finset.inf'_le radius (Finset.mem_univ m)
  refine ⟨radiusCommon, hradiusCommon, ?_⟩
  intro hbottomOpposite hrungOpposite
  apply hafterRadius
  · intro m j
    exact (hbottomOpposite m j).trans_le (hradiusCommon_le m)
  · intro m j
    exact (hrungOpposite m j).trans_le (hradiusCommon_le m)

/--
Single-radius endpoint independence for one fixed realized homotopy grid.

The radius is selected after the grid, its reached states, and all differential
data have been fixed.  If the fixed grid already misses the predecessor bound,
the implication is vacuous.  Otherwise the minimum of the predecessor and
equality radii controls every horizontal and vertical edge and the realized
ladder theorem identifies the boundary endpoint states.  Thus this result is
an endpoint-independence consumer, not a claim that the grid can be selected
before its state-dependent radius.
-/
theorem exists_common_mesh_radius_for_fixed_realized_homotopyGrid_of_curvature
    [CompactSpace M] [ConnectedSpace M]
    {g : ClosedSmoothRiemannianMetric 3 M}
    (hcurv : HasConstantSectionalCurvature3 g 1)
    {x y : M} {p₀ p₁ : Path x y} (F : p₀.Homotopy p₁)
    (initial : CartanChain.ChainState g) (hinitial : initial.anchor = x)
    (t : ℕ → unitInterval) (htzero : t 0 = 0)
    (k : ℕ) (htone : ∀ n ≥ k, t n = 1)
    (rowChain : ∀ m : Fin (k + 2),
      DifferentialInducedSuccessor.Chain.ReachableChain
        (homotopyGridRow F t m) initial)
    (rungData : ∀ m : Fin (k + 1), ∀ j : Fin (k + 1),
      DifferentialInducedSuccessor.Data
        ((rowChain m.castSucc).state (j + 1))
        (homotopyGridRow F t (m + 1) (j + 1)))
    (bottomAtUpper : ∀ m : Fin (k + 1), ∀ j : Fin (k + 1),
      DifferentialInducedSuccessor.Data
        ((rowChain m.castSucc).state j)
        (homotopyGridRow F t (m + 1) (j + 1)))
    (rungAtNext : ∀ m : Fin (k + 1), ∀ j : Fin k,
      DifferentialInducedSuccessor.Data
        (rungData m j.castSucc).successor
        (homotopyGridRow F t (m + 1) (j + 2))) :
    letI : MetricSpace M := g.toMetricSpace
    ∃ eta > (0 : ℝ),
      (∀ m : Fin (k + 2), ∀ j : Fin (k + 1),
        dist (homotopyGridRow F t m (j + 1))
          (homotopyGridRow F t m j) < eta) →
      (∀ m : Fin (k + 1), ∀ j : Fin (k + 1),
        dist (homotopyGridRow F t (m + 1) (j + 1))
          (homotopyGridRow F t m (j + 1)) < eta) →
      (rowChain 0).state (k + 1) =
        (rowChain (Fin.last (k + 1))).state (k + 1) := by
  classical
  letI : MetricSpace M := g.toMetricSpace
  rcases
      exists_common_patch_radii_for_fixed_realized_homotopyGrid_of_curvature
        hcurv F initial hinitial t htzero k htone rowChain rungData
          bottomAtUpper rungAtNext with
    ⟨epsilon, hepsilon, hafterEpsilon⟩
  let Horizontal : ℝ → Prop := fun r ↦
    ∀ m : Fin (k + 2), ∀ j : Fin (k + 1),
      dist (homotopyGridRow F t m (j + 1))
        (homotopyGridRow F t m j) < r
  let Vertical : ℝ → Prop := fun r ↦
    ∀ m : Fin (k + 1), ∀ j : Fin (k + 1),
      dist (homotopyGridRow F t (m + 1) (j + 1))
        (homotopyGridRow F t m (j + 1)) < r
  by_cases hmesh : Horizontal epsilon ∧ Vertical epsilon
  · have hhorizontalPredecessor :
        ∀ m : Fin (k + 1), ∀ j : Fin (k + 1),
          dist (homotopyGridRow F t m (j + 1))
            (homotopyGridRow F t m j) < epsilon := by
      intro m j
      exact hmesh.1 m.castSucc j
    have hverticalPredecessor :
        ∀ m : Fin (k + 1), ∀ j : Fin k,
          dist (homotopyGridRow F t (m + 1) (j + 1))
            (homotopyGridRow F t m (j + 1)) < epsilon := by
      intro m j
      exact hmesh.2 m j.castSucc
    rcases hafterEpsilon hhorizontalPredecessor hverticalPredecessor with
      ⟨radius, hradius, hafterRadius⟩
    let eta : ℝ := min epsilon radius
    have heta : 0 < eta := lt_min hepsilon hradius
    refine ⟨eta, heta, ?_⟩
    intro hhorizontal hvertical
    apply hafterRadius
    · intro m j
      exact (hvertical m j).trans_le (min_le_right epsilon radius)
    · intro m j
      exact (hhorizontal m.succ j.succ).trans_le
        (min_le_right epsilon radius)
  · refine ⟨epsilon, hepsilon, ?_⟩
    intro hhorizontal hvertical
    exfalso
    apply hmesh
    exact ⟨hhorizontal, hvertical⟩

end DifferentialSuccessorFiniteRealizedGridCommonRadius
end Poincare
