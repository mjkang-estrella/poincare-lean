import Poincare.Global.DifferentialSuccessorAdaptiveGridRefinement

/-!
# Vanishing finite maxima on refining homotopy grids

Every continuous homotopy rectangle admits arbitrarily fine subdivisions
which retain all nodes of a prescribed finite subdivision.  The existing
refinement theorem expresses fineness by pointwise horizontal and vertical
edge estimates over all natural indices.

This file packages its output as honest finite subdivisions and takes the
maximum over each of the two actual finite edge families.  Applying the
refinement theorem at the reciprocal scales `1 / (n + 1)` then gives a
countable family of seed-refining grids whose two finite maxima vanish.

There is no Cartan successor, equality, curvature, common-radius, or
lower-semicontinuity assumption in this geometric result.
-/

noncomputable section

open Set
open scoped Manifold ContDiff Topology unitInterval

namespace Poincare
namespace DifferentialHomotopyGridFiniteMaximaRefinement

universe u

open DifferentialSuccessorAdjacentContinuation
open DifferentialSuccessorAdaptiveGridRefinement

/-- An eventually stationary monotone subdivision of the unit interval,
with a specified positive terminal index. -/
structure FiniteHomotopySubdivision where
  nodes : ℕ → unitInterval
  terminalIndex : ℕ
  terminalIndex_pos : 0 < terminalIndex
  nodes_zero : nodes 0 = 0
  nodes_monotone : Monotone nodes
  nodes_one : ∀ n ≥ terminalIndex, nodes n = 1

namespace FiniteHomotopySubdivision

/-- `fine` retains every node of `coarse` through a monotone bounded factor
map.  Repeated coarse nodes are allowed. -/
def Refines (fine coarse : FiniteHomotopySubdivision) : Prop :=
  ∃ factor : ℕ → ℕ,
    Monotone factor ∧
      factor 0 = 0 ∧
      (∀ n, factor n ≤ fine.terminalIndex) ∧
      ∀ n, fine.nodes (factor n) = coarse.nodes n

section FiniteEdges

variable {M : Type u} [PseudoMetricSpace M]
variable {x y : M} {p₀ p₁ : Path x y}

/-- One horizontal edge length in the finite displayed part of a homotopy
subdivision. -/
def horizontalEdgeDistance
    (F : p₀.Homotopy p₁) (subdivision : FiniteHomotopySubdivision)
    (a : Fin (subdivision.terminalIndex + 2) ×
      Fin (subdivision.terminalIndex + 1)) : ℝ :=
  dist
    (homotopyGridRow F subdivision.nodes (a.1 : ℕ) ((a.2 : ℕ) + 1))
    (homotopyGridRow F subdivision.nodes (a.1 : ℕ) (a.2 : ℕ))

/-- One vertical edge length in the finite displayed part of a homotopy
subdivision. -/
def verticalEdgeDistance
    (F : p₀.Homotopy p₁) (subdivision : FiniteHomotopySubdivision)
    (a : Fin (subdivision.terminalIndex + 1) ×
      Fin (subdivision.terminalIndex + 1)) : ℝ :=
  dist
    (homotopyGridRow F subdivision.nodes ((a.1 : ℕ) + 1)
      ((a.2 : ℕ) + 1))
    (homotopyGridRow F subdivision.nodes (a.1 : ℕ) ((a.2 : ℕ) + 1))

/-- The maximum of all horizontal edge lengths in the finite displayed
homotopy grid. -/
def horizontalMaximum
    (F : p₀.Homotopy p₁) (subdivision : FiniteHomotopySubdivision) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty
    (horizontalEdgeDistance F subdivision)

/-- The maximum of all vertical edge lengths in the finite displayed
homotopy grid. -/
def verticalMaximum
    (F : p₀.Homotopy p₁) (subdivision : FiniteHomotopySubdivision) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty
    (verticalEdgeDistance F subdivision)

/-- A strict bound for the horizontal finite maximum is exactly a strict
bound for every member of its finite edge family. -/
theorem horizontalMaximum_lt_iff
    (F : p₀.Homotopy p₁) (subdivision : FiniteHomotopySubdivision)
    (eta : ℝ) :
    horizontalMaximum F subdivision < eta ↔
      ∀ a : Fin (subdivision.terminalIndex + 2) ×
        Fin (subdivision.terminalIndex + 1),
          horizontalEdgeDistance F subdivision a < eta := by
  rw [horizontalMaximum, Finset.sup'_lt_iff]
  constructor
  · intro h a
    exact h a (Finset.mem_univ a)
  · intro h a _ha
    exact h a

/-- A strict bound for the vertical finite maximum is exactly a strict bound
for every member of its finite edge family. -/
theorem verticalMaximum_lt_iff
    (F : p₀.Homotopy p₁) (subdivision : FiniteHomotopySubdivision)
    (eta : ℝ) :
    verticalMaximum F subdivision < eta ↔
      ∀ a : Fin (subdivision.terminalIndex + 1) ×
        Fin (subdivision.terminalIndex + 1),
          verticalEdgeDistance F subdivision a < eta := by
  rw [verticalMaximum, Finset.sup'_lt_iff]
  constructor
  · intro h a
    exact h a (Finset.mem_univ a)
  · intro h a _ha
    exact h a

end FiniteEdges
end FiniteHomotopySubdivision

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace E M] [IsManifold I ∞ M]

/-- At every positive scale, a finite subdivision has a seed-refining
subdivision whose two actual finite edge maxima are below that scale. -/
theorem exists_refinement_horizontalMaximum_verticalMaximum_lt
    [CompactSpace M] [ConnectedSpace M]
    (g : ClosedSmoothRiemannianMetric 3 M)
    {x y : M} {p₀ p₁ : Path x y} (F : p₀.Homotopy p₁)
    (seed : FiniteHomotopySubdivision)
    {eta : ℝ} (heta : 0 < eta) :
    letI : MetricSpace M := g.toMetricSpace
    ∃ fine : FiniteHomotopySubdivision,
      fine.Refines seed ∧
        fine.horizontalMaximum F < eta ∧
        fine.verticalMaximum F < eta := by
  letI : MetricSpace M := g.toMetricSpace
  rcases exists_refining_homotopy_grid_adjacent_dist_lt
      g F heta seed.nodes seed.nodes_zero seed.nodes_monotone
        seed.terminalIndex seed.nodes_one with
    ⟨nodes, terminalIndex, factor, hterminalIndex, hnodesZero,
      hnodesMonotone, hnodesOne, hfactorMonotone, hfactorZero,
      hfactorBound, hfactorValue, hhorizontal, hvertical⟩
  let fine : FiniteHomotopySubdivision :=
    { nodes := nodes
      terminalIndex := terminalIndex
      terminalIndex_pos := hterminalIndex
      nodes_zero := hnodesZero
      nodes_monotone := hnodesMonotone
      nodes_one := hnodesOne }
  refine ⟨fine, ?_, ?_, ?_⟩
  · exact ⟨factor, hfactorMonotone, hfactorZero, hfactorBound,
      hfactorValue⟩
  · rw [FiniteHomotopySubdivision.horizontalMaximum_lt_iff]
    intro a
    simpa [FiniteHomotopySubdivision.horizontalEdgeDistance, fine] using
      hhorizontal (a.1 : ℕ) (a.2 : ℕ)
  · rw [FiniteHomotopySubdivision.verticalMaximum_lt_iff]
    intro a
    simpa [FiniteHomotopySubdivision.verticalEdgeDistance, fine] using
      hvertical (a.1 : ℕ) (a.2 : ℕ)

/-- A countable family of finite homotopy subdivisions, each retaining every
node of one prescribed seed, whose actual horizontal and vertical finite edge
maxima vanish.

The stages need not refine one another.  Retaining the fixed seed at every
stage is the exact geometric fact needed before any separate transport of
realized successor histories is attempted. -/
theorem exists_seedRefining_homotopy_grid_sequence_finite_maxima_vanish
    [CompactSpace M] [ConnectedSpace M]
    (g : ClosedSmoothRiemannianMetric 3 M)
    {x y : M} {p₀ p₁ : Path x y} (F : p₀.Homotopy p₁)
    (seed : FiniteHomotopySubdivision) :
    letI : MetricSpace M := g.toMetricSpace
    ∃ stage : ℕ → FiniteHomotopySubdivision,
      (∀ n, (stage n).Refines seed) ∧
        (∀ n, (stage n).horizontalMaximum F <
          1 / ((n : ℝ) + 1)) ∧
        (∀ n, (stage n).verticalMaximum F <
          1 / ((n : ℝ) + 1)) ∧
        ∀ delta > (0 : ℝ), ∃ N, ∀ n ≥ N,
          (stage n).horizontalMaximum F < delta ∧
            (stage n).verticalMaximum F < delta := by
  letI : MetricSpace M := g.toMetricSpace
  have hstageExists : ∀ n : ℕ,
      ∃ fine : FiniteHomotopySubdivision,
        fine.Refines seed ∧
          fine.horizontalMaximum F < 1 / ((n : ℝ) + 1) ∧
          fine.verticalMaximum F < 1 / ((n : ℝ) + 1) := by
    intro n
    exact exists_refinement_horizontalMaximum_verticalMaximum_lt
      g F seed (Nat.one_div_pos_of_nat (α := ℝ))
  choose stage hstage using hstageExists
  refine ⟨stage, ?_, ?_, ?_, ?_⟩
  · intro n
    exact (hstage n).1
  · intro n
    exact (hstage n).2.1
  · intro n
    exact (hstage n).2.2
  · intro delta hdelta
    rcases exists_nat_one_div_lt hdelta with ⟨N, hN⟩
    refine ⟨N, ?_⟩
    intro n hn
    have hthreshold :
        1 / ((n : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) :=
      Nat.one_div_le_one_div hn
    exact ⟨((hstage n).2.1.trans_le hthreshold).trans hN,
      ((hstage n).2.2.trans_le hthreshold).trans hN⟩

end DifferentialHomotopyGridFiniteMaximaRefinement
end Poincare
