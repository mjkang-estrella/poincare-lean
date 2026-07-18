import Poincare.Global.CartanAtlasRootedPathAdaptiveMeshRealization
import Poincare.Global.DifferentialSuccessorFiniteRealizedGridCommonRadius

/-!
# Uniform-radius realization on an arbitrary finite homotopy subdivision

The rooted-overlap realization used a particular reparameterized homotopy and
its uniform subdivision.  The dependent recursion itself needs neither of
those choices.  This file isolates the exact general statement: for an
arbitrary path homotopy `F`, eventually stationary subdivision `t`, and
terminal index `K`, one state-uniform successor-data radius realizes every
row, rung, and cross-cell datum as soon as the two actual edge families are
smaller than half that radius.

The resulting record retains the initial-anchor and subdivision endpoint
proofs needed by the existing post-realization common-radius theorem.  It has
no rooted-boundary provenance: relating a refined boundary row to an older
rooted endpoint chain is a separate strict-factor transport problem.
-/

noncomputable section

open Metric Set
open scoped Manifold ContDiff Topology unitInterval

namespace Poincare
namespace DifferentialSuccessorArbitraryFiniteGridUniformRadiusRealization

set_option linter.unusedSectionVars false

open CartanAtlasRootedPathAdaptiveMeshRealization
open DifferentialInducedSuccessor
open DifferentialInducedSuccessor.Chain
open DifferentialSuccessorAdjacentContinuation
open DifferentialSuccessorFiniteRealizedGridCommonRadius

universe u

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace E M]
variable [IsManifold I ∞ M]

variable {g : ClosedSmoothRiemannianMetric 3 M}

/-- Horizontal edges in the finite displayed part of an arbitrary homotopy
grid are smaller than half of `rho`. -/
def HorizontalHalfRadiusSmall
    [CompactSpace M] [ConnectedSpace M]
    {x y : M} {p₀ p₁ : Path x y} (F : p₀.Homotopy p₁)
    (t : ℕ → unitInterval) (K : ℕ) (rho : ℝ) : Prop :=
  letI : MetricSpace M := g.toMetricSpace
  ∀ m : Fin (K + 2), ∀ j : Fin (K + 1),
    dist (homotopyGridRow F t m (j + 1))
      (homotopyGridRow F t m j) < rho / 2

/-- Vertical edges in the finite displayed part of an arbitrary homotopy
grid are smaller than half of `rho`. -/
def VerticalHalfRadiusSmall
    [CompactSpace M] [ConnectedSpace M]
    {x y : M} {p₀ p₁ : Path x y} (F : p₀.Homotopy p₁)
    (t : ℕ → unitInterval) (K : ℕ) (rho : ℝ) : Prop :=
  letI : MetricSpace M := g.toMetricSpace
  ∀ m : Fin (K + 1), ∀ j : Fin (K + 1),
    dist (homotopyGridRow F t (m + 1) (j + 1))
      (homotopyGridRow F t m (j + 1)) < rho / 2

/-- The actual differential data realized on one arbitrary finite homotopy
grid.  The record is deliberately generic in `F`, `t`, and `K`. -/
structure RealizedHomotopyGrid
    {x y : M} {p₀ p₁ : Path x y} (F : p₀.Homotopy p₁)
    (initial : CartanChain.ChainState g)
    (t : ℕ → unitInterval) (K : ℕ) where
  initial_anchor : initial.anchor = x
  subdivision_zero : t 0 = 0
  subdivision_terminal : ∀ n ≥ K, t n = 1
  rowChain : ∀ m : Fin (K + 2),
    ReachableChain (homotopyGridRow F t m) initial
  rungData : ∀ m : Fin (K + 1), ∀ j : Fin (K + 1),
    Data ((rowChain m.castSucc).state (j + 1))
      (homotopyGridRow F t (m + 1) (j + 1))
  bottomAtUpper : ∀ m : Fin (K + 1), ∀ j : Fin (K + 1),
    Data ((rowChain m.castSucc).state j)
      (homotopyGridRow F t (m + 1) (j + 1))
  rungAtNext : ∀ m : Fin (K + 1), ∀ j : Fin K,
    Data (rungData m j.castSucc).successor
      (homotopyGridRow F t (m + 1) (j + 2))

namespace RealizedHomotopyGrid

/-- Constant curvature selects the usual positive common radius for the
actual arbitrary grid, after all of its histories have been realized. -/
theorem exists_commonMeshRadius
    [CompactSpace M] [ConnectedSpace M]
    {x y : M} {p₀ p₁ : Path x y} {F : p₀.Homotopy p₁}
    {initial : CartanChain.ChainState g}
    {t : ℕ → unitInterval} {K : ℕ}
    (grid : RealizedHomotopyGrid F initial t K)
    (hcurv : HasConstantSectionalCurvature3 g 1) :
    letI : MetricSpace M := g.toMetricSpace
    ∃ eta > (0 : ℝ),
      (∀ m : Fin (K + 2), ∀ j : Fin (K + 1),
        dist (homotopyGridRow F t m (j + 1))
          (homotopyGridRow F t m j) < eta) →
      (∀ m : Fin (K + 1), ∀ j : Fin (K + 1),
        dist (homotopyGridRow F t (m + 1) (j + 1))
          (homotopyGridRow F t m (j + 1)) < eta) →
      (grid.rowChain 0).state (K + 1) =
        (grid.rowChain (Fin.last (K + 1))).state (K + 1) := by
  letI : MetricSpace M := g.toMetricSpace
  exact
    exists_common_mesh_radius_for_fixed_realized_homotopyGrid_of_curvature
      hcurv F initial grid.initial_anchor t grid.subdivision_zero K
        grid.subdivision_terminal grid.rowChain grid.rungData
        grid.bottomAtUpper grid.rungAtNext

end RealizedHomotopyGrid

/-- One uniform successor-data radius realizes the complete differential grid
on any eventually stationary finite homotopy subdivision.

Rows are constructed by dependent recursion at their actually reached
states.  One horizontal plus one vertical half-radius edge supplies the
diagonal `bottomAtUpper` datum; every other requested datum uses one
half-radius edge. -/
noncomputable def realizedGrid_of_uniformSuccessorRadius
    [CompactSpace M] [ConnectedSpace M]
    {x y : M} {p₀ p₁ : Path x y} (F : p₀.Homotopy p₁)
    (initial : CartanChain.ChainState g) (hinitial : initial.anchor = x)
    (t : ℕ → unitInterval) (K : ℕ)
    (htzero : t 0 = 0) (htone : ∀ n ≥ K, t n = 1)
    (rho : ℝ) (hrho : 0 < rho)
    (hdata : letI : MetricSpace M := g.toMetricSpace
      ∀ (s : CartanChain.ChainState g) (q : M),
        dist q s.anchor < rho → Nonempty (Data s q))
    (hhorizontal : HorizontalHalfRadiusSmall (g := g) F t K rho)
    (hvertical : VerticalHalfRadiusSmall (g := g) F t K rho) :
    RealizedHomotopyGrid F initial t K := by
  classical
  letI : MetricSpace M := g.toMetricSpace
  have hhalf : rho / 2 < rho := half_lt_self hrho
  have hroot : ∀ m : ℕ,
      initial.anchor = homotopyGridRow F t m 0 := by
    intro m
    simpa [homotopyGridRow, htzero] using hinitial
  have hstationary : ∀ m n : ℕ, K ≤ n →
      homotopyGridRow F t m n = homotopyGridRow F t m K := by
    intro m n hn
    simp only [homotopyGridRow, htone n hn, htone K le_rfl]
  let rowChain : ∀ m : Fin (K + 2),
      ReachableChain (homotopyGridRow F t m) initial := fun m ↦
    reachableChain_of_finite_anchored_step_supply
      (homotopyGridRow F t m) initial K (hroot m)
      (hstationary m)
      (by
        intro i s hs
        apply hdata s
        rw [hs]
        exact (hhorizontal m i.castSucc).trans hhalf)
  let rungData : ∀ m : Fin (K + 1), ∀ j : Fin (K + 1),
      Data ((rowChain m.castSucc).state (j + 1))
        (homotopyGridRow F t (m + 1) (j + 1)) := by
    intro m j
    apply Classical.choice
    apply hdata
    rw [(rowChain m.castSucc).state_anchor_eq_node (hroot m) (j + 1)]
    exact (hvertical m j).trans hhalf
  let bottomAtUpper : ∀ m : Fin (K + 1), ∀ j : Fin (K + 1),
      Data ((rowChain m.castSucc).state j)
        (homotopyGridRow F t (m + 1) (j + 1)) := by
    intro m j
    apply Classical.choice
    apply hdata
    rw [(rowChain m.castSucc).state_anchor_eq_node (hroot m) j]
    calc
      dist (homotopyGridRow F t (m + 1) (j + 1))
          (homotopyGridRow F t m j) ≤
        dist (homotopyGridRow F t (m + 1) (j + 1))
            (homotopyGridRow F t m (j + 1)) +
          dist (homotopyGridRow F t m (j + 1))
            (homotopyGridRow F t m j) :=
        dist_triangle _ _ _
      _ < rho / 2 + rho / 2 :=
        add_lt_add (hvertical m j) (hhorizontal m.castSucc j)
      _ = rho := by ring
  let rungAtNext : ∀ m : Fin (K + 1), ∀ j : Fin K,
      Data (rungData m j.castSucc).successor
        (homotopyGridRow F t (m + 1) (j + 2)) := by
    intro m j
    apply Classical.choice
    apply hdata
    rw [(rungData m j.castSucc).successor_anchor]
    exact (hhorizontal m.succ j.succ).trans hhalf
  exact
    { initial_anchor := hinitial
      subdivision_zero := htzero
      subdivision_terminal := htone
      rowChain := rowChain
      rungData := rungData
      bottomAtUpper := bottomAtUpper
      rungAtNext := rungAtNext }

/-- Existence form of the arbitrary-grid realization theorem. -/
theorem nonempty_realizedGrid_of_uniformSuccessorRadius
    [CompactSpace M] [ConnectedSpace M]
    {x y : M} {p₀ p₁ : Path x y} (F : p₀.Homotopy p₁)
    (initial : CartanChain.ChainState g) (hinitial : initial.anchor = x)
    (t : ℕ → unitInterval) (K : ℕ)
    (htzero : t 0 = 0) (htone : ∀ n ≥ K, t n = 1)
    (rho : ℝ) (hrho : 0 < rho)
    (hdata : letI : MetricSpace M := g.toMetricSpace
      ∀ (s : CartanChain.ChainState g) (q : M),
        dist q s.anchor < rho → Nonempty (Data s q))
    (hhorizontal : HorizontalHalfRadiusSmall (g := g) F t K rho)
    (hvertical : VerticalHalfRadiusSmall (g := g) F t K rho) :
    Nonempty (RealizedHomotopyGrid F initial t K) :=
  ⟨realizedGrid_of_uniformSuccessorRadius F initial hinitial t K htzero
    htone rho hrho hdata hhorizontal hvertical⟩

end DifferentialSuccessorArbitraryFiniteGridUniformRadiusRealization
end Poincare
