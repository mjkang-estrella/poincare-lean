import Poincare.Global.CartanRootedOverlapReparameterizedHomotopyGrid
import Poincare.Global.CartanAtlasRootedPathAdaptiveMeshRealization

/-!
# Realizing reparameterized overlap grids from one uniform successor radius

Once one successor-data radius works for every actually reached Cartan state,
geometric smallness of a fixed reparameterized homotopy grid constructs all
of its row, rung, and cross-cell differential data.  Horizontal and vertical
edges are required to be smaller than half the radius; the diagonal datum
then follows from the triangle inequality.

This removes the realized differential fields from the construction input.
It does not assert that a reparameterized homotopy grid can be chosen small
relative to the state-dependent common radius selected after realization.
-/

noncomputable section

open Metric Set
open scoped Manifold ContDiff Topology unitInterval

namespace Poincare
namespace CartanRootedOverlapReparameterizedGridRealization

set_option linter.unusedSectionVars false

open CartanAtlasRootedPathAdaptiveMeshRealization
open CartanAtlasRootedReachableEndpointTransport
open CartanCanonicalRootedEndpointAssembly
open CartanRootedOverlapReparameterizedBoundaryState
open CartanRootedOverlapReparameterizedHomotopyGrid
open DifferentialInducedSuccessor
open DifferentialInducedSuccessor.Chain
open DifferentialSuccessorAdjacentContinuation

universe u

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace E M]
variable [IsManifold I ∞ M]
variable [CompactSpace M] [ConnectedSpace M]

variable {g : ClosedSmoothRiemannianMetric 3 M}

/-- Horizontal edges of the fixed common grid are smaller than half of the
uniform successor-data radius. -/
def HorizontalHalfRadiusSmall
    [SimplyConnectedSpace M]
    (endpoint : RootedPathContinuedEndpointFamily g)
    {x y z : M} {leftMesh rightMesh : ℝ}
    (leftTerminal : TerminalShortPathCertificate g x z leftMesh)
    (rightTerminal : TerminalShortPathCertificate g y z rightMesh)
    (N : ℕ) (rho : ℝ) : Prop :=
  letI : MetricSpace M := g.toMetricSpace
  ∀ m : Fin (N + 3), ∀ j : Fin (N + 2),
    dist
      (reparameterizedOverlapGridRow
        endpoint leftTerminal rightTerminal N m (j + 1))
      (reparameterizedOverlapGridRow
        endpoint leftTerminal rightTerminal N m j) < rho / 2

/-- Vertical edges of the fixed common grid are smaller than half of the
uniform successor-data radius. -/
def VerticalHalfRadiusSmall
    [SimplyConnectedSpace M]
    (endpoint : RootedPathContinuedEndpointFamily g)
    {x y z : M} {leftMesh rightMesh : ℝ}
    (leftTerminal : TerminalShortPathCertificate g x z leftMesh)
    (rightTerminal : TerminalShortPathCertificate g y z rightMesh)
    (N : ℕ) (rho : ℝ) : Prop :=
  letI : MetricSpace M := g.toMetricSpace
  ∀ m : Fin (N + 2), ∀ j : Fin (N + 2),
    dist
      (reparameterizedOverlapGridRow
        endpoint leftTerminal rightTerminal N (m + 1) (j + 1))
      (reparameterizedOverlapGridRow
        endpoint leftTerminal rightTerminal N m (j + 1)) < rho / 2

/-- The root is the zeroth node of every row before any differential data
have been selected. -/
theorem root_anchor_eq_reparameterizedOverlapGridRow_zero
    [SimplyConnectedSpace M]
    (endpoint : RootedPathContinuedEndpointFamily g)
    {x y z : M} {leftMesh rightMesh : ℝ}
    (leftTerminal : TerminalShortPathCertificate g x z leftMesh)
    (rightTerminal : TerminalShortPathCertificate g y z rightMesh)
    (N m : ℕ) :
    endpoint.root.anchor =
      reparameterizedOverlapGridRow
        endpoint leftTerminal rightTerminal N m 0 := by
  simp [reparameterizedOverlapGridRow, homotopyGridRow,
    commonUniformSubdivision_zero]

/-- Every row is stationary after the common overlap column `N + 1`. -/
theorem reparameterizedOverlapGridRow_stationary
    [SimplyConnectedSpace M]
    (endpoint : RootedPathContinuedEndpointFamily g)
    {x y z : M} {leftMesh rightMesh : ℝ}
    (leftTerminal : TerminalShortPathCertificate g x z leftMesh)
    (rightTerminal : TerminalShortPathCertificate g y z rightMesh)
    (N n m : ℕ) (hn : N + 1 ≤ n) :
    reparameterizedOverlapGridRow
        endpoint leftTerminal rightTerminal N m n =
      reparameterizedOverlapGridRow
        endpoint leftTerminal rightTerminal N m (N + 1) := by
  simp [reparameterizedOverlapGridRow, homotopyGridRow,
    commonUniformSubdivision_terminal N n hn]

/-- One radius valid for every Cartan state, together with half-radius edge
smallness, constructs the complete realized reparameterized homotopy grid.

Rows are built by dependent recursion, querying successor data only at the
state actually reached.  `bottomAtUpper` uses one horizontal and one vertical
half-radius edge; the remaining cross-cell data use a single half-radius
edge. -/
noncomputable def realizedGrid_of_uniformSuccessorRadius
    [SimplyConnectedSpace M]
    (endpoint : RootedPathContinuedEndpointFamily g)
    {x y z : M} {leftMesh rightMesh : ℝ}
    (leftTerminal : TerminalShortPathCertificate g x z leftMesh)
    (rightTerminal : TerminalShortPathCertificate g y z rightMesh)
    (N : ℕ)
    (hleft : endpoint.terminalIndex x ≤ N)
    (hright : endpoint.terminalIndex y ≤ N)
    (rho : ℝ) (hrho : 0 < rho)
    (hdata : letI : MetricSpace M := g.toMetricSpace
      ∀ (s : CartanChain.ChainState g) (q : M),
        dist q s.anchor < rho → Nonempty (Data s q))
    (hhorizontal :
      HorizontalHalfRadiusSmall endpoint leftTerminal rightTerminal N rho)
    (hvertical :
      VerticalHalfRadiusSmall endpoint leftTerminal rightTerminal N rho) :
    ReparameterizedRootedOverlapRealizedHomotopyGrid endpoint
      leftTerminal rightTerminal N := by
  classical
  letI : MetricSpace M := g.toMetricSpace
  have hhalf : rho / 2 < rho := half_lt_self hrho
  let rowChain : ∀ m : Fin (N + 3),
      ReachableChain
        (reparameterizedOverlapGridRow
          endpoint leftTerminal rightTerminal N m)
        endpoint.root := fun m ↦
    reachableChain_of_finite_anchored_step_supply
      (reparameterizedOverlapGridRow
        endpoint leftTerminal rightTerminal N m)
      endpoint.root (N + 1)
      (root_anchor_eq_reparameterizedOverlapGridRow_zero
        endpoint leftTerminal rightTerminal N m)
      (fun n hn ↦
        reparameterizedOverlapGridRow_stationary
          endpoint leftTerminal rightTerminal N n m hn)
      (by
        intro i s hs
        apply hdata s
        rw [hs]
        exact (hhorizontal m i.castSucc).trans hhalf)
  let rungData : ∀ m : Fin (N + 2), ∀ j : Fin (N + 2),
      Data ((rowChain m.castSucc).state (j + 1))
        (reparameterizedOverlapGridRow
          endpoint leftTerminal rightTerminal N (m + 1) (j + 1)) := by
    intro m j
    apply Classical.choice
    apply hdata
    have hanchor :=
      (rowChain m.castSucc).state_anchor_eq_node
        (root_anchor_eq_reparameterizedOverlapGridRow_zero
          endpoint leftTerminal rightTerminal N m.castSucc) (j + 1)
    rw [hanchor]
    exact (hvertical m j).trans hhalf
  let bottomAtUpper : ∀ m : Fin (N + 2), ∀ j : Fin (N + 2),
      Data ((rowChain m.castSucc).state j)
        (reparameterizedOverlapGridRow
          endpoint leftTerminal rightTerminal N (m + 1) (j + 1)) := by
    intro m j
    apply Classical.choice
    apply hdata
    have hanchor :=
      (rowChain m.castSucc).state_anchor_eq_node
        (root_anchor_eq_reparameterizedOverlapGridRow_zero
          endpoint leftTerminal rightTerminal N m.castSucc) j
    rw [hanchor]
    calc
      dist
          (reparameterizedOverlapGridRow
            endpoint leftTerminal rightTerminal N (m + 1) (j + 1))
          (reparameterizedOverlapGridRow
            endpoint leftTerminal rightTerminal N m j) ≤
        dist
            (reparameterizedOverlapGridRow
              endpoint leftTerminal rightTerminal N (m + 1) (j + 1))
            (reparameterizedOverlapGridRow
              endpoint leftTerminal rightTerminal N m (j + 1)) +
          dist
            (reparameterizedOverlapGridRow
              endpoint leftTerminal rightTerminal N m (j + 1))
            (reparameterizedOverlapGridRow
              endpoint leftTerminal rightTerminal N m j) :=
        dist_triangle _ _ _
      _ < rho / 2 + rho / 2 :=
        add_lt_add (hvertical m j) (hhorizontal m.castSucc j)
      _ = rho := by ring
  let rungAtNext : ∀ m : Fin (N + 2), ∀ j : Fin (N + 1),
      Data (rungData m j.castSucc).successor
        (reparameterizedOverlapGridRow
          endpoint leftTerminal rightTerminal N (m + 1) (j + 2)) := by
    intro m j
    apply Classical.choice
    apply hdata
    rw [(rungData m j.castSucc).successor_anchor]
    exact (hhorizontal m.succ j.succ).trans hhalf
  exact
    { left_terminalIndex_le := hleft
      right_terminalIndex_le := hright
      rowChain := rowChain
      rungData := rungData
      bottomAtUpper := bottomAtUpper
      rungAtNext := rungAtNext }

/-- Existence form of `realizedGrid_of_uniformSuccessorRadius`. -/
theorem nonempty_realizedGrid_of_uniformSuccessorRadius
    [SimplyConnectedSpace M]
    (endpoint : RootedPathContinuedEndpointFamily g)
    {x y z : M} {leftMesh rightMesh : ℝ}
    (leftTerminal : TerminalShortPathCertificate g x z leftMesh)
    (rightTerminal : TerminalShortPathCertificate g y z rightMesh)
    (N : ℕ)
    (hleft : endpoint.terminalIndex x ≤ N)
    (hright : endpoint.terminalIndex y ≤ N)
    (rho : ℝ) (hrho : 0 < rho)
    (hdata : letI : MetricSpace M := g.toMetricSpace
      ∀ (s : CartanChain.ChainState g) (q : M),
        dist q s.anchor < rho → Nonempty (Data s q))
    (hhorizontal :
      HorizontalHalfRadiusSmall endpoint leftTerminal rightTerminal N rho)
    (hvertical :
      VerticalHalfRadiusSmall endpoint leftTerminal rightTerminal N rho) :
    Nonempty
      (ReparameterizedRootedOverlapRealizedHomotopyGrid endpoint
        leftTerminal rightTerminal N) :=
  ⟨realizedGrid_of_uniformSuccessorRadius endpoint leftTerminal rightTerminal
    N hleft hright rho hrho hdata hhorizontal hvertical⟩

end CartanRootedOverlapReparameterizedGridRealization
end Poincare
