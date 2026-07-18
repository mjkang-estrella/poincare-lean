import Poincare.Global.CartanCanonicalRootedEndpointAssembly
import Poincare.Global.DifferentialSuccessorFiniteRealizedGridCommonRadius

/-!
# Rooted overlap transport through a realized homotopy grid

Two rooted endpoint continuations ending at `x` and `y` need not be related by
a strict factor schedule.  Given short terminal paths from `x` and `y` to one
overlap point `z`, they instead determine two independent paths from the
common root to `z`.  Simple connectivity supplies a homotopy between those
paths.

This file records the exact finite realized differential grid needed by the
existing common-radius theorem.  The only boundary identifications retained
by the grid are the predecessor states reached by the original endpoint
continuations.  Horizontal and vertical mesh bounds then identify the two
boundary terminal states; the constant terminal column is removed with the
zero-successor theorem to construct `CommonRootTerminalTransport`.

In particular, none of the definitions below requires
`RootedOverlapStrictFactorSchedule` or identifies samples of one endpoint path
with samples of the other.
-/

noncomputable section

open Set
open scoped Manifold ContDiff Topology unitInterval

namespace Poincare

set_option linter.unusedSectionVars false

universe u

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace E M]
variable [IsManifold I ∞ M]

namespace CartanCanonicalRootedEndpointAssembly
namespace TerminalShortPathCertificate

/-- Restrict a terminal `C¹` curve to the unit interval, retaining its
certified endpoints. -/
def toPath
    {g : ClosedSmoothRiemannianMetric 3 M} {y z : M} {mesh : ℝ}
    (certificate : TerminalShortPathCertificate g y z mesh) : Path y z :=
  Path.ofLine certificate.curve_contMDiffOn.continuousOn
    certificate.curve_zero certificate.curve_one

@[simp]
theorem toPath_apply
    {g : ClosedSmoothRiemannianMetric 3 M} {y z : M} {mesh : ℝ}
    (certificate : TerminalShortPathCertificate g y z mesh)
    (t : unitInterval) :
    certificate.toPath t = certificate.curve t :=
  rfl

end TerminalShortPathCertificate
end CartanCanonicalRootedEndpointAssembly

namespace CartanRootedOverlapHomotopyGrid

open CartanAtlasRealizedEndpointTransport
open CartanAtlasRootedReachableEndpointTransport
open CartanCanonicalRootedEndpointAssembly
open DifferentialInducedSuccessor
open DifferentialInducedSuccessor.Chain
open DifferentialSuccessorAdjacentContinuation
open DifferentialSuccessorFiniteRealizedGridCommonRadius

/-- The path from the fixed root to an overlap point obtained by following the
chosen root-to-endpoint path and then one independently supplied terminal
path. -/
def rootToOverlapPath
    {g : ClosedSmoothRiemannianMetric 3 M}
    (endpoint : RootedPathContinuedEndpointFamily g)
    {x z : M} {mesh : ℝ}
    (terminal : TerminalShortPathCertificate g x z mesh) :
    Path endpoint.root.anchor z :=
  (endpoint.path x).trans terminal.toPath

/-- Simple connectivity compares the two independent root-to-overlap paths.
No relation between their subdivisions is assumed. -/
noncomputable def overlapHomotopy
    [SimplyConnectedSpace M]
    {g : ClosedSmoothRiemannianMetric 3 M}
    (endpoint : RootedPathContinuedEndpointFamily g)
    {x y z : M} {leftMesh rightMesh : ℝ}
    (leftTerminal : TerminalShortPathCertificate g x z leftMesh)
    (rightTerminal : TerminalShortPathCertificate g y z rightMesh) :
    (rootToOverlapPath endpoint leftTerminal).Homotopy
      (rootToOverlapPath endpoint rightTerminal) :=
  Classical.choice
    (SimplyConnectedSpace.paths_homotopic
      (rootToOverlapPath endpoint leftTerminal)
      (rootToOverlapPath endpoint rightTerminal))

/-- A fixed finite realized grid for the homotopy between two independent
root-to-overlap paths.

The four realized families are exactly those consumed by
`exists_common_mesh_radius_for_fixed_realized_homotopyGrid_of_curvature`.
The two predecessor fields trace the left and right boundary rows back to the
actual terminal states of the rooted endpoint family. -/
structure RootedOverlapRealizedHomotopyGrid
    [SimplyConnectedSpace M]
    {g : ClosedSmoothRiemannianMetric 3 M}
    (endpoint : RootedPathContinuedEndpointFamily g)
    {x y z : M} {leftMesh rightMesh : ℝ}
    (leftTerminal : TerminalShortPathCertificate g x z leftMesh)
    (rightTerminal : TerminalShortPathCertificate g y z rightMesh) where
  subdivision : ℕ → unitInterval
  gridSize : ℕ
  gridSize_pos : 0 < gridSize
  subdivision_zero : subdivision 0 = 0
  subdivision_terminal : ∀ n ≥ gridSize, subdivision n = 1
  rowChain : ∀ m : Fin (gridSize + 2),
    ReachableChain
      (homotopyGridRow
        (overlapHomotopy endpoint leftTerminal rightTerminal)
        subdivision m)
      endpoint.root
  rungData : ∀ m : Fin (gridSize + 1), ∀ j : Fin (gridSize + 1),
    Data ((rowChain m.castSucc).state (j + 1))
      (homotopyGridRow
        (overlapHomotopy endpoint leftTerminal rightTerminal)
        subdivision (m + 1) (j + 1))
  bottomAtUpper : ∀ m : Fin (gridSize + 1), ∀ j : Fin (gridSize + 1),
    Data ((rowChain m.castSucc).state j)
      (homotopyGridRow
        (overlapHomotopy endpoint leftTerminal rightTerminal)
        subdivision (m + 1) (j + 1))
  rungAtNext : ∀ m : Fin (gridSize + 1), ∀ j : Fin gridSize,
    Data (rungData m j.castSucc).successor
      (homotopyGridRow
        (overlapHomotopy endpoint leftTerminal rightTerminal)
        subdivision (m + 1) (j + 2))
  left_predecessor :
    (rowChain 0).state (gridSize - 1) = endpoint.terminalState x
  right_predecessor :
    (rowChain (Fin.last (gridSize + 1))).state (gridSize - 1) =
      endpoint.terminalState y

namespace RootedOverlapRealizedHomotopyGrid

variable [SimplyConnectedSpace M]
variable {g : ClosedSmoothRiemannianMetric 3 M}
variable {endpoint : RootedPathContinuedEndpointFamily g}
variable {x y z : M} {leftMesh rightMesh : ℝ}
variable {leftTerminal : TerminalShortPathCertificate g x z leftMesh}
variable {rightTerminal : TerminalShortPathCertificate g y z rightMesh}

/-- Every sampled point in or beyond the terminal column is the common
overlap endpoint, independently of the row. -/
theorem row_node_eq_overlap
    (grid : RootedOverlapRealizedHomotopyGrid endpoint
      leftTerminal rightTerminal)
    (m n : ℕ) (hn : grid.gridSize ≤ n) :
    homotopyGridRow
        (overlapHomotopy endpoint leftTerminal rightTerminal)
        grid.subdivision m n = z := by
  simp [homotopyGridRow, grid.subdivision_terminal n hn]

/-- The initial Cartan state is anchored at the zeroth node of every row.
This follows from the relative boundary of the path homotopy. -/
theorem root_anchor_eq_row_zero
    (grid : RootedOverlapRealizedHomotopyGrid endpoint
      leftTerminal rightTerminal)
    (m : ℕ) :
    endpoint.root.anchor =
      homotopyGridRow
        (overlapHomotopy endpoint leftTerminal rightTerminal)
        grid.subdivision m 0 := by
  simp [homotopyGridRow, grid.subdivision_zero]

/-- The extra successor in the constant terminal column is the zero
successor, hence it does not change the reached Cartan state. -/
theorem row_terminal_tail_eq
    (grid : RootedOverlapRealizedHomotopyGrid endpoint
      leftTerminal rightTerminal)
    (m : Fin (grid.gridSize + 2)) :
    (grid.rowChain m).state (grid.gridSize + 1) =
      (grid.rowChain m).state grid.gridSize := by
  have hstateAnchor :
      ((grid.rowChain m).state grid.gridSize).anchor = z := by
    calc
      ((grid.rowChain m).state grid.gridSize).anchor =
          homotopyGridRow
            (overlapHomotopy endpoint leftTerminal rightTerminal)
            grid.subdivision m grid.gridSize :=
        (grid.rowChain m).state_anchor_eq_node
          (grid.root_anchor_eq_row_zero m) grid.gridSize
      _ = z := grid.row_node_eq_overlap m grid.gridSize le_rfl
  have hnextAtAnchor :
      homotopyGridRow
          (overlapHomotopy endpoint leftTerminal rightTerminal)
          grid.subdivision m (grid.gridSize + 1) =
        ((grid.rowChain m).state grid.gridSize).anchor := by
    exact
      (grid.row_node_eq_overlap m (grid.gridSize + 1)
        (Nat.le_add_right grid.gridSize 1)).trans hstateAnchor.symm
  have hvectorZero :
      ((grid.rowChain m).data grid.gridSize).v = 0 :=
    DifferentialSuccessorZero.data_vector_eq_zero_of_anchor_eq
      ((grid.rowChain m).data grid.gridSize) hnextAtAnchor
  calc
    (grid.rowChain m).state (grid.gridSize + 1) =
        ((grid.rowChain m).data grid.gridSize).successor :=
      (grid.rowChain m).state_succ grid.gridSize
    _ = (grid.rowChain m).state grid.gridSize :=
      DifferentialSuccessorZero.successor_eq_of_vector_eq_zero
        ((grid.rowChain m).data grid.gridSize) hvectorZero

/-- The common horizontal mesh bound for the exact fixed realized grid. -/
def HorizontalSmall
    [CompactSpace M] [ConnectedSpace M]
    (grid : RootedOverlapRealizedHomotopyGrid endpoint
      leftTerminal rightTerminal)
    (eta : ℝ) : Prop :=
  letI : MetricSpace M := g.toMetricSpace
  ∀ m : Fin (grid.gridSize + 2), ∀ j : Fin (grid.gridSize + 1),
    dist
      (homotopyGridRow
        (overlapHomotopy endpoint leftTerminal rightTerminal)
        grid.subdivision m (j + 1))
      (homotopyGridRow
        (overlapHomotopy endpoint leftTerminal rightTerminal)
        grid.subdivision m j) < eta

/-- The common vertical mesh bound for the exact fixed realized grid. -/
def VerticalSmall
    [CompactSpace M] [ConnectedSpace M]
    (grid : RootedOverlapRealizedHomotopyGrid endpoint
      leftTerminal rightTerminal)
    (eta : ℝ) : Prop :=
  letI : MetricSpace M := g.toMetricSpace
  ∀ m : Fin (grid.gridSize + 1), ∀ j : Fin (grid.gridSize + 1),
    dist
      (homotopyGridRow
        (overlapHomotopy endpoint leftTerminal rightTerminal)
        grid.subdivision (m + 1) (j + 1))
      (homotopyGridRow
        (overlapHomotopy endpoint leftTerminal rightTerminal)
        grid.subdivision m (j + 1)) < eta

/-- Constant curvature chooses a positive radius for one already-realized
grid.  The result remains conditional on that fixed grid satisfying both mesh
bounds, preserving the quantifier order of the analytic theorem. -/
theorem exists_commonMeshRadius
    [CompactSpace M] [ConnectedSpace M]
    (grid : RootedOverlapRealizedHomotopyGrid endpoint
      leftTerminal rightTerminal)
    (hcurv : HasConstantSectionalCurvature3 g 1) :
    ∃ eta > (0 : ℝ),
      grid.HorizontalSmall eta → grid.VerticalSmall eta →
      (grid.rowChain 0).state (grid.gridSize + 1) =
        (grid.rowChain (Fin.last (grid.gridSize + 1))).state
          (grid.gridSize + 1) := by
  letI : MetricSpace M := g.toMetricSpace
  simpa only [HorizontalSmall, VerticalSmall] using
    (exists_common_mesh_radius_for_fixed_realized_homotopyGrid_of_curvature
      hcurv (overlapHomotopy endpoint leftTerminal rightTerminal)
      endpoint.root rfl grid.subdivision grid.subdivision_zero grid.gridSize
      grid.subdivision_terminal grid.rowChain grid.rungData
      grid.bottomAtUpper grid.rungAtNext)

/-- A canonical choice of the positive radius supplied for this fixed
realized grid. -/
noncomputable def commonMeshRadius
    [CompactSpace M] [ConnectedSpace M]
    (grid : RootedOverlapRealizedHomotopyGrid endpoint
      leftTerminal rightTerminal)
    (hcurv : HasConstantSectionalCurvature3 g 1) : ℝ :=
  Classical.choose (grid.exists_commonMeshRadius hcurv)

theorem commonMeshRadius_pos
    [CompactSpace M] [ConnectedSpace M]
    (grid : RootedOverlapRealizedHomotopyGrid endpoint
      leftTerminal rightTerminal)
    (hcurv : HasConstantSectionalCurvature3 g 1) :
    0 < grid.commonMeshRadius hcurv :=
  (Classical.choose_spec (grid.exists_commonMeshRadius hcurv)).1

/-- Horizontal and vertical smallness at the chosen radius identify the two
last states of the boundary rows. -/
theorem boundary_terminal_eq_of_small
    [CompactSpace M] [ConnectedSpace M]
    (grid : RootedOverlapRealizedHomotopyGrid endpoint
      leftTerminal rightTerminal)
    (hcurv : HasConstantSectionalCurvature3 g 1)
    (hhorizontal : grid.HorizontalSmall (grid.commonMeshRadius hcurv))
    (hvertical : grid.VerticalSmall (grid.commonMeshRadius hcurv)) :
    (grid.rowChain 0).state (grid.gridSize + 1) =
      (grid.rowChain (Fin.last (grid.gridSize + 1))).state
        (grid.gridSize + 1) :=
  (Classical.choose_spec (grid.exists_commonMeshRadius hcurv)).2
    hhorizontal hvertical

/-- Convert a boundary endpoint equality into the concrete transport consumed
by Cartan-atlas compatibility.  The predecessor indices are `gridSize - 1`;
the stored boundary traces identify those states with the original rooted
endpoint states.  The zero terminal tail moves the grid equality back from
column `gridSize + 1` to the common next-node column `gridSize`. -/
def toCommonRootTerminalTransport_of_boundary_eq
    (grid : RootedOverlapRealizedHomotopyGrid endpoint
      leftTerminal rightTerminal)
    (hterminal :
      (grid.rowChain 0).state (grid.gridSize + 1) =
        (grid.rowChain (Fin.last (grid.gridSize + 1))).state
          (grid.gridSize + 1)) :
    CommonRootTerminalTransport
      (endpoint.terminalState x) (endpoint.terminalState y) z := by
  refine
    { root := endpoint.root
      leftNodes :=
        homotopyGridRow
          (overlapHomotopy endpoint leftTerminal rightTerminal)
          grid.subdivision 0
      rightNodes :=
        homotopyGridRow
          (overlapHomotopy endpoint leftTerminal rightTerminal)
          grid.subdivision (Fin.last (grid.gridSize + 1))
      leftChain := grid.rowChain 0
      rightChain := grid.rowChain (Fin.last (grid.gridSize + 1))
      leftIndex := grid.gridSize - 1
      rightIndex := grid.gridSize - 1
      left_predecessor := grid.left_predecessor
      right_predecessor := grid.right_predecessor
      left_next_node := ?_
      right_next_node := ?_
      terminal_eq := ?_ }
  · rw [Nat.sub_add_cancel grid.gridSize_pos]
    exact grid.row_node_eq_overlap 0 grid.gridSize le_rfl
  · rw [Nat.sub_add_cancel grid.gridSize_pos]
    exact
      grid.row_node_eq_overlap (Fin.last (grid.gridSize + 1))
        grid.gridSize le_rfl
  · rw [Nat.sub_add_cancel grid.gridSize_pos]
    exact
      (grid.row_terminal_tail_eq 0).symm.trans
        (hterminal.trans
          (grid.row_terminal_tail_eq
            (Fin.last (grid.gridSize + 1))))

/-- The chosen common radius and its two mesh bounds construct a genuine
common-root terminal transport without a strict factor schedule. -/
noncomputable def toCommonRootTerminalTransport
    [CompactSpace M] [ConnectedSpace M]
    (grid : RootedOverlapRealizedHomotopyGrid endpoint
      leftTerminal rightTerminal)
    (hcurv : HasConstantSectionalCurvature3 g 1)
    (hhorizontal : grid.HorizontalSmall (grid.commonMeshRadius hcurv))
    (hvertical : grid.VerticalSmall (grid.commonMeshRadius hcurv)) :
    CommonRootTerminalTransport
      (endpoint.terminalState x) (endpoint.terminalState y) z :=
  grid.toCommonRootTerminalTransport_of_boundary_eq
    (grid.boundary_terminal_eq_of_small hcurv hhorizontal hvertical)

/-- The realized homotopy-grid transport gives the overlap equality needed by
the Cartan-atlas consumer. -/
theorem germ_value_eq_of_small
    [CompactSpace M] [ConnectedSpace M]
    (grid : RootedOverlapRealizedHomotopyGrid endpoint
      leftTerminal rightTerminal)
    (hcurv : HasConstantSectionalCurvature3 g 1)
    (hhorizontal : grid.HorizontalSmall (grid.commonMeshRadius hcurv))
    (hvertical : grid.VerticalSmall (grid.commonMeshRadius hcurv)) :
    (endpoint.terminalState x).germ z =
      (endpoint.terminalState y).germ z :=
  germ_value_eq_of_commonRootTerminalTransport
    (endpoint.terminalState x) (endpoint.terminalState y) z
    (grid.toCommonRootTerminalTransport hcurv hhorizontal hvertical)

end RootedOverlapRealizedHomotopyGrid
end CartanRootedOverlapHomotopyGrid
end Poincare
