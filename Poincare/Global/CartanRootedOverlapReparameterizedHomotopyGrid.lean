import Poincare.Global.CartanRootedOverlapReparameterizedBoundaryState

/-!
# Realized homotopy grids with reparameterized boundary provenance

The two rooted endpoint chains may use unrelated node-time sequences.  The
reparameterized boundary construction places both root-to-overlap paths on one
uniform column grid.  This file records the remaining realized differential
data for a homotopy between those paths.

Unlike `CartanRootedOverlapHomotopyGrid.RootedOverlapRealizedHomotopyGrid`,
the structure below has no stored left or right predecessor equality.  Its
boundary rows are definitionally selected from the reparameterized homotopy,
and the predecessor identities are theorems obtained by transporting those
rows to `reparameterizedBoundaryNodes` and applying reachable-chain state
provenance.
-/

noncomputable section

open Set
open scoped Manifold ContDiff Topology unitInterval

namespace Poincare
namespace CartanRootedOverlapReparameterizedHomotopyGrid

set_option linter.unusedSectionVars false

open CartanAtlasRealizedEndpointTransport
open CartanAtlasRootedReachableEndpointTransport
open CartanCanonicalRootedEndpointAssembly
open CartanRootedOverlapReparameterizedBoundary
open CartanRootedOverlapReparameterizedBoundaryState
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

/-- One row of the reparameterized overlap homotopy, sampled with the common
uniform subdivision. -/
def reparameterizedOverlapGridRow
    [SimplyConnectedSpace M]
    (endpoint : RootedPathContinuedEndpointFamily g)
    {x y z : M} {leftMesh rightMesh : ℝ}
    (leftTerminal : TerminalShortPathCertificate g x z leftMesh)
    (rightTerminal : TerminalShortPathCertificate g y z rightMesh)
    (N m : ℕ) : ℕ → M :=
  homotopyGridRow
    (reparameterizedOverlapHomotopy endpoint leftTerminal rightTerminal N)
    (commonUniformSubdivision N) m

/-- The zeroth homotopy row is exactly the reparameterized left boundary node
sequence. -/
theorem reparameterizedOverlapGridRow_zero
    [SimplyConnectedSpace M]
    (endpoint : RootedPathContinuedEndpointFamily g)
    {x y z : M} {leftMesh rightMesh : ℝ}
    (leftTerminal : TerminalShortPathCertificate g x z leftMesh)
    (rightTerminal : TerminalShortPathCertificate g y z rightMesh)
    (N : ℕ) :
    reparameterizedOverlapGridRow endpoint leftTerminal rightTerminal N 0 =
      reparameterizedBoundaryNodes endpoint leftTerminal N := by
  funext n
  simp [reparameterizedOverlapGridRow, homotopyGridRow,
    reparameterizedBoundaryNodes, commonUniformSubdivision_zero]

/-- The last realized row is exactly the reparameterized right boundary node
sequence.  Its row index lies beyond the terminal index of the common
subdivision, so the homotopy parameter is `1`. -/
theorem reparameterizedOverlapGridRow_last
    [SimplyConnectedSpace M]
    (endpoint : RootedPathContinuedEndpointFamily g)
    {x y z : M} {leftMesh rightMesh : ℝ}
    (leftTerminal : TerminalShortPathCertificate g x z leftMesh)
    (rightTerminal : TerminalShortPathCertificate g y z rightMesh)
    (N : ℕ) :
    reparameterizedOverlapGridRow endpoint leftTerminal rightTerminal N
        (Fin.last (N + 2)) =
      reparameterizedBoundaryNodes endpoint rightTerminal N := by
  funext n
  change
    reparameterizedOverlapHomotopy endpoint leftTerminal rightTerminal N
        (commonUniformSubdivision N (N + 2),
          commonUniformSubdivision N n) =
      reparameterizedRootToOverlapPath endpoint rightTerminal N
        (commonUniformSubdivision N n)
  rw [commonUniformSubdivision_terminal N (N + 2) (by omega)]
  simp

/-- Transport a realized chain across an equality of its node sequences. -/
def transportReachableChain
    {nodes₁ nodes₂ : ℕ → M}
    {initial : CartanChain.ChainState g}
    (chain : ReachableChain nodes₁ initial)
    (hnodes : nodes₁ = nodes₂) :
    ReachableChain nodes₂ initial :=
  hnodes ▸ chain

@[simp]
theorem transportReachableChain_state
    {nodes₁ nodes₂ : ℕ → M}
    {initial : CartanChain.ChainState g}
    (chain : ReachableChain nodes₁ initial)
    (hnodes : nodes₁ = nodes₂)
    (n : ℕ) :
    (transportReachableChain chain hnodes).state n = chain.state n := by
  cases hnodes
  rfl

/-- A realized differential grid for the reparameterized overlap homotopy.

`N` is the common predecessor column.  The common subdivision becomes
constant at `1` from column `N + 1` onward, so the generic realized-grid size
is `N + 1`.  The terminal-index bounds are the only boundary provenance
stored in this record; the actual predecessor state equalities are derived
below. -/
structure ReparameterizedRootedOverlapRealizedHomotopyGrid
    [SimplyConnectedSpace M]
    (endpoint : RootedPathContinuedEndpointFamily g)
    {x y z : M} {leftMesh rightMesh : ℝ}
    (leftTerminal : TerminalShortPathCertificate g x z leftMesh)
    (rightTerminal : TerminalShortPathCertificate g y z rightMesh)
    (N : ℕ) where
  left_terminalIndex_le : endpoint.terminalIndex x ≤ N
  right_terminalIndex_le : endpoint.terminalIndex y ≤ N
  rowChain : ∀ m : Fin (N + 3),
    ReachableChain
      (reparameterizedOverlapGridRow
        endpoint leftTerminal rightTerminal N m)
      endpoint.root
  rungData : ∀ m : Fin (N + 2), ∀ j : Fin (N + 2),
    Data ((rowChain m.castSucc).state (j + 1))
      (reparameterizedOverlapGridRow
        endpoint leftTerminal rightTerminal N (m + 1) (j + 1))
  bottomAtUpper : ∀ m : Fin (N + 2), ∀ j : Fin (N + 2),
    Data ((rowChain m.castSucc).state j)
      (reparameterizedOverlapGridRow
        endpoint leftTerminal rightTerminal N (m + 1) (j + 1))
  rungAtNext : ∀ m : Fin (N + 2), ∀ j : Fin (N + 1),
    Data (rungData m j.castSucc).successor
      (reparameterizedOverlapGridRow
        endpoint leftTerminal rightTerminal N (m + 1) (j + 2))

namespace ReparameterizedRootedOverlapRealizedHomotopyGrid

variable [SimplyConnectedSpace M]
variable {endpoint : RootedPathContinuedEndpointFamily g}
variable {x y z : M} {leftMesh rightMesh : ℝ}
variable {leftTerminal : TerminalShortPathCertificate g x z leftMesh}
variable {rightTerminal : TerminalShortPathCertificate g y z rightMesh}
variable {N : ℕ}

/-- The realized zeroth row, transported to the exact node family consumed by
the left boundary-state provenance theorem. -/
def leftBoundaryChain
    (grid : ReparameterizedRootedOverlapRealizedHomotopyGrid
      endpoint leftTerminal rightTerminal N) :
    ReachableChain
      (reparameterizedBoundaryNodes endpoint leftTerminal N)
      endpoint.root :=
  transportReachableChain (grid.rowChain 0)
    (reparameterizedOverlapGridRow_zero
      endpoint leftTerminal rightTerminal N)

/-- The realized last row, transported to the exact node family consumed by
the right boundary-state provenance theorem. -/
def rightBoundaryChain
    (grid : ReparameterizedRootedOverlapRealizedHomotopyGrid
      endpoint leftTerminal rightTerminal N) :
    ReachableChain
      (reparameterizedBoundaryNodes endpoint rightTerminal N)
      endpoint.root :=
  transportReachableChain (grid.rowChain (Fin.last (N + 2)))
    (reparameterizedOverlapGridRow_last
      endpoint leftTerminal rightTerminal N)

/-- The left predecessor identity is a theorem from reachable-chain state
provenance, not a field of the realized-grid record. -/
theorem left_predecessor
    (grid : ReparameterizedRootedOverlapRealizedHomotopyGrid
      endpoint leftTerminal rightTerminal N) :
    (grid.rowChain 0).state N = endpoint.terminalState x := by
  have hstate :=
    reachableChain_state_commonPredecessor_eq_terminalState
      endpoint leftTerminal N grid.left_terminalIndex_le
      grid.leftBoundaryChain
  simpa only [leftBoundaryChain, transportReachableChain_state] using hstate

/-- The right predecessor identity is likewise derived from the right
reachable boundary chain. -/
theorem right_predecessor
    (grid : ReparameterizedRootedOverlapRealizedHomotopyGrid
      endpoint leftTerminal rightTerminal N) :
    (grid.rowChain (Fin.last (N + 2))).state N =
      endpoint.terminalState y := by
  have hstate :=
    reachableChain_state_commonPredecessor_eq_terminalState
      endpoint rightTerminal N grid.right_terminalIndex_le
      grid.rightBoundaryChain
  simpa only [rightBoundaryChain, transportReachableChain_state] using hstate

set_option linter.unusedVariables false in
/-- Every sampled point in or beyond the terminal column is the common
overlap endpoint, independently of the row. -/
theorem row_node_eq_overlap
    (grid : ReparameterizedRootedOverlapRealizedHomotopyGrid
      endpoint leftTerminal rightTerminal N)
    (m n : ℕ) (hn : N + 1 ≤ n) :
    reparameterizedOverlapGridRow
        endpoint leftTerminal rightTerminal N m n = z := by
  simp [reparameterizedOverlapGridRow, homotopyGridRow,
    commonUniformSubdivision_terminal N n hn]

set_option linter.unusedVariables false in
/-- The common root is the zeroth node of every row. -/
theorem root_anchor_eq_row_zero
    (grid : ReparameterizedRootedOverlapRealizedHomotopyGrid
      endpoint leftTerminal rightTerminal N)
    (m : ℕ) :
    endpoint.root.anchor =
      reparameterizedOverlapGridRow
        endpoint leftTerminal rightTerminal N m 0 := by
  simp [reparameterizedOverlapGridRow, homotopyGridRow,
    commonUniformSubdivision_zero]

/-- The extra successor in the constant overlap column is a zero successor,
so it does not change the reached state. -/
theorem row_terminal_tail_eq
    (grid : ReparameterizedRootedOverlapRealizedHomotopyGrid
      endpoint leftTerminal rightTerminal N)
    (m : Fin (N + 3)) :
    (grid.rowChain m).state (N + 2) =
      (grid.rowChain m).state (N + 1) := by
  have hstateAnchor :
      ((grid.rowChain m).state (N + 1)).anchor = z := by
    calc
      ((grid.rowChain m).state (N + 1)).anchor =
          reparameterizedOverlapGridRow
            endpoint leftTerminal rightTerminal N m (N + 1) :=
        (grid.rowChain m).state_anchor_eq_node
          (grid.root_anchor_eq_row_zero m) (N + 1)
      _ = z := grid.row_node_eq_overlap m (N + 1) le_rfl
  have hnextAtAnchor :
      reparameterizedOverlapGridRow
          endpoint leftTerminal rightTerminal N m (N + 2) =
        ((grid.rowChain m).state (N + 1)).anchor := by
    exact
      (grid.row_node_eq_overlap m (N + 2) (by omega)).trans
        hstateAnchor.symm
  have hvectorZero : ((grid.rowChain m).data (N + 1)).v = 0 :=
    DifferentialSuccessorZero.data_vector_eq_zero_of_anchor_eq
      ((grid.rowChain m).data (N + 1)) hnextAtAnchor
  calc
    (grid.rowChain m).state (N + 2) =
        ((grid.rowChain m).data (N + 1)).successor := by
      simpa only [Nat.add_assoc] using
        (grid.rowChain m).state_succ (N + 1)
    _ = (grid.rowChain m).state (N + 1) :=
      DifferentialSuccessorZero.successor_eq_of_vector_eq_zero
        ((grid.rowChain m).data (N + 1)) hvectorZero

set_option linter.unusedVariables false in
/-- The horizontal mesh condition for this exact realized reparameterized
grid. -/
def HorizontalSmall
    [CompactSpace M] [ConnectedSpace M]
    (grid : ReparameterizedRootedOverlapRealizedHomotopyGrid
      endpoint leftTerminal rightTerminal N)
    (eta : ℝ) : Prop :=
  letI : MetricSpace M := g.toMetricSpace
  ∀ m : Fin (N + 3), ∀ j : Fin (N + 2),
    dist
      (reparameterizedOverlapGridRow
        endpoint leftTerminal rightTerminal N m (j + 1))
      (reparameterizedOverlapGridRow
        endpoint leftTerminal rightTerminal N m j) < eta

set_option linter.unusedVariables false in
/-- The vertical mesh condition for this exact realized reparameterized
grid. -/
def VerticalSmall
    [CompactSpace M] [ConnectedSpace M]
    (grid : ReparameterizedRootedOverlapRealizedHomotopyGrid
      endpoint leftTerminal rightTerminal N)
    (eta : ℝ) : Prop :=
  letI : MetricSpace M := g.toMetricSpace
  ∀ m : Fin (N + 2), ∀ j : Fin (N + 2),
    dist
      (reparameterizedOverlapGridRow
        endpoint leftTerminal rightTerminal N (m + 1) (j + 1))
      (reparameterizedOverlapGridRow
        endpoint leftTerminal rightTerminal N m (j + 1)) < eta

/-- Constant curvature chooses a positive common radius for the already
realized reparameterized grid. -/
theorem exists_commonMeshRadius
    [CompactSpace M] [ConnectedSpace M]
    (grid : ReparameterizedRootedOverlapRealizedHomotopyGrid
      endpoint leftTerminal rightTerminal N)
    (hcurv : HasConstantSectionalCurvature3 g 1) :
    ∃ eta > (0 : ℝ),
      grid.HorizontalSmall eta → grid.VerticalSmall eta →
      (grid.rowChain 0).state (N + 2) =
        (grid.rowChain (Fin.last (N + 2))).state (N + 2) := by
  letI : MetricSpace M := g.toMetricSpace
  simpa only [HorizontalSmall, VerticalSmall] using
    (exists_common_mesh_radius_for_fixed_realized_homotopyGrid_of_curvature
      hcurv
      (reparameterizedOverlapHomotopy
        endpoint leftTerminal rightTerminal N)
      endpoint.root rfl (commonUniformSubdivision N)
      (commonUniformSubdivision_zero N) (N + 1)
      (commonUniformSubdivision_terminal N) grid.rowChain grid.rungData
      grid.bottomAtUpper grid.rungAtNext)

/-- The canonical positive radius supplied for this fixed grid. -/
noncomputable def commonMeshRadius
    [CompactSpace M] [ConnectedSpace M]
    (grid : ReparameterizedRootedOverlapRealizedHomotopyGrid
      endpoint leftTerminal rightTerminal N)
    (hcurv : HasConstantSectionalCurvature3 g 1) : ℝ :=
  Classical.choose (grid.exists_commonMeshRadius hcurv)

theorem commonMeshRadius_pos
    [CompactSpace M] [ConnectedSpace M]
    (grid : ReparameterizedRootedOverlapRealizedHomotopyGrid
      endpoint leftTerminal rightTerminal N)
    (hcurv : HasConstantSectionalCurvature3 g 1) :
    0 < grid.commonMeshRadius hcurv :=
  (Classical.choose_spec (grid.exists_commonMeshRadius hcurv)).1

/-- Smallness at the chosen radius identifies the two boundary-row states in
the final padded overlap column. -/
theorem boundary_terminal_eq_of_small
    [CompactSpace M] [ConnectedSpace M]
    (grid : ReparameterizedRootedOverlapRealizedHomotopyGrid
      endpoint leftTerminal rightTerminal N)
    (hcurv : HasConstantSectionalCurvature3 g 1)
    (hhorizontal : grid.HorizontalSmall (grid.commonMeshRadius hcurv))
    (hvertical : grid.VerticalSmall (grid.commonMeshRadius hcurv)) :
    (grid.rowChain 0).state (N + 2) =
      (grid.rowChain (Fin.last (N + 2))).state (N + 2) :=
  (Classical.choose_spec (grid.exists_commonMeshRadius hcurv)).2
    hhorizontal hvertical

/-- Convert a realized boundary equality into the concrete common-root
terminal transport.  Both predecessor fields of the result are filled by the
derived provenance theorems `left_predecessor` and `right_predecessor`. -/
def toCommonRootTerminalTransport_of_boundary_eq
    (grid : ReparameterizedRootedOverlapRealizedHomotopyGrid
      endpoint leftTerminal rightTerminal N)
    (hterminal :
      (grid.rowChain 0).state (N + 2) =
        (grid.rowChain (Fin.last (N + 2))).state (N + 2)) :
    CommonRootTerminalTransport
      (endpoint.terminalState x) (endpoint.terminalState y) z := by
  refine
    { root := endpoint.root
      leftNodes :=
        reparameterizedOverlapGridRow
          endpoint leftTerminal rightTerminal N 0
      rightNodes :=
        reparameterizedOverlapGridRow endpoint leftTerminal rightTerminal N
          (Fin.last (N + 2))
      leftChain := grid.rowChain 0
      rightChain := grid.rowChain (Fin.last (N + 2))
      leftIndex := N
      rightIndex := N
      left_predecessor := grid.left_predecessor
      right_predecessor := grid.right_predecessor
      left_next_node := grid.row_node_eq_overlap 0 (N + 1) le_rfl
      right_next_node :=
        grid.row_node_eq_overlap (Fin.last (N + 2)) (N + 1) le_rfl
      terminal_eq := ?_ }
  exact
    (grid.row_terminal_tail_eq 0).symm.trans
      (hterminal.trans
        (grid.row_terminal_tail_eq (Fin.last (N + 2))))

/-- The chosen common radius and its mesh bounds construct a genuine
common-root terminal transport with no stored predecessor identities. -/
noncomputable def toCommonRootTerminalTransport
    [CompactSpace M] [ConnectedSpace M]
    (grid : ReparameterizedRootedOverlapRealizedHomotopyGrid
      endpoint leftTerminal rightTerminal N)
    (hcurv : HasConstantSectionalCurvature3 g 1)
    (hhorizontal : grid.HorizontalSmall (grid.commonMeshRadius hcurv))
    (hvertical : grid.VerticalSmall (grid.commonMeshRadius hcurv)) :
    CommonRootTerminalTransport
      (endpoint.terminalState x) (endpoint.terminalState y) z :=
  grid.toCommonRootTerminalTransport_of_boundary_eq
    (grid.boundary_terminal_eq_of_small hcurv hhorizontal hvertical)

/-- The reparameterized realized-grid transport proves equality of the two
actual terminal Cartan germ values at the overlap point. -/
theorem germ_value_eq_of_small
    [CompactSpace M] [ConnectedSpace M]
    (grid : ReparameterizedRootedOverlapRealizedHomotopyGrid
      endpoint leftTerminal rightTerminal N)
    (hcurv : HasConstantSectionalCurvature3 g 1)
    (hhorizontal : grid.HorizontalSmall (grid.commonMeshRadius hcurv))
    (hvertical : grid.VerticalSmall (grid.commonMeshRadius hcurv)) :
    (endpoint.terminalState x).germ z =
      (endpoint.terminalState y).germ z :=
  germ_value_eq_of_commonRootTerminalTransport
    (endpoint.terminalState x) (endpoint.terminalState y) z
    (grid.toCommonRootTerminalTransport hcurv hhorizontal hvertical)

end ReparameterizedRootedOverlapRealizedHomotopyGrid
end CartanRootedOverlapReparameterizedHomotopyGrid
end Poincare
