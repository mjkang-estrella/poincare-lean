import Poincare.Global.CartanRootedOverlapHomotopyGrid
import Poincare.Global.FiniteUnitIntervalInterpolation

/-!
# Reparameterized rooted-overlap boundary paths

The two rooted endpoint chains generally use unrelated node-time sequences.
This file puts each concatenated root-to-overlap path on the same uniform
index grid without identifying those original times.  A projected Lagrange
interpolant sends the common uniform nodes to the appropriate half-times of
each endpoint path, pads after the retained terminal index, and sends the
last node to the overlap endpoint.

The resulting left and right paths therefore admit a simple-connectivity
homotopy with a genuinely shared column subdivision.  The evaluation lemmas
below are proposition-level boundary provenance; no strict-factor schedule
or equality between the two original subdivisions is assumed.
-/

noncomputable section

open Set
open scoped Manifold ContDiff Topology unitInterval

namespace Poincare
namespace CartanRootedOverlapReparameterizedBoundary

set_option linter.unusedSectionVars false

open CartanAtlasRootedReachableEndpointTransport
open CartanCanonicalRootedEndpointAssembly
open CartanRootedOverlapHomotopyGrid
open FiniteUnitIntervalInterpolation

universe u

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace E M]
variable [IsManifold I ∞ M]

variable {g : ClosedSmoothRiemannianMetric 3 M}

/-- Embed a unit-interval time into the first half of a concatenated path. -/
def halfTime (t : unitInterval) : unitInterval :=
  ⟨(t : ℝ) / 2,
    unitInterval.div_mem t.2.1 (by norm_num)
      (t.2.2.trans (by norm_num))⟩

@[simp]
theorem coe_halfTime (t : unitInterval) : (halfTime t : ℝ) = (t : ℝ) / 2 :=
  rfl

theorem halfTime_le_half (t : unitInterval) :
    (halfTime t : ℝ) ≤ 1 / 2 := by
  dsimp [halfTime]
  linarith [t.2.2]

/-- The original first path is recovered at every embedded half-time. -/
@[simp]
theorem rootToOverlapPath_apply_halfTime
    (endpoint : RootedPathContinuedEndpointFamily g)
    {x z : M} {mesh : ℝ}
    (terminal : TerminalShortPathCertificate g x z mesh)
    (t : unitInterval) :
    rootToOverlapPath endpoint terminal (halfTime t) = endpoint.path x t := by
  rw [rootToOverlapPath, Path.trans_apply]
  split_ifs with h
  · congr 1
    apply Subtype.ext
    change 2 * ((t : ℝ) / 2) = (t : ℝ)
    ring
  · exact False.elim (h (halfTime_le_half t))

/-- Nodal times for one endpoint boundary on a common grid of `N + 1`
pieces.  Nodes `0, ..., N` sample the original endpoint path (stationary
after its retained terminal index); node `N + 1` samples the overlap point. -/
def boundaryNodalTime
    (endpoint : RootedPathContinuedEndpointFamily g)
    (x : M) (N : ℕ) (j : Fin (N + 2)) : unitInterval :=
  if j.val ≤ N then
    halfTime (endpoint.nodeTime x (min j.val (endpoint.terminalIndex x)))
  else
    1

@[simp]
theorem boundaryNodalTime_zero
    (endpoint : RootedPathContinuedEndpointFamily g) (x : M) (N : ℕ) :
    boundaryNodalTime endpoint x N 0 = 0 := by
  simp [boundaryNodalTime, halfTime, endpoint.nodeTime_zero x]

@[simp]
theorem boundaryNodalTime_last
    (endpoint : RootedPathContinuedEndpointFamily g) (x : M) (N : ℕ) :
    boundaryNodalTime endpoint x N (Fin.last (N + 1)) = 1 := by
  simp [boundaryNodalTime]

/-- The continuous endpoint-preserving reparameterization selected from the
finite nodal data. -/
def boundaryReparameterization
    (endpoint : RootedPathContinuedEndpointFamily g)
    (x : M) (N : ℕ) : unitInterval → unitInterval :=
  interpolation (N + 1) (boundaryNodalTime endpoint x N)

theorem continuous_boundaryReparameterization
    (endpoint : RootedPathContinuedEndpointFamily g) (x : M) (N : ℕ) :
    Continuous (boundaryReparameterization endpoint x N) :=
  continuous_interpolation (N + 1) (boundaryNodalTime endpoint x N)

@[simp]
theorem boundaryReparameterization_zero
    (endpoint : RootedPathContinuedEndpointFamily g) (x : M) (N : ℕ) :
    boundaryReparameterization endpoint x N 0 = 0 :=
  interpolation_zero (Nat.succ_pos N)
    (boundaryNodalTime endpoint x N) (boundaryNodalTime_zero endpoint x N)

@[simp]
theorem boundaryReparameterization_one
    (endpoint : RootedPathContinuedEndpointFamily g) (x : M) (N : ℕ) :
    boundaryReparameterization endpoint x N 1 = 1 :=
  interpolation_one (Nat.succ_pos N)
    (boundaryNodalTime endpoint x N) (boundaryNodalTime_last endpoint x N)

/-- The root-to-overlap path whose common uniform nodes reproduce one
endpoint chain and then its overlap endpoint. -/
def reparameterizedRootToOverlapPath
    (endpoint : RootedPathContinuedEndpointFamily g)
    {x z : M} {mesh : ℝ}
    (terminal : TerminalShortPathCertificate g x z mesh)
    (N : ℕ) : Path endpoint.root.anchor z :=
  (rootToOverlapPath endpoint terminal).reparam
    (boundaryReparameterization endpoint x N)
    (continuous_boundaryReparameterization endpoint x N)
    (boundaryReparameterization_zero endpoint x N)
    (boundaryReparameterization_one endpoint x N)

/-- Evaluation of the reparameterized path at any common uniform node. -/
theorem reparameterizedRootToOverlapPath_apply_uniformNode
    (endpoint : RootedPathContinuedEndpointFamily g)
    {x z : M} {mesh : ℝ}
    (terminal : TerminalShortPathCertificate g x z mesh)
    (N : ℕ) (j : Fin (N + 2)) :
    reparameterizedRootToOverlapPath endpoint terminal N
        (uniformNode (N + 1) j) =
      rootToOverlapPath endpoint terminal (boundaryNodalTime endpoint x N j) := by
  change
    rootToOverlapPath endpoint terminal
        (boundaryReparameterization endpoint x N (uniformNode (N + 1) j)) = _
  rw [boundaryReparameterization, interpolation_uniformNode (Nat.succ_pos N)]

/-- Every nonfinal common node samples the corresponding original endpoint
node, padded at the retained terminal index. -/
theorem reparameterizedRootToOverlapPath_apply_uniformNode_castSucc
    (endpoint : RootedPathContinuedEndpointFamily g)
    {x z : M} {mesh : ℝ}
    (terminal : TerminalShortPathCertificate g x z mesh)
    (N : ℕ) (j : Fin (N + 1)) :
    reparameterizedRootToOverlapPath endpoint terminal N
        (uniformNode (N + 1) j.castSucc) =
      endpoint.nodes x (min j.val (endpoint.terminalIndex x)) := by
  rw [reparameterizedRootToOverlapPath_apply_uniformNode]
  have hj : j.val ≤ N := Nat.le_of_lt_succ j.isLt
  rw [boundaryNodalTime, if_pos (by simpa using hj)]
  exact rootToOverlapPath_apply_halfTime endpoint terminal _

/-- Before the retained terminal index, the common boundary reproduces the
original endpoint node at the same index. -/
theorem reparameterizedRootToOverlapPath_apply_originalNode
    (endpoint : RootedPathContinuedEndpointFamily g)
    {x z : M} {mesh : ℝ}
    (terminal : TerminalShortPathCertificate g x z mesh)
    (N : ℕ) (j : Fin (N + 1))
    (hj : j.val ≤ endpoint.terminalIndex x) :
    reparameterizedRootToOverlapPath endpoint terminal N
        (uniformNode (N + 1) j.castSucc) = endpoint.nodes x j.val := by
  rw [reparameterizedRootToOverlapPath_apply_uniformNode_castSucc,
    Nat.min_eq_left hj]

/-- At and after the retained terminal index, the common boundary is
stationary at the endpoint anchor. -/
theorem reparameterizedRootToOverlapPath_apply_paddedNode
    (endpoint : RootedPathContinuedEndpointFamily g)
    {x z : M} {mesh : ℝ}
    (terminal : TerminalShortPathCertificate g x z mesh)
    (N : ℕ) (j : Fin (N + 1))
    (hj : endpoint.terminalIndex x ≤ j.val) :
    reparameterizedRootToOverlapPath endpoint terminal N
        (uniformNode (N + 1) j.castSucc) = x := by
  rw [reparameterizedRootToOverlapPath_apply_uniformNode_castSucc,
    Nat.min_eq_right hj]
  simp [RootedPathContinuedEndpointFamily.nodes,
    endpoint.nodeTime_terminal x]

/-- The last common boundary node is the overlap endpoint. -/
theorem reparameterizedRootToOverlapPath_apply_last
    (endpoint : RootedPathContinuedEndpointFamily g)
    {x z : M} {mesh : ℝ}
    (terminal : TerminalShortPathCertificate g x z mesh)
    (N : ℕ) :
    reparameterizedRootToOverlapPath endpoint terminal N
        (uniformNode (N + 1) (Fin.last (N + 1))) = z := by
  rw [reparameterizedRootToOverlapPath_apply_uniformNode,
    boundaryNodalTime_last]
  exact (rootToOverlapPath endpoint terminal).target

/-- Simple connectivity compares the two independently reparameterized
root-to-overlap paths on their common uniform boundary grid. -/
noncomputable def reparameterizedOverlapHomotopy
    [SimplyConnectedSpace M]
    (endpoint : RootedPathContinuedEndpointFamily g)
    {x y z : M} {leftMesh rightMesh : ℝ}
    (leftTerminal : TerminalShortPathCertificate g x z leftMesh)
    (rightTerminal : TerminalShortPathCertificate g y z rightMesh)
    (N : ℕ) :
    (reparameterizedRootToOverlapPath endpoint leftTerminal N).Homotopy
      (reparameterizedRootToOverlapPath endpoint rightTerminal N) :=
  Classical.choice
    (SimplyConnectedSpace.paths_homotopic
      (reparameterizedRootToOverlapPath endpoint leftTerminal N)
      (reparameterizedRootToOverlapPath endpoint rightTerminal N))

end CartanRootedOverlapReparameterizedBoundary
end Poincare
