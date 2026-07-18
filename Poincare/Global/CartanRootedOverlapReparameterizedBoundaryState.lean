import Poincare.Global.CartanRootedOverlapReparameterizedBoundary
import Poincare.Global.DifferentialSuccessorReachableChainRefinement
import Poincare.Global.DifferentialSuccessorZero

/-!
# State provenance on reparameterized rooted-overlap boundaries

The reparameterized boundary path has `N + 1` uniform pieces.  Its first
`N + 1` nodes reproduce one rooted endpoint chain, padded by the endpoint
after the retained terminal index; the final node and every later sample are
the overlap point.  This file turns that path-level statement into a
state-level one.

In particular, any realized differential chain on the common boundary reaches
the original endpoint terminal state at the common predecessor column `N`.
The proof first uses prefix canonicity at the original terminal index, then
removes every stationary padded successor by the zero-vector theorem.
-/

noncomputable section

open Set
open scoped Manifold ContDiff Topology unitInterval

namespace Poincare
namespace CartanRootedOverlapReparameterizedBoundaryState

set_option linter.unusedSectionVars false

open CartanAtlasRootedReachableEndpointTransport
open CartanCanonicalRootedEndpointAssembly
open CartanRootedOverlapReparameterizedBoundary
open DifferentialInducedSuccessor
open DifferentialInducedSuccessor.Chain
open DifferentialSuccessorReachableChainRefinement
open FiniteUnitIntervalInterpolation

universe u

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace E M]
variable [IsManifold I ∞ M]

variable {g : ClosedSmoothRiemannianMetric 3 M}

/-- The common uniform subdivision, extended constantly by `1` after its
final path parameter.  Indices `0, ..., N` are the nonfinal uniform nodes;
index `N + 1` and every later index are the terminal parameter. -/
def commonUniformSubdivision (N : ℕ) (n : ℕ) : unitInterval :=
  if h : n ≤ N then
    uniformNode (N + 1)
      (Fin.castSucc (⟨n, Nat.lt_succ_of_le h⟩ : Fin (N + 1)))
  else
    1

@[simp]
theorem commonUniformSubdivision_zero (N : ℕ) :
    commonUniformSubdivision N 0 = 0 := by
  simp [commonUniformSubdivision]

theorem commonUniformSubdivision_eq_uniformNode_castSucc
    (N : ℕ) (j : Fin (N + 1)) :
    commonUniformSubdivision N j.val =
      uniformNode (N + 1) j.castSucc := by
  rw [commonUniformSubdivision, dif_pos (Nat.le_of_lt_succ j.isLt)]

@[simp]
theorem commonUniformSubdivision_terminal
    (N n : ℕ) (hn : N + 1 ≤ n) :
    commonUniformSubdivision N n = 1 := by
  rw [commonUniformSubdivision, dif_neg]
  omega

/-- The eventually constant node sequence sampled from one reparameterized
root-to-overlap boundary path. -/
def reparameterizedBoundaryNodes
    (endpoint : RootedPathContinuedEndpointFamily g)
    {x z : M} {mesh : ℝ}
    (terminal : TerminalShortPathCertificate g x z mesh)
    (N : ℕ) : ℕ → M :=
  fun n ↦
    reparameterizedRootToOverlapPath endpoint terminal N
      (commonUniformSubdivision N n)

@[simp]
theorem reparameterizedBoundaryNodes_zero
    (endpoint : RootedPathContinuedEndpointFamily g)
    {x z : M} {mesh : ℝ}
    (terminal : TerminalShortPathCertificate g x z mesh)
    (N : ℕ) :
    reparameterizedBoundaryNodes endpoint terminal N 0 =
      endpoint.root.anchor := by
  simp [reparameterizedBoundaryNodes]

/-- Through the retained terminal index, the common boundary has exactly the
same nodes as the original rooted endpoint chain. -/
theorem reparameterizedBoundaryNodes_eq_endpoint_nodes
    (endpoint : RootedPathContinuedEndpointFamily g)
    {x z : M} {mesh : ℝ}
    (terminal : TerminalShortPathCertificate g x z mesh)
    (N n : ℕ)
    (hterminalN : endpoint.terminalIndex x ≤ N)
    (hn : n ≤ endpoint.terminalIndex x) :
    reparameterizedBoundaryNodes endpoint terminal N n =
      endpoint.nodes x n := by
  let j : Fin (N + 1) :=
    ⟨n, Nat.lt_succ_of_le (hn.trans hterminalN)⟩
  rw [reparameterizedBoundaryNodes,
    commonUniformSubdivision_eq_uniformNode_castSucc N j]
  simpa [j] using
    (reparameterizedRootToOverlapPath_apply_originalNode
      endpoint terminal N j hn)

/-- From the retained terminal index through the common predecessor column
`N`, the boundary node sequence is stationary at `x`. -/
theorem reparameterizedBoundaryNodes_eq_endpoint_of_padding
    (endpoint : RootedPathContinuedEndpointFamily g)
    {x z : M} {mesh : ℝ}
    (terminal : TerminalShortPathCertificate g x z mesh)
    (N n : ℕ)
    (hterminal : endpoint.terminalIndex x ≤ n)
    (hn : n ≤ N) :
    reparameterizedBoundaryNodes endpoint terminal N n = x := by
  let j : Fin (N + 1) := ⟨n, Nat.lt_succ_of_le hn⟩
  rw [reparameterizedBoundaryNodes,
    commonUniformSubdivision_eq_uniformNode_castSucc N j]
  simpa [j] using
    (reparameterizedRootToOverlapPath_apply_paddedNode
      endpoint terminal N j hterminal)

/-- The final common node and all later nodes are the overlap endpoint. -/
theorem reparameterizedBoundaryNodes_terminal
    (endpoint : RootedPathContinuedEndpointFamily g)
    {x z : M} {mesh : ℝ}
    (terminal : TerminalShortPathCertificate g x z mesh)
    (N n : ℕ) (hn : N + 1 ≤ n) :
    reparameterizedBoundaryNodes endpoint terminal N n = z := by
  rw [reparameterizedBoundaryNodes,
    commonUniformSubdivision_terminal N n hn]
  exact (reparameterizedRootToOverlapPath endpoint terminal N).target

/-- A realized chain on the reparameterized boundary reaches the original
rooted endpoint terminal state at the common predecessor column `N`.

Prefix canonicity identifies the state at the original terminal index.  Each
subsequent boundary node is the same endpoint anchor, so its differential
datum has zero vector and its successor leaves the state unchanged. -/
theorem reachableChain_state_commonPredecessor_eq_terminalState
    (endpoint : RootedPathContinuedEndpointFamily g)
    {x z : M} {mesh : ℝ}
    (terminal : TerminalShortPathCertificate g x z mesh)
    (N : ℕ)
    (hterminalN : endpoint.terminalIndex x ≤ N)
    (chain : ReachableChain
      (reparameterizedBoundaryNodes endpoint terminal N) endpoint.root) :
    chain.state N = endpoint.terminalState x := by
  let K := endpoint.terminalIndex x
  have hstateK : chain.state K = endpoint.terminalState x := by
    change chain.state K = (endpoint.chain x).state K
    apply ReachableChain.state_eq_of_prefix_nodes
    intro j hj
    exact
      reparameterizedBoundaryNodes_eq_endpoint_nodes
        endpoint terminal N (j + 1) hterminalN (Nat.succ_le_of_lt hj)
  have hstate_add : ∀ r : ℕ, K + r ≤ N →
      chain.state (K + r) = endpoint.terminalState x := by
    intro r
    induction r with
    | zero =>
        intro _
        simpa using hstateK
    | succ r ih =>
        intro hKrN
        have hprevN : K + r ≤ N := by omega
        have hprev : chain.state (K + r) = endpoint.terminalState x :=
          ih hprevN
        have hnode :
            reparameterizedBoundaryNodes endpoint terminal N
                (K + r + 1) = x := by
          apply reparameterizedBoundaryNodes_eq_endpoint_of_padding
          · dsimp [K]
            omega
          · omega
        have hanchor : (chain.state (K + r)).anchor = x := by
          rw [hprev]
          exact endpoint.terminalState_anchor x
        have hvectorZero : (chain.data (K + r)).v = 0 :=
          DifferentialSuccessorZero.data_vector_eq_zero_of_anchor_eq
            (chain.data (K + r)) (hnode.trans hanchor.symm)
        calc
          chain.state (K + Nat.succ r) = chain.state (K + r + 1) := by
            rfl
          _ = (chain.data (K + r)).successor :=
            chain.state_succ (K + r)
          _ = chain.state (K + r) :=
            DifferentialSuccessorZero.successor_eq_of_vector_eq_zero
              (chain.data (K + r)) hvectorZero
          _ = endpoint.terminalState x := hprev
  have hKN : K ≤ N := hterminalN
  have hfinal := hstate_add (N - K) (by omega)
  simpa [Nat.add_sub_of_le hKN] using hfinal

end CartanRootedOverlapReparameterizedBoundaryState
end Poincare
