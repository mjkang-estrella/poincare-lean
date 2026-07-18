import Poincare.Global.CartanCanonicalFamilyComparedWholeCellRealization
import Poincare.Global.CartanTerminalShortPathDiameter
import Poincare.Global.CartanRootedOverlapHomotopyGrid
import Poincare.Global.CartanRootedOverlapReparameterizedBoundary
import Poincare.Global.DifferentialSuccessorReachableChainRefinement

/-!
# Direct rooted-overlap boundary subdivisions

The earlier reparameterized boundary uses polynomial interpolation through
retained nodes; that interpolation need not be monotone between nodes.  For
strict-factor geometry it is better to sample the direct concatenated path at
the actual rooted node times embedded in its first half, followed by the
terminal endpoint at time `1`.  The resulting finite subdivision is monotone,
and is strict whenever the retained rooted subdivision is strict.
-/

noncomputable section

open Metric Set
open scoped Manifold ContDiff Topology unitInterval

namespace Poincare
namespace CartanRootedOverlapDirectBoundarySubdivision

set_option linter.unusedSectionVars false

open CartanAtlasRootedReachableEndpointTransport
open CartanCanonicalRootedEndpointAssembly
open CartanRootedOverlapHomotopyGrid
open CartanRootedOverlapReparameterizedBoundary
open CartanTerminalShortPathDiameter
open DifferentialInducedSuccessor.Chain
open DifferentialSuccessorReachableChainRefinement

universe u

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace E M]
variable [IsManifold I ∞ M]

variable {g : ClosedSmoothRiemannianMetric 3 M}

/-- Double a parameter known to lie in the first half of the unit interval. -/
def firstHalfParameter (t : unitInterval) (ht : (t : ℝ) ≤ 1 / 2) :
    unitInterval :=
  ⟨2 * t, (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨t.2.1, ht⟩⟩

@[simp]
theorem coe_firstHalfParameter (t : unitInterval)
    (ht : (t : ℝ) ≤ 1 / 2) :
    (firstHalfParameter t ht : ℝ) = 2 * t :=
  rfl

/-- Translate and double a parameter known to lie in the second half. -/
def secondHalfParameter (t : unitInterval) (ht : (1 / 2 : ℝ) ≤ t) :
    unitInterval :=
  ⟨2 * t - 1,
    unitInterval.two_mul_sub_one_mem_iff.2 ⟨ht, t.2.2⟩⟩

@[simp]
theorem coe_secondHalfParameter (t : unitInterval)
    (ht : (1 / 2 : ℝ) ≤ t) :
    (secondHalfParameter t ht : ℝ) = 2 * t - 1 :=
  rfl

/-- On the first half, the concatenated path is the rooted path evaluated at
the doubled parameter. -/
theorem rootToOverlapPath_apply_of_le_half
    (endpoint : RootedPathContinuedEndpointFamily g)
    {x z : M} {mesh : ℝ}
    (terminal : TerminalShortPathCertificate g x z mesh)
    (t : unitInterval) (ht : (t : ℝ) ≤ 1 / 2) :
    rootToOverlapPath endpoint terminal t =
      endpoint.path x (firstHalfParameter t ht) := by
  rw [rootToOverlapPath, Path.trans_apply, dif_pos ht]
  rfl

/-- On the closed second half, including the gluing time, the concatenated
path is the terminal curve evaluated at the translated doubled parameter. -/
theorem rootToOverlapPath_apply_of_half_le
    (endpoint : RootedPathContinuedEndpointFamily g)
    {x z : M} {mesh : ℝ}
    (terminal : TerminalShortPathCertificate g x z mesh)
    (t : unitInterval) (ht : (1 / 2 : ℝ) ≤ t) :
    rootToOverlapPath endpoint terminal t =
      terminal.curve (secondHalfParameter t ht) := by
  rw [rootToOverlapPath, Path.trans_apply]
  by_cases hle : (t : ℝ) ≤ 1 / 2
  · rw [dif_pos hle]
    have htval : (t : ℝ) = 1 / 2 := le_antisymm hle ht
    have hfirst :
        (⟨2 * (t : ℝ),
          (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨t.2.1, hle⟩⟩ :
            unitInterval) = 1 := by
      apply Subtype.ext
      simp [htval]
    have hsecond : secondHalfParameter t ht = 0 := by
      apply Subtype.ext
      simp [secondHalfParameter, htval]
    rw [hfirst, (endpoint.path x).target, hsecond]
    simpa using terminal.curve_zero.symm
  · rw [dif_neg hle]
    rfl

/-- The rooted node times in the first half of the concatenated path, then
the terminal overlap endpoint at time `1`. -/
def directBoundarySubdivision
    (endpoint : RootedPathContinuedEndpointFamily g) (x : M) : ℕ → unitInterval :=
  fun n ↦
    if n ≤ endpoint.terminalIndex x then
      halfTime (endpoint.nodeTime x n)
    else
      1

@[simp]
theorem directBoundarySubdivision_zero
    (endpoint : RootedPathContinuedEndpointFamily g) (x : M) :
    directBoundarySubdivision endpoint x 0 = 0 := by
  rw [directBoundarySubdivision, if_pos (Nat.zero_le _),
    endpoint.nodeTime_zero]
  apply Subtype.ext
  norm_num [halfTime]

theorem directBoundarySubdivision_monotone
    (endpoint : RootedPathContinuedEndpointFamily g) (x : M)
    (hmono : Monotone (endpoint.nodeTime x)) :
    Monotone (directBoundarySubdivision endpoint x) := by
  apply monotone_nat_of_le_succ
  intro n
  change
    (if n ≤ endpoint.terminalIndex x then
      halfTime (endpoint.nodeTime x n) else 1) ≤
    (if n + 1 ≤ endpoint.terminalIndex x then
      halfTime (endpoint.nodeTime x (n + 1)) else 1)
  by_cases hn : n < endpoint.terminalIndex x
  · rw [if_pos (Nat.le_of_lt hn), if_pos (Nat.succ_le_iff.2 hn)]
    change (endpoint.nodeTime x n : ℝ) / 2 ≤
      (endpoint.nodeTime x (n + 1) : ℝ) / 2
    exact div_le_div_of_nonneg_right
      (Subtype.coe_le_coe.2 (hmono (Nat.le_succ n))) (by norm_num)
  · by_cases heq : n = endpoint.terminalIndex x
    · subst n
      rw [if_pos le_rfl, if_neg (by omega), endpoint.nodeTime_terminal]
      exact (halfTime (1 : unitInterval)).property.2
    · have hlarge : endpoint.terminalIndex x < n := by omega
      rw [if_neg (by omega), if_neg (by omega)]

@[simp]
theorem directBoundarySubdivision_terminal
    (endpoint : RootedPathContinuedEndpointFamily g) (x : M)
    (n : ℕ) (hn : endpoint.terminalIndex x + 1 ≤ n) :
    directBoundarySubdivision endpoint x n = 1 := by
  rw [directBoundarySubdivision, if_neg (by omega)]

theorem directBoundarySubdivision_strict
    (endpoint : RootedPathContinuedEndpointFamily g) (x : M)
    (hstrict : ∀ n < endpoint.terminalIndex x,
      endpoint.nodeTime x n < endpoint.nodeTime x (n + 1)) :
    ∀ n < endpoint.terminalIndex x + 1,
      directBoundarySubdivision endpoint x n <
        directBoundarySubdivision endpoint x (n + 1) := by
  intro n hn
  change
    (if n ≤ endpoint.terminalIndex x then
      halfTime (endpoint.nodeTime x n) else 1) <
    (if n + 1 ≤ endpoint.terminalIndex x then
      halfTime (endpoint.nodeTime x (n + 1)) else 1)
  by_cases hbefore : n < endpoint.terminalIndex x
  · rw [if_pos (Nat.le_of_lt hbefore),
      if_pos (Nat.succ_le_iff.2 hbefore)]
    change (endpoint.nodeTime x n : ℝ) / 2 <
      (endpoint.nodeTime x (n + 1) : ℝ) / 2
    exact div_lt_div_of_pos_right
      (Subtype.coe_lt_coe.2 (hstrict n hbefore)) (by norm_num)
  · have heq : n = endpoint.terminalIndex x := by omega
    subst n
    rw [if_pos le_rfl, if_neg (by omega), endpoint.nodeTime_terminal]
    change ((1 : ℝ) / 2) < 1
    norm_num

/-- The direct boundary node sequence on one root-to-overlap path. -/
def directBoundaryNodes
    (endpoint : RootedPathContinuedEndpointFamily g)
    {x z : M} {mesh : ℝ}
    (terminal : TerminalShortPathCertificate g x z mesh) : ℕ → M :=
  fun n ↦ rootToOverlapPath endpoint terminal
    (directBoundarySubdivision endpoint x n)

/-- Through the retained terminal index, direct boundary nodes are exactly
the original endpoint realization nodes. -/
theorem directBoundaryNodes_eq_endpoint_nodes
    (endpoint : RootedPathContinuedEndpointFamily g)
    {x z : M} {mesh : ℝ}
    (terminal : TerminalShortPathCertificate g x z mesh)
    (n : ℕ) (hn : n ≤ endpoint.terminalIndex x) :
    directBoundaryNodes endpoint terminal n = endpoint.nodes x n := by
  rw [directBoundaryNodes, directBoundarySubdivision, if_pos hn,
    rootToOverlapPath_apply_halfTime]
  rfl

@[simp]
theorem directBoundaryNodes_zero
    (endpoint : RootedPathContinuedEndpointFamily g)
    {x z : M} {mesh : ℝ}
    (terminal : TerminalShortPathCertificate g x z mesh) :
    directBoundaryNodes endpoint terminal 0 = endpoint.root.anchor := by
  simp [directBoundaryNodes, directBoundarySubdivision_zero,
    rootToOverlapPath]

@[simp]
theorem directBoundaryNodes_terminal
    (endpoint : RootedPathContinuedEndpointFamily g)
    {x z : M} {mesh : ℝ}
    (terminal : TerminalShortPathCertificate g x z mesh)
    (n : ℕ) (hn : endpoint.terminalIndex x + 1 ≤ n) :
    directBoundaryNodes endpoint terminal n = z := by
  rw [directBoundaryNodes, directBoundarySubdivision_terminal endpoint x n hn]
  exact (rootToOverlapPath endpoint terminal).target

/-- Every direct-boundary parameter cell has path-image diameter below the
same mesh, provided the rooted cells have that diameter and the terminal
curve has certified total length below the mesh.  The gluing cell is handled
entirely by the terminal-curve diameter theorem. -/
theorem directBoundarySubdivision_cellDiameter
    [CompactSpace M] [ConnectedSpace M]
    (endpoint : RootedPathContinuedEndpointFamily g)
    {x z : M} {mesh : ℝ}
    (terminal : TerminalShortPathCertificate g x z mesh)
    (hrootCell :
      letI : MetricSpace M := g.toMetricSpace
      ∀ (n : ℕ) (a b : unitInterval),
        a ∈ Icc (endpoint.nodeTime x n) (endpoint.nodeTime x (n + 1)) →
        b ∈ Icc (endpoint.nodeTime x n) (endpoint.nodeTime x (n + 1)) →
        dist (endpoint.path x a) (endpoint.path x b) < mesh)
    (n : ℕ) (a b : unitInterval)
    (ha : a ∈ Icc (directBoundarySubdivision endpoint x n)
      (directBoundarySubdivision endpoint x (n + 1)))
    (hb : b ∈ Icc (directBoundarySubdivision endpoint x n)
      (directBoundarySubdivision endpoint x (n + 1))) :
    letI : MetricSpace M := g.toMetricSpace
    dist (rootToOverlapPath endpoint terminal a)
      (rootToOverlapPath endpoint terminal b) < mesh := by
  letI : MetricSpace M := g.toMetricSpace
  by_cases hn : n < endpoint.terminalIndex x
  · have hnleft : n ≤ endpoint.terminalIndex x := Nat.le_of_lt hn
    have hnright : n + 1 ≤ endpoint.terminalIndex x :=
      Nat.succ_le_iff.2 hn
    have hleft : directBoundarySubdivision endpoint x n =
        halfTime (endpoint.nodeTime x n) := by
      rw [directBoundarySubdivision, if_pos hnleft]
    have hright : directBoundarySubdivision endpoint x (n + 1) =
        halfTime (endpoint.nodeTime x (n + 1)) := by
      rw [directBoundarySubdivision, if_pos hnright]
    rw [hleft, hright] at ha hb
    have haHalf : (a : ℝ) ≤ 1 / 2 :=
      (Subtype.coe_le_coe.2 ha.2).trans
        (halfTime_le_half (endpoint.nodeTime x (n + 1)))
    have hbHalf : (b : ℝ) ≤ 1 / 2 :=
      (Subtype.coe_le_coe.2 hb.2).trans
        (halfTime_le_half (endpoint.nodeTime x (n + 1)))
    have haCell : firstHalfParameter a haHalf ∈
        Icc (endpoint.nodeTime x n) (endpoint.nodeTime x (n + 1)) := by
      constructor
      · apply Subtype.coe_le_coe.1
        have h := Subtype.coe_le_coe.2 ha.1
        simp only [coe_halfTime, coe_firstHalfParameter] at h ⊢
        linarith
      · apply Subtype.coe_le_coe.1
        have h := Subtype.coe_le_coe.2 ha.2
        simp only [coe_halfTime, coe_firstHalfParameter] at h ⊢
        linarith
    have hbCell : firstHalfParameter b hbHalf ∈
        Icc (endpoint.nodeTime x n) (endpoint.nodeTime x (n + 1)) := by
      constructor
      · apply Subtype.coe_le_coe.1
        have h := Subtype.coe_le_coe.2 hb.1
        simp only [coe_halfTime, coe_firstHalfParameter] at h ⊢
        linarith
      · apply Subtype.coe_le_coe.1
        have h := Subtype.coe_le_coe.2 hb.2
        simp only [coe_halfTime, coe_firstHalfParameter] at h ⊢
        linarith
    rw [rootToOverlapPath_apply_of_le_half endpoint terminal a haHalf,
      rootToOverlapPath_apply_of_le_half endpoint terminal b hbHalf]
    exact hrootCell n _ _ haCell hbCell
  · by_cases heq : n = endpoint.terminalIndex x
    · subst n
      have hleft :
          directBoundarySubdivision endpoint x (endpoint.terminalIndex x) =
            halfTime 1 := by
        rw [directBoundarySubdivision, if_pos le_rfl,
          endpoint.nodeTime_terminal]
      have hright :
          directBoundarySubdivision endpoint x
              (endpoint.terminalIndex x + 1) = 1 :=
        directBoundarySubdivision_terminal endpoint x _ le_rfl
      rw [hleft, hright] at ha hb
      have haHalf : (1 / 2 : ℝ) ≤ a := by
        have h := Subtype.coe_le_coe.2 ha.1
        simpa [halfTime] using h
      have hbHalf : (1 / 2 : ℝ) ≤ b := by
        have h := Subtype.coe_le_coe.2 hb.1
        simpa [halfTime] using h
      rw [rootToOverlapPath_apply_of_half_le endpoint terminal a haHalf,
        rootToOverlapPath_apply_of_half_le endpoint terminal b hbHalf]
      exact CartanTerminalShortPathDiameter.TerminalShortPathCertificate.dist_curve_lt_mesh
        terminal
        (secondHalfParameter a haHalf).property
        (secondHalfParameter b hbHalf).property
    · have hnlarge : endpoint.terminalIndex x < n := by omega
      have hleft := directBoundarySubdivision_terminal endpoint x n (by omega)
      have hright := directBoundarySubdivision_terminal endpoint x (n + 1)
        (by omega)
      rw [hleft, hright] at ha hb
      have haone : a = 1 := le_antisymm ha.2 ha.1
      have hbone : b = 1 := le_antisymm hb.2 hb.1
      subst a
      subst b
      simpa using
        CartanTerminalShortPathDiameter.TerminalShortPathCertificate.dist_curve_lt_mesh
        terminal
        (a := (0 : ℝ)) (b := (0 : ℝ)) (by norm_num) (by norm_num)

/-- Any realized chain on the direct boundary reaches the fixed endpoint
terminal state at the retained predecessor index. -/
theorem reachableChain_state_predecessor_eq_terminalState
    (endpoint : RootedPathContinuedEndpointFamily g)
    {x z : M} {mesh : ℝ}
    (terminal : TerminalShortPathCertificate g x z mesh)
    (chain : ReachableChain (directBoundaryNodes endpoint terminal)
      endpoint.root) :
    chain.state (endpoint.terminalIndex x) = endpoint.terminalState x := by
  change chain.state (endpoint.terminalIndex x) =
    (endpoint.chain x).state (endpoint.terminalIndex x)
  apply ReachableChain.state_eq_of_prefix_nodes
  intro j hj
  exact directBoundaryNodes_eq_endpoint_nodes endpoint terminal (j + 1)
    (Nat.succ_le_of_lt hj)

end CartanRootedOverlapDirectBoundarySubdivision
end Poincare
