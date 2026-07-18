import Poincare.Global.CartanCanonicalRootedReparameterizedUniformRadiusGridAssembly
import Poincare.Global.DifferentialHomotopyGridFiniteMaximaRefinement
import Poincare.Global.DifferentialSuccessorArbitraryFiniteGridUniformRadiusRealization
import Poincare.Global.DifferentialSuccessorStrictFactorCurvatureTransport

/-!
# Refined rooted-overlap grids from vanishing finite maxima

The canonical rooted grid previously fixed both the overlap homotopy and the
uniform subdivision before asking for half-radius smallness.  A genuinely
refining response changes the subdivision and therefore cannot inhabit that
old hard-coded grid type.

This file gives the missing geometric bridge.  The reparameterized overlap
homotopy stays fixed, but its subdivision is an arbitrary finite refinement
of the original common uniform subdivision.  Actual finite horizontal and
vertical maxima below half of the uniform successor radius construct all
differential row, rung, and cross-cell data via the arbitrary-grid realization
theorem.  A countable sequence of such refinements has both maxima tending to
zero.

The refinement factor is retained as exact boundary provenance: every old
grid node occurs literally at its factor index in the refined grid, and the
factor is strictly increasing through the old finite prefix.  What is not
proved here is Cartan-state transport along those insertions.  That remaining
step needs the state-dependent insertion equality radii, not more geometric
subdivision data.
-/

noncomputable section

open Metric Set
open scoped Manifold ContDiff Topology unitInterval

namespace Poincare
namespace CartanRootedOverlapRefinedGridFiniteMaximaBridge

set_option linter.unusedSectionVars false

open CartanAtlasRootedReachableEndpointTransport
open CartanCanonicalRootedEndpointAssembly
open CartanCanonicalRootedReparameterizedUniformRadiusGridAssembly
open CartanRootedOverlapReparameterizedBoundary
open CartanRootedOverlapReparameterizedBoundaryState
open CartanRootedOverlapReparameterizedHomotopyGrid
open DifferentialHomotopyGridFiniteMaximaRefinement
open DifferentialSuccessorAdjacentContinuation
open DifferentialSuccessorArbitraryFiniteGridUniformRadiusRealization
open DifferentialSuccessorFiniteInsertionRefinement
open DifferentialSuccessorStrictFactorCurvatureTransport
open DifferentialSuccessorStrictFactorInsertionTransport
open FiniteUnitIntervalInterpolation

universe u

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace E M]
variable [IsManifold I ∞ M]
variable [CompactSpace M] [ConnectedSpace M]

variable {g : ClosedSmoothRiemannianMetric 3 M}

/-! ## The original finite uniform subdivision -/

/-- The eventually stationary common uniform subdivision is monotone. -/
theorem commonUniformSubdivision_monotone (N : ℕ) :
    Monotone (commonUniformSubdivision N) := by
  intro a b hab
  by_cases ha : a ≤ N
  · by_cases hb : b ≤ N
    · unfold commonUniformSubdivision
      simp only [dif_pos ha, dif_pos hb]
      change (a : ℝ) / (N + 1 : ℕ) ≤ (b : ℝ) / (N + 1 : ℕ)
      gcongr
    · unfold commonUniformSubdivision
      simp only [dif_pos ha, dif_neg hb]
      exact (uniformNode (N + 1)
        (Fin.castSucc ⟨a, Nat.lt_succ_of_le ha⟩)).property.2
  · have hb : ¬ b ≤ N := fun h ↦ ha (hab.trans h)
    simp [commonUniformSubdivision, ha, hb]

/-- The original common uniform node family as the finite-subdivision object
consumed by the finite-maxima refinement theorem. -/
def commonUniformFiniteSubdivision (N : ℕ) :
    FiniteHomotopySubdivision where
  nodes := commonUniformSubdivision N
  terminalIndex := N + 1
  terminalIndex_pos := Nat.succ_pos N
  nodes_zero := commonUniformSubdivision_zero N
  nodes_monotone := commonUniformSubdivision_monotone N
  nodes_one := commonUniformSubdivision_terminal N

/-- Consecutive nodes in the nonstationary prefix of the common uniform
subdivision are strictly increasing. -/
theorem commonUniformFiniteSubdivision_strict
    (N n : ℕ) (hn : n < (commonUniformFiniteSubdivision N).terminalIndex) :
    (commonUniformFiniteSubdivision N).nodes n <
      (commonUniformFiniteSubdivision N).nodes (n + 1) := by
  have hnN : n ≤ N := by
    simpa [commonUniformFiniteSubdivision] using hn
  change commonUniformSubdivision N n < commonUniformSubdivision N (n + 1)
  unfold commonUniformSubdivision
  simp only [dif_pos hnN]
  by_cases hnext : n + 1 ≤ N
  · simp only [dif_pos hnext]
    change (n : ℝ) / (N + 1 : ℕ) <
      (n + 1 : ℕ) / (N + 1 : ℕ)
    have hdenom : (0 : ℝ) < (N + 1 : ℕ) := by positivity
    exact (div_lt_div_iff_of_pos_right hdenom).2 (by exact_mod_cast Nat.lt_succ_self n)
  · have hnEq : n = N := by omega
    subst n
    simp only [dif_neg (by omega : ¬N + 1 ≤ N)]
    change (N : ℝ) / (N + 1 : ℕ) < 1
    have hdenom : (0 : ℝ) < (N + 1 : ℕ) := by positivity
    rw [div_lt_one hdenom]
    exact_mod_cast Nat.lt_succ_self N

/-! ## A geometric refined-grid precertificate -/

/-- One refinement of the original common grid whose two actual finite edge
families are below half of the uniform generic successor radius.

The factor relation is geometric boundary provenance.  No reached-state
equality or post-realization curvature-radius inequality is stored here. -/
structure RefinedUniformRadiusGridPrecertificate
    [SimplyConnectedSpace M]
    (successor : UniformGenericSuccessorRadiusCertificate g)
    (endpoint : RootedPathContinuedEndpointFamily g)
    {x y z : M} {leftMesh rightMesh : ℝ}
    (leftTerminal : TerminalShortPathCertificate g x z leftMesh)
    (rightTerminal : TerminalShortPathCertificate g y z rightMesh)
    (N : ℕ) where
  left_terminalIndex_le : endpoint.terminalIndex x ≤ N
  right_terminalIndex_le : endpoint.terminalIndex y ≤ N
  subdivision : FiniteHomotopySubdivision
  refinesCommonUniform :
    subdivision.Refines (commonUniformFiniteSubdivision N)
  horizontalHalfRadius :
    DifferentialSuccessorArbitraryFiniteGridUniformRadiusRealization.HorizontalHalfRadiusSmall
      (g := g)
      (reparameterizedOverlapHomotopy endpoint leftTerminal rightTerminal N)
      subdivision.nodes subdivision.terminalIndex successor.radius
  verticalHalfRadius :
    DifferentialSuccessorArbitraryFiniteGridUniformRadiusRealization.VerticalHalfRadiusSmall
      (g := g)
      (reparameterizedOverlapHomotopy endpoint leftTerminal rightTerminal N)
      subdivision.nodes subdivision.terminalIndex successor.radius

namespace RefinedUniformRadiusGridPrecertificate

variable [SimplyConnectedSpace M]
variable {successor : UniformGenericSuccessorRadiusCertificate g}
variable {endpoint : RootedPathContinuedEndpointFamily g}
variable {x y z : M} {leftMesh rightMesh : ℝ}
variable {leftTerminal : TerminalShortPathCertificate g x z leftMesh}
variable {rightTerminal : TerminalShortPathCertificate g y z rightMesh}
variable {N : ℕ}

/-- The complete arbitrary-subdivision differential grid computed from the
geometric precertificate. -/
noncomputable def grid
    (precertificate : RefinedUniformRadiusGridPrecertificate successor endpoint
      leftTerminal rightTerminal N) :
    RealizedHomotopyGrid
      (reparameterizedOverlapHomotopy endpoint leftTerminal rightTerminal N)
      endpoint.root precertificate.subdivision.nodes
      precertificate.subdivision.terminalIndex :=
  realizedGrid_of_uniformSuccessorRadius
    (reparameterizedOverlapHomotopy endpoint leftTerminal rightTerminal N)
    endpoint.root rfl precertificate.subdivision.nodes
    precertificate.subdivision.terminalIndex
    precertificate.subdivision.nodes_zero
    precertificate.subdivision.nodes_one successor.radius successor.radius_pos
    successor.data precertificate.horizontalHalfRadius
    precertificate.verticalHalfRadius

/-- Build a geometric precertificate directly from strict bounds on the two
actual finite maxima of a refining subdivision. -/
def ofFiniteMaxima
    (hleft : endpoint.terminalIndex x ≤ N)
    (hright : endpoint.terminalIndex y ≤ N)
    (subdivision : FiniteHomotopySubdivision)
    (hrefines : subdivision.Refines (commonUniformFiniteSubdivision N))
    (hhorizontal : letI : MetricSpace M := g.toMetricSpace
      subdivision.horizontalMaximum
        (reparameterizedOverlapHomotopy endpoint leftTerminal rightTerminal N) <
          successor.radius / 2)
    (hvertical : letI : MetricSpace M := g.toMetricSpace
      subdivision.verticalMaximum
        (reparameterizedOverlapHomotopy endpoint leftTerminal rightTerminal N) <
          successor.radius / 2) :
    RefinedUniformRadiusGridPrecertificate successor endpoint
      leftTerminal rightTerminal N where
  left_terminalIndex_le := hleft
  right_terminalIndex_le := hright
  subdivision := subdivision
  refinesCommonUniform := hrefines
  horizontalHalfRadius := by
    letI : MetricSpace M := g.toMetricSpace
    rw [FiniteHomotopySubdivision.horizontalMaximum_lt_iff] at hhorizontal
    intro m j
    exact hhorizontal (m, j)
  verticalHalfRadius := by
    letI : MetricSpace M := g.toMetricSpace
    rw [FiniteHomotopySubdivision.verticalMaximum_lt_iff] at hvertical
    intro m j
    exact hvertical (m, j)

/-- A canonical factor map witnessing that every original uniform node is
retained in the refined subdivision. -/
noncomputable def factor
    (precertificate : RefinedUniformRadiusGridPrecertificate successor endpoint
      leftTerminal rightTerminal N) : ℕ → ℕ :=
  Classical.choose precertificate.refinesCommonUniform

theorem factor_monotone
    (precertificate : RefinedUniformRadiusGridPrecertificate successor endpoint
      leftTerminal rightTerminal N) :
    Monotone precertificate.factor :=
  (Classical.choose_spec precertificate.refinesCommonUniform).1

@[simp]
theorem factor_zero
    (precertificate : RefinedUniformRadiusGridPrecertificate successor endpoint
      leftTerminal rightTerminal N) :
    precertificate.factor 0 = 0 :=
  (Classical.choose_spec precertificate.refinesCommonUniform).2.1

theorem factor_le_terminalIndex
    (precertificate : RefinedUniformRadiusGridPrecertificate successor endpoint
      leftTerminal rightTerminal N) (n : ℕ) :
    precertificate.factor n ≤ precertificate.subdivision.terminalIndex :=
  (Classical.choose_spec precertificate.refinesCommonUniform).2.2.1 n

theorem subdivision_nodes_factor
    (precertificate : RefinedUniformRadiusGridPrecertificate successor endpoint
      leftTerminal rightTerminal N) (n : ℕ) :
    precertificate.subdivision.nodes (precertificate.factor n) =
      commonUniformSubdivision N n := by
  exact (Classical.choose_spec
    precertificate.refinesCommonUniform).2.2.2 n

/-- The refinement factor is genuinely strict throughout the original
nonstationary prefix; this is derived, not stored. -/
theorem factor_strict
    (precertificate : RefinedUniformRadiusGridPrecertificate successor endpoint
      leftTerminal rightTerminal N) (n : ℕ) (hn : n < N + 1) :
    precertificate.factor n < precertificate.factor (n + 1) := by
  have hle := precertificate.factor_monotone (Nat.le_succ n)
  apply lt_of_le_of_ne hle
  intro heq
  have hnodes := congrArg precertificate.subdivision.nodes heq
  rw [precertificate.subdivision_nodes_factor n,
    precertificate.subdivision_nodes_factor (n + 1)] at hnodes
  exact (ne_of_lt (commonUniformFiniteSubdivision_strict N n (by
    simpa [commonUniformFiniteSubdivision] using hn))) hnodes

/-- Exact two-dimensional grid provenance: every old common-grid node occurs
at the pair of retained factor indices in the refined grid. -/
theorem refinedGridNode_at_factor
    (precertificate : RefinedUniformRadiusGridPrecertificate successor endpoint
      leftTerminal rightTerminal N) (m n : ℕ) :
    homotopyGridRow
        (reparameterizedOverlapHomotopy endpoint leftTerminal rightTerminal N)
        precertificate.subdivision.nodes (precertificate.factor m)
        (precertificate.factor n) =
      reparameterizedOverlapGridRow endpoint leftTerminal rightTerminal N m n := by
  simp only [homotopyGridRow, reparameterizedOverlapGridRow]
  rw [precertificate.subdivision_nodes_factor m,
    precertificate.subdivision_nodes_factor n]

/-- The retained zeroth row is exactly the old reparameterized left boundary
at every retained column. -/
theorem refinedLeftBoundaryNode_at_factor
    (precertificate : RefinedUniformRadiusGridPrecertificate successor endpoint
      leftTerminal rightTerminal N) (n : ℕ) :
    homotopyGridRow
        (reparameterizedOverlapHomotopy endpoint leftTerminal rightTerminal N)
        precertificate.subdivision.nodes 0 (precertificate.factor n) =
      reparameterizedBoundaryNodes endpoint leftTerminal N n := by
  calc
    _ = homotopyGridRow
          (reparameterizedOverlapHomotopy endpoint leftTerminal rightTerminal N)
          precertificate.subdivision.nodes (precertificate.factor 0)
          (precertificate.factor n) := by rw [precertificate.factor_zero]
    _ = reparameterizedOverlapGridRow endpoint leftTerminal rightTerminal N 0 n :=
      precertificate.refinedGridNode_at_factor 0 n
    _ = reparameterizedBoundaryNodes endpoint leftTerminal N n := congrFun
      (reparameterizedOverlapGridRow_zero endpoint leftTerminal rightTerminal N) n

/-! ## Factor-index state transport on the two rooted boundary rows -/

/-- The refined node sequence on an arbitrary retained homotopy row. -/
def refinedRowNodes
    (precertificate : RefinedUniformRadiusGridPrecertificate successor endpoint
      leftTerminal rightTerminal N) (m : ℕ) : ℕ → M :=
  homotopyGridRow
    (reparameterizedOverlapHomotopy endpoint leftTerminal rightTerminal N)
    precertificate.subdivision.nodes (precertificate.factor m)

/-- Every retained row index lies in the actual finite realized grid. -/
def refinedRowIndex
    (precertificate : RefinedUniformRadiusGridPrecertificate successor endpoint
      leftTerminal rightTerminal N) (m : ℕ) :
    Fin (precertificate.subdivision.terminalIndex + 2) :=
  ⟨precertificate.factor m, by
    have hle := precertificate.factor_le_terminalIndex m
    omega⟩

/-- The actual recursively realized chain on one retained refined row. -/
noncomputable def refinedRowChain
    (precertificate : RefinedUniformRadiusGridPrecertificate successor endpoint
      leftTerminal rightTerminal N) (m : ℕ) :
    DifferentialInducedSuccessor.Chain.ReachableChain
      (precertificate.refinedRowNodes m) endpoint.root :=
  (precertificate.grid).rowChain (precertificate.refinedRowIndex m)

/-- Through the original left endpoint's terminal index, the retained refined
left-boundary nodes are exactly the nodes of its rooted endpoint chain. -/
theorem refinedLeftBoundaryNode_factor_eq_endpointNode
    (precertificate : RefinedUniformRadiusGridPrecertificate successor endpoint
      leftTerminal rightTerminal N)
    (n : ℕ) (hn : n ≤ endpoint.terminalIndex x) :
    precertificate.refinedRowNodes 0 (precertificate.factor n) =
      endpoint.nodes x n := by
  calc
    _ = homotopyGridRow
          (reparameterizedOverlapHomotopy endpoint leftTerminal rightTerminal N)
          precertificate.subdivision.nodes 0 (precertificate.factor n) := by
      rw [refinedRowNodes, precertificate.factor_zero]
    _ = reparameterizedBoundaryNodes endpoint leftTerminal N n :=
      precertificate.refinedLeftBoundaryNode_at_factor n
    _ = endpoint.nodes x n :=
      reparameterizedBoundaryNodes_eq_endpoint_nodes endpoint leftTerminal N n
        precertificate.left_terminalIndex_le hn

/-- The retained row corresponding to the old final homotopy row is exactly
the rooted right boundary at every retained column. -/
theorem refinedRightBoundaryNode_at_factor
    (precertificate : RefinedUniformRadiusGridPrecertificate successor endpoint
      leftTerminal rightTerminal N) (n : ℕ) :
    precertificate.refinedRowNodes (N + 2) (precertificate.factor n) =
      reparameterizedBoundaryNodes endpoint rightTerminal N n := by
  calc
    _ = reparameterizedOverlapGridRow endpoint leftTerminal rightTerminal N
          (N + 2) n :=
      precertificate.refinedGridNode_at_factor (N + 2) n
    _ = reparameterizedBoundaryNodes endpoint rightTerminal N n := by
      exact congrFun
        (reparameterizedOverlapGridRow_last endpoint leftTerminal rightTerminal N) n

/-- Through the original right endpoint's terminal index, the retained
refined right-boundary nodes are exactly its rooted endpoint-chain nodes. -/
theorem refinedRightBoundaryNode_factor_eq_endpointNode
    (precertificate : RefinedUniformRadiusGridPrecertificate successor endpoint
      leftTerminal rightTerminal N)
    (n : ℕ) (hn : n ≤ endpoint.terminalIndex y) :
    precertificate.refinedRowNodes (N + 2) (precertificate.factor n) =
      endpoint.nodes y n := by
  calc
    _ = reparameterizedBoundaryNodes endpoint rightTerminal N n :=
      precertificate.refinedRightBoundaryNode_at_factor n
    _ = endpoint.nodes y n :=
      reparameterizedBoundaryNodes_eq_endpoint_nodes endpoint rightTerminal N n
        precertificate.right_terminalIndex_le hn

/-- Actual equality across every insertion block transports the original left
terminal Cartan state to its retained factor index in the realized refined
left row.  The hypotheses are local insertion-history equalities, not the
homotopy-grid endpoint conclusion. -/
theorem leftTerminalState_eq_refined_factor_of_gapTerminalEq
    (precertificate : RefinedUniformRadiusGridPrecertificate successor endpoint
      leftTerminal rightTerminal N)
    (insertionChain : ∀ n i : ℕ,
      DifferentialInducedSuccessor.Chain.ReachableChain
        (insertNodeListSchedule
          (factorRefinementStage (endpoint.nodes x)
            (precertificate.refinedRowNodes 0) precertificate.factor n)
          (precertificate.factor n)
          (factorGapNodes (precertificate.refinedRowNodes 0)
            precertificate.factor n) i) endpoint.root)
    (hgap : ∀ n < endpoint.terminalIndex x,
      (insertionChain n 0).state
          (endpoint.terminalIndex x + (precertificate.factor n - n)) =
        (insertionChain n
          (factorGapNodes (precertificate.refinedRowNodes 0)
            precertificate.factor n).length).state
          (endpoint.terminalIndex x + (precertificate.factor n - n) +
            (factorGapNodes (precertificate.refinedRowNodes 0)
              precertificate.factor n).length)) :
    endpoint.terminalState x =
      (precertificate.refinedRowChain 0).state
        (precertificate.factor (endpoint.terminalIndex x)) := by
  have htransport :=
    DifferentialSuccessorStrictFactorCurvatureTransport.ReachableChain.state_eq_of_strict_factor_of_gap_terminal_eq
      (endpoint.nodes x) (precertificate.refinedRowNodes 0)
      (endpoint.terminalIndex x) precertificate.factor
      precertificate.factor_zero
      (fun n hn ↦ precertificate.factor_strict n (by
        have hterminal := precertificate.left_terminalIndex_le
        omega))
      (fun n hn ↦
        precertificate.refinedLeftBoundaryNode_factor_eq_endpointNode n hn)
      (endpoint.chain x) (precertificate.refinedRowChain 0)
      insertionChain hgap
  simpa [RootedPathContinuedEndpointFamily.terminalState] using htransport

/-- The analogous insertion-block transport for the original right terminal
state and the retained refined right row. -/
theorem rightTerminalState_eq_refined_factor_of_gapTerminalEq
    (precertificate : RefinedUniformRadiusGridPrecertificate successor endpoint
      leftTerminal rightTerminal N)
    (insertionChain : ∀ n i : ℕ,
      DifferentialInducedSuccessor.Chain.ReachableChain
        (insertNodeListSchedule
          (factorRefinementStage (endpoint.nodes y)
            (precertificate.refinedRowNodes (N + 2)) precertificate.factor n)
          (precertificate.factor n)
          (factorGapNodes (precertificate.refinedRowNodes (N + 2))
            precertificate.factor n) i) endpoint.root)
    (hgap : ∀ n < endpoint.terminalIndex y,
      (insertionChain n 0).state
          (endpoint.terminalIndex y + (precertificate.factor n - n)) =
        (insertionChain n
          (factorGapNodes (precertificate.refinedRowNodes (N + 2))
            precertificate.factor n).length).state
          (endpoint.terminalIndex y + (precertificate.factor n - n) +
            (factorGapNodes (precertificate.refinedRowNodes (N + 2))
              precertificate.factor n).length)) :
    endpoint.terminalState y =
      (precertificate.refinedRowChain (N + 2)).state
        (precertificate.factor (endpoint.terminalIndex y)) := by
  have htransport :=
    DifferentialSuccessorStrictFactorCurvatureTransport.ReachableChain.state_eq_of_strict_factor_of_gap_terminal_eq
      (endpoint.nodes y) (precertificate.refinedRowNodes (N + 2))
      (endpoint.terminalIndex y) precertificate.factor
      precertificate.factor_zero
      (fun n hn ↦ precertificate.factor_strict n (by
        have hterminal := precertificate.right_terminalIndex_le
        omega))
      (fun n hn ↦
        precertificate.refinedRightBoundaryNode_factor_eq_endpointNode n hn)
      (endpoint.chain y) (precertificate.refinedRowChain (N + 2))
      insertionChain hgap
  simpa [RootedPathContinuedEndpointFamily.terminalState] using htransport

/-- Constant curvature attaches the exact two-stage positive radius
certificate whose validated insertion inequalities imply the left
factor-index state equality above.  The radii are selected only from the
actual insertion histories. -/
theorem leftBoundary_strictFactorRadiusCertificate_of_curvature
    (hcurv : HasConstantSectionalCurvature3 g 1)
    (precertificate : RefinedUniformRadiusGridPrecertificate successor endpoint
      leftTerminal rightTerminal N)
    (insertionChain : ∀ n i : ℕ,
      DifferentialInducedSuccessor.Chain.ReachableChain
        (insertNodeListSchedule
          (factorRefinementStage (endpoint.nodes x)
            (precertificate.refinedRowNodes 0) precertificate.factor n)
          (precertificate.factor n)
          (factorGapNodes (precertificate.refinedRowNodes 0)
            precertificate.factor n) i) endpoint.root) :
    letI : MetricSpace M := g.toMetricSpace
    StrictFactorRadiusCertificate
      (endpoint.nodes x) (precertificate.refinedRowNodes 0) endpoint.root
      (endpoint.terminalIndex x) precertificate.factor (endpoint.chain x)
      (precertificate.refinedRowChain 0) insertionChain := by
  letI : MetricSpace M := g.toMetricSpace
  apply DifferentialSuccessorStrictFactorCurvatureTransport.ReachableChain.strictFactorRadiusCertificate_of_curvature
    hcurv (endpoint.nodes x) (precertificate.refinedRowNodes 0)
      (endpoint.terminalIndex x) precertificate.factor
      precertificate.factor_zero
  · intro n hn
    apply precertificate.factor_strict n
    have hterminal := precertificate.left_terminalIndex_le
    omega
  · intro n hn
    exact precertificate.refinedLeftBoundaryNode_factor_eq_endpointNode n hn

/-- Constant curvature supplies the corresponding two-stage insertion-radius
certificate on the retained right boundary. -/
theorem rightBoundary_strictFactorRadiusCertificate_of_curvature
    (hcurv : HasConstantSectionalCurvature3 g 1)
    (precertificate : RefinedUniformRadiusGridPrecertificate successor endpoint
      leftTerminal rightTerminal N)
    (insertionChain : ∀ n i : ℕ,
      DifferentialInducedSuccessor.Chain.ReachableChain
        (insertNodeListSchedule
          (factorRefinementStage (endpoint.nodes y)
            (precertificate.refinedRowNodes (N + 2)) precertificate.factor n)
          (precertificate.factor n)
          (factorGapNodes (precertificate.refinedRowNodes (N + 2))
            precertificate.factor n) i) endpoint.root) :
    letI : MetricSpace M := g.toMetricSpace
    StrictFactorRadiusCertificate
      (endpoint.nodes y) (precertificate.refinedRowNodes (N + 2)) endpoint.root
      (endpoint.terminalIndex y) precertificate.factor (endpoint.chain y)
      (precertificate.refinedRowChain (N + 2)) insertionChain := by
  letI : MetricSpace M := g.toMetricSpace
  apply DifferentialSuccessorStrictFactorCurvatureTransport.ReachableChain.strictFactorRadiusCertificate_of_curvature
    hcurv (endpoint.nodes y) (precertificate.refinedRowNodes (N + 2))
      (endpoint.terminalIndex y) precertificate.factor
      precertificate.factor_zero
  · intro n hn
    apply precertificate.factor_strict n
    have hterminal := precertificate.right_terminalIndex_le
    omega
  · intro n hn
    exact precertificate.refinedRightBoundaryNode_factor_eq_endpointNode n hn

/-! ## Finite-maxima existence and vanishing sequence -/

/-- The finite-maxima refinement theorem supplies a genuine half-radius
precertificate refining the old common uniform grid. -/
theorem nonempty_of_finiteMaxima_refinement
    (successor : UniformGenericSuccessorRadiusCertificate g)
    (endpoint : RootedPathContinuedEndpointFamily g)
    {x y z : M} {leftMesh rightMesh : ℝ}
    (leftTerminal : TerminalShortPathCertificate g x z leftMesh)
    (rightTerminal : TerminalShortPathCertificate g y z rightMesh)
    (N : ℕ)
    (hleft : endpoint.terminalIndex x ≤ N)
    (hright : endpoint.terminalIndex y ≤ N) :
    Nonempty (RefinedUniformRadiusGridPrecertificate successor endpoint
      leftTerminal rightTerminal N) := by
  letI : MetricSpace M := g.toMetricSpace
  rcases exists_refinement_horizontalMaximum_verticalMaximum_lt
      g (reparameterizedOverlapHomotopy endpoint leftTerminal rightTerminal N)
      (commonUniformFiniteSubdivision N) (half_pos successor.radius_pos) with
    ⟨subdivision, hrefines, hhorizontal, hvertical⟩
  exact ⟨ofFiniteMaxima hleft hright subdivision hrefines
    hhorizontal hvertical⟩

/-- There is a sequence of seed-refining half-radius precertificates whose
two actual finite maxima tend to zero. -/
theorem exists_sequence_finiteMaxima_vanish
    (successor : UniformGenericSuccessorRadiusCertificate g)
    (endpoint : RootedPathContinuedEndpointFamily g)
    {x y z : M} {leftMesh rightMesh : ℝ}
    (leftTerminal : TerminalShortPathCertificate g x z leftMesh)
    (rightTerminal : TerminalShortPathCertificate g y z rightMesh)
    (N : ℕ)
    (hleft : endpoint.terminalIndex x ≤ N)
    (hright : endpoint.terminalIndex y ≤ N) :
    letI : MetricSpace M := g.toMetricSpace
    ∃ stage : ℕ → RefinedUniformRadiusGridPrecertificate successor endpoint
        leftTerminal rightTerminal N,
      ∀ delta > (0 : ℝ), ∃ stageIndex, ∀ n ≥ stageIndex,
        (stage n).subdivision.horizontalMaximum
            (reparameterizedOverlapHomotopy endpoint leftTerminal
              rightTerminal N) < delta ∧
          (stage n).subdivision.verticalMaximum
            (reparameterizedOverlapHomotopy endpoint leftTerminal
              rightTerminal N) < delta := by
  letI : MetricSpace M := g.toMetricSpace
  let F := reparameterizedOverlapHomotopy endpoint leftTerminal rightTerminal N
  have hstageExists : ∀ n : ℕ,
      ∃ subdivision : FiniteHomotopySubdivision,
        subdivision.Refines (commonUniformFiniteSubdivision N) ∧
          subdivision.horizontalMaximum F <
            min (successor.radius / 2) (1 / ((n : ℝ) + 1)) ∧
          subdivision.verticalMaximum F <
            min (successor.radius / 2) (1 / ((n : ℝ) + 1)) := by
    intro n
    exact exists_refinement_horizontalMaximum_verticalMaximum_lt g F
      (commonUniformFiniteSubdivision N)
      (lt_min (half_pos successor.radius_pos)
        (Nat.one_div_pos_of_nat (n := n) (α := ℝ)))
  choose subdivision hsubdivision using hstageExists
  let stage : ℕ → RefinedUniformRadiusGridPrecertificate successor endpoint
      leftTerminal rightTerminal N := fun n ↦
    ofFiniteMaxima hleft hright (subdivision n) (hsubdivision n).1
      ((hsubdivision n).2.1.trans_le (min_le_left _ _))
      ((hsubdivision n).2.2.trans_le (min_le_left _ _))
  refine ⟨stage, ?_⟩
  intro delta hdelta
  rcases exists_nat_one_div_lt hdelta with ⟨stageIndex, hstageIndex⟩
  refine ⟨stageIndex, ?_⟩
  intro n hn
  have hthreshold :
      1 / ((n : ℝ) + 1) ≤ 1 / ((stageIndex : ℝ) + 1) :=
    Nat.one_div_le_one_div hn
  have hhorizontal :=
    (((hsubdivision n).2.1.trans_le (min_le_right _ _)).trans_le
      hthreshold).trans hstageIndex
  have hvertical :=
    (((hsubdivision n).2.2.trans_le (min_le_right _ _)).trans_le
      hthreshold).trans hstageIndex
  simpa [stage, F, ofFiniteMaxima] using And.intro hhorizontal hvertical

end RefinedUniformRadiusGridPrecertificate

end CartanRootedOverlapRefinedGridFiniteMaximaBridge
end Poincare
