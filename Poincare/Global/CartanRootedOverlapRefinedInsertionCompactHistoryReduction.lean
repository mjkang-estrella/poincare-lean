import Poincare.Global.CartanRootedOverlapRefinedGridFiniteMaximaBridge
import Poincare.Global.DifferentialSuccessorAdaptiveFeedbackIteration

/-!
# Compact-history closure for actual refined boundary insertions

The finite-maxima bridge constructs arbitrarily fine realized homotopy grids,
but geometric grid edges do not control the two state-dependent defects in a
left-to-right strict-factor insertion schedule.  In particular, one of the
two displayed defects can still span the unsplit remainder of an old coarse
edge.  This file therefore keeps the missing feedback honest.

One stage contains actual reachable chains on the two coarse
reparameterized boundaries and on every intermediate single-node insertion
history.  Its first and second insertion defects are maxima of the exact
finite distance families occurring in the two
`StrictFactorCommonRadiusCertificate`s.  The second combined defect also
contains the actual horizontal and vertical finite grid maxima.  Constant
curvature chooses the two dependent insertion radii and the post-realization
grid radius only after those histories have been realized.

A compact-history package parameterizes the resulting active threshold by a
positive lower-semicontinuous function on one compact set and separately
assumes vanishing of the measured insertion defects and of the actual grid
maxima.  The existing adaptive-feedback theorem then selects a validated
stage.  At that stage, strict-factor transport reaches the retained terminal
column on both boundary rows, while the arbitrary-grid common-radius theorem
identifies the two realized rows.  The conclusion is a concrete
`CommonRootTerminalTransport`, and hence equality of the two carried Cartan
germ values.  No terminal equality, certificate inequality, or overlap
coherence conclusion is stored in the feedback data.
-/

noncomputable section

open Metric Set
open scoped Manifold ContDiff Topology unitInterval

namespace Poincare
namespace CartanRootedOverlapRefinedInsertionCompactHistoryReduction

set_option linter.unusedSectionVars false

open CartanAtlasRealizedEndpointTransport
open CartanAtlasRootedReachableEndpointTransport
open CartanCanonicalRootedEndpointAssembly
open CartanCanonicalRootedReparameterizedUniformRadiusGridAssembly
open CartanRootedOverlapReparameterizedBoundary
open CartanRootedOverlapReparameterizedBoundaryState
open CartanRootedOverlapRefinedGridFiniteMaximaBridge
open DifferentialHomotopyGridFiniteMaximaRefinement
open DifferentialInducedSuccessor
open DifferentialInducedSuccessor.Chain
open DifferentialSuccessorAdjacentContinuation
open DifferentialSuccessorAdaptiveFeedbackIteration
open DifferentialSuccessorArbitraryFiniteGridUniformRadiusRealization
open DifferentialSuccessorFiniteInsertionRefinement
open DifferentialSuccessorReachableChainRefinement
open DifferentialSuccessorStrictFactorInsertionTransport

universe u v

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

/-! ## Finite maxima for possibly empty realized-history families -/

/-- The supremum of a finite real family, with value zero when the index type
is empty.  Strict-factor schedules can genuinely have no inserted nodes, so
the empty case must not be hidden behind an artificial nonemptiness field. -/
noncomputable def finiteSupOrZero {A : Type v} [Fintype A]
    (f : A → ℝ) : ℝ := by
  classical
  exact
    if h : Nonempty A then
      letI : Nonempty A := h
      Finset.univ.sup' Finset.univ_nonempty f
    else
      0

/-- Below a positive threshold, `finiteSupOrZero` is exactly pointwise
smallness of the underlying finite family. -/
theorem finiteSupOrZero_lt_iff {A : Type v} [Fintype A]
    (f : A → ℝ) {eta : ℝ} (heta : 0 < eta) :
    finiteSupOrZero f < eta ↔ ∀ a, f a < eta := by
  classical
  cases isEmpty_or_nonempty A with
  | inl hEmpty =>
      letI : IsEmpty A := hEmpty
      have hnot : ¬Nonempty A := not_nonempty_iff.mpr hEmpty
      constructor
      · intro _h a
        exact isEmptyElim a
      · intro _h
        rw [finiteSupOrZero, dif_neg hnot]
        exact heta
  | inr hNonempty =>
      letI : Nonempty A := hNonempty
      rw [finiteSupOrZero, dif_pos hNonempty, Finset.sup'_lt_iff]
      constructor
      · intro h a
        exact h a (Finset.mem_univ a)
      · intro h a _ha
        exact h a

section GenericStrictFactorDefects

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace E M] [IsManifold I ∞ M]
variable [CompactSpace M] [ConnectedSpace M]

/-- The first distance tested at one exact realized insertion history. -/
def strictFactorFirstDistance
    {g : ClosedSmoothRiemannianMetric 3 M}
    (seed refined : ℕ → M) {initial : CartanChain.ChainState g}
    (k : ℕ) (e : ℕ → ℕ)
    (chain : ∀ n i : ℕ,
      ReachableChain
        (insertNodeListSchedule
          (factorRefinementStage seed refined e n) (e n)
          (factorGapNodes refined e n) i) initial)
    (a : StrictFactorRealizedHistoryIndex refined k e) : ℝ :=
  letI : MetricSpace M := g.toMetricSpace
  dist
    (insertNodeListSchedule
      (factorRefinementStage seed refined e a.1) (e a.1)
      (factorGapNodes refined e a.1) (a.2 + 1)
      (e a.1 + a.2 + 1))
    ((chain a.1 (a.2 + 1)).state (e a.1 + a.2)).anchor

/-- The second distance tested at one exact realized insertion history. -/
def strictFactorSecondDistance
    {g : ClosedSmoothRiemannianMetric 3 M}
    (seed refined : ℕ → M) {initial : CartanChain.ChainState g}
    (k : ℕ) (e : ℕ → ℕ)
    (_chain : ∀ n i : ℕ,
      ReachableChain
        (insertNodeListSchedule
          (factorRefinementStage seed refined e n) (e n)
          (factorGapNodes refined e n) i) initial)
    (a : StrictFactorRealizedHistoryIndex refined k e) : ℝ :=
  letI : MetricSpace M := g.toMetricSpace
  dist
    (insertNodeListSchedule
      (factorRefinementStage seed refined e a.1) (e a.1)
      (factorGapNodes refined e a.1) a.2
      (e a.1 + a.2 + 1))
    (insertNodeListSchedule
      (factorRefinementStage seed refined e a.1) (e a.1)
      (factorGapNodes refined e a.1) (a.2 + 1)
      (e a.1 + a.2 + 1))

/-- The maximum first insertion defect on one strict-factor realization. -/
def strictFactorFirstDefect
    {g : ClosedSmoothRiemannianMetric 3 M}
    (seed refined : ℕ → M) {initial : CartanChain.ChainState g}
    (k : ℕ) (e : ℕ → ℕ)
    (chain : ∀ n i : ℕ,
      ReachableChain
        (insertNodeListSchedule
          (factorRefinementStage seed refined e n) (e n)
          (factorGapNodes refined e n) i) initial) : ℝ :=
  finiteSupOrZero (strictFactorFirstDistance seed refined k e chain)

/-- The maximum second insertion defect on one strict-factor realization. -/
def strictFactorSecondDefect
    {g : ClosedSmoothRiemannianMetric 3 M}
    (seed refined : ℕ → M) {initial : CartanChain.ChainState g}
    (k : ℕ) (e : ℕ → ℕ)
    (chain : ∀ n i : ℕ,
      ReachableChain
        (insertNodeListSchedule
          (factorRefinementStage seed refined e n) (e n)
          (factorGapNodes refined e n) i) initial) : ℝ :=
  finiteSupOrZero (strictFactorSecondDistance seed refined k e chain)

theorem strictFactorFirstDefect_lt_iff
    {g : ClosedSmoothRiemannianMetric 3 M}
    (seed refined : ℕ → M) {initial : CartanChain.ChainState g}
    (k : ℕ) (e : ℕ → ℕ)
    (chain : ∀ n i : ℕ,
      ReachableChain
        (insertNodeListSchedule
          (factorRefinementStage seed refined e n) (e n)
          (factorGapNodes refined e n) i) initial)
    {eta : ℝ} (heta : 0 < eta) :
    strictFactorFirstDefect seed refined k e chain < eta ↔
      ∀ a : StrictFactorRealizedHistoryIndex refined k e,
        strictFactorFirstDistance seed refined k e chain a < eta := by
  exact finiteSupOrZero_lt_iff _ heta

theorem strictFactorSecondDefect_lt_iff
    {g : ClosedSmoothRiemannianMetric 3 M}
    (seed refined : ℕ → M) {initial : CartanChain.ChainState g}
    (k : ℕ) (e : ℕ → ℕ)
    (chain : ∀ n i : ℕ,
      ReachableChain
        (insertNodeListSchedule
          (factorRefinementStage seed refined e n) (e n)
          (factorGapNodes refined e n) i) initial)
    {eta : ℝ} (heta : 0 < eta) :
    strictFactorSecondDefect seed refined k e chain < eta ↔
      ∀ a : StrictFactorRealizedHistoryIndex refined k e,
        strictFactorSecondDistance seed refined k e chain a < eta := by
  exact finiteSupOrZero_lt_iff _ heta

end GenericStrictFactorDefects

/-! ## A zero-successor lemma for retained terminal columns -/

section StationaryReachableChain

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace E M] [IsManifold I ∞ M]

/-- Once a realized node sequence is stationary, its reached state is
stationary as well.  This uses the actual data on the chain and the
zero-vector theorem; it does not replace the data by a new policy. -/
theorem ReachableChain.state_eq_of_nodes_stationary_from
    {g : ClosedSmoothRiemannianMetric 3 M}
    {nodes : ℕ → M} {initial : CartanChain.ChainState g}
    (chain : ReachableChain nodes initial)
    (hinitial : initial.anchor = nodes 0)
    (a q : ℕ) (haq : a ≤ q)
    (hstationary : ∀ n, a ≤ n → nodes n = nodes a) :
    chain.state q = chain.state a := by
  have hind : ∀ r : ℕ, chain.state (a + r) = chain.state a := by
    intro r
    induction r with
    | zero => simp
    | succ r ih =>
        have hnextAtAnchor :
            nodes (a + r + 1) = (chain.state (a + r)).anchor := by
          calc
            nodes (a + r + 1) = nodes a :=
              hstationary (a + r + 1) (by omega)
            _ = nodes (a + r) :=
              (hstationary (a + r) (by omega)).symm
            _ = (chain.state (a + r)).anchor :=
              (chain.state_anchor_eq_node hinitial (a + r)).symm
        have hvectorZero : (chain.data (a + r)).v = 0 :=
          DifferentialSuccessorZero.data_vector_eq_zero_of_anchor_eq
            (chain.data (a + r)) hnextAtAnchor
        calc
          chain.state (a + Nat.succ r) =
              chain.state (a + r + 1) := by
            congr 1
          _ = (chain.data (a + r)).successor :=
            chain.state_succ (a + r)
          _ = chain.state (a + r) :=
            DifferentialSuccessorZero.successor_eq_of_vector_eq_zero
              (chain.data (a + r)) hvectorZero
          _ = chain.state a := ih
  have h := hind (q - a)
  simpa [Nat.add_sub_of_le haq] using h

end StationaryReachableChain

/-! ## Actual boundary and insertion histories at one refined stage -/

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace E M] [IsManifold I ∞ M]
variable [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M]

variable {g : ClosedSmoothRiemannianMetric 3 M}
variable {successor : UniformGenericSuccessorRadiusCertificate g}
variable {endpoint : RootedPathContinuedEndpointFamily g}
variable {x y z : M} {leftMesh rightMesh : ℝ}
variable {leftTerminal : TerminalShortPathCertificate g x z leftMesh}
variable {rightTerminal : TerminalShortPathCertificate g y z rightMesh}
variable {N : ℕ}

/-- All actual histories needed to test strict-factor transport on the two
retained boundary rows of one refined grid.  Coarse boundary reachability is
explicit because it is not a consequence of fine-grid edge smallness. -/
structure BoundaryInsertionHistories
    (precertificate : RefinedUniformRadiusGridPrecertificate successor endpoint
      leftTerminal rightTerminal N) where
  leftBoundaryChain : ReachableChain
    (reparameterizedBoundaryNodes endpoint leftTerminal N) endpoint.root
  rightBoundaryChain : ReachableChain
    (reparameterizedBoundaryNodes endpoint rightTerminal N) endpoint.root
  leftInsertionChain : ∀ n i : ℕ,
    ReachableChain
      (insertNodeListSchedule
        (factorRefinementStage
          (reparameterizedBoundaryNodes endpoint leftTerminal N)
          (precertificate.refinedRowNodes 0) precertificate.factor n)
        (precertificate.factor n)
        (factorGapNodes (precertificate.refinedRowNodes 0)
          precertificate.factor n) i) endpoint.root
  rightInsertionChain : ∀ n i : ℕ,
    ReachableChain
      (insertNodeListSchedule
        (factorRefinementStage
          (reparameterizedBoundaryNodes endpoint rightTerminal N)
          (precertificate.refinedRowNodes (N + 2)) precertificate.factor n)
        (precertificate.factor n)
        (factorGapNodes (precertificate.refinedRowNodes (N + 2))
          precertificate.factor n) i) endpoint.root

/-- One geometric refined grid together with every actual coarse and
intermediate boundary history used by its adaptive insertion tests. -/
structure RefinedBoundaryInsertionStage
    (successor : UniformGenericSuccessorRadiusCertificate g)
    (endpoint : RootedPathContinuedEndpointFamily g)
    {x y z : M} {leftMesh rightMesh : ℝ}
    (leftTerminal : TerminalShortPathCertificate g x z leftMesh)
    (rightTerminal : TerminalShortPathCertificate g y z rightMesh)
    (N : ℕ) where
  precertificate : RefinedUniformRadiusGridPrecertificate successor endpoint
    leftTerminal rightTerminal N
  histories : BoundaryInsertionHistories precertificate

namespace RefinedBoundaryInsertionStage

variable (stage : RefinedBoundaryInsertionStage successor endpoint
  leftTerminal rightTerminal N)

/-! ### The four exact insertion-defect maxima -/

def leftFirstDefect : ℝ :=
  strictFactorFirstDefect
    (reparameterizedBoundaryNodes endpoint leftTerminal N)
    (stage.precertificate.refinedRowNodes 0) (N + 1)
    stage.precertificate.factor stage.histories.leftInsertionChain

def leftSecondDefect : ℝ :=
  strictFactorSecondDefect
    (reparameterizedBoundaryNodes endpoint leftTerminal N)
    (stage.precertificate.refinedRowNodes 0) (N + 1)
    stage.precertificate.factor stage.histories.leftInsertionChain

def rightFirstDefect : ℝ :=
  strictFactorFirstDefect
    (reparameterizedBoundaryNodes endpoint rightTerminal N)
    (stage.precertificate.refinedRowNodes (N + 2)) (N + 1)
    stage.precertificate.factor stage.histories.rightInsertionChain

def rightSecondDefect : ℝ :=
  strictFactorSecondDefect
    (reparameterizedBoundaryNodes endpoint rightTerminal N)
    (stage.precertificate.refinedRowNodes (N + 2)) (N + 1)
    stage.precertificate.factor stage.histories.rightInsertionChain

/-- The first adaptive defect tests both boundary insertion schedules. -/
def firstDefect : ℝ := max stage.leftFirstDefect stage.rightFirstDefect

/-- The insertion-only part of the second adaptive defect. -/
def insertionSecondDefect : ℝ :=
  max stage.leftSecondDefect stage.rightSecondDefect

/-- The complete second adaptive defect: both insertion schedules and both
actual finite grid edge families. -/
def secondDefect : ℝ :=
  letI : MetricSpace M := g.toMetricSpace
  let F := reparameterizedOverlapHomotopy endpoint leftTerminal rightTerminal N
  max stage.insertionSecondDefect
    (max (stage.precertificate.subdivision.horizontalMaximum F)
      (stage.precertificate.subdivision.verticalMaximum F))

/-! ### Exact curvature radius certificates and their dependent choices -/

theorem leftCommonRadiusCertificate_of_curvature
    (hcurv : HasConstantSectionalCurvature3 g 1) :
    letI : MetricSpace M := g.toMetricSpace
    StrictFactorCommonRadiusCertificate
      (reparameterizedBoundaryNodes endpoint leftTerminal N)
      (stage.precertificate.refinedRowNodes 0) endpoint.root (N + 1)
      stage.precertificate.factor stage.histories.leftBoundaryChain
      (stage.precertificate.refinedRowChain 0)
      stage.histories.leftInsertionChain := by
  letI : MetricSpace M := g.toMetricSpace
  apply ReachableChain.strictFactorCommonRadiusCertificate_of_curvature
    hcurv (reparameterizedBoundaryNodes endpoint leftTerminal N)
      (stage.precertificate.refinedRowNodes 0) (N + 1)
      stage.precertificate.factor stage.precertificate.factor_zero
  · intro n hn
    exact stage.precertificate.factor_strict n hn
  · intro n _hn
    simpa [RefinedUniformRadiusGridPrecertificate.refinedRowNodes,
      stage.precertificate.factor_zero] using
      stage.precertificate.refinedLeftBoundaryNode_at_factor n

theorem rightCommonRadiusCertificate_of_curvature
    (hcurv : HasConstantSectionalCurvature3 g 1) :
    letI : MetricSpace M := g.toMetricSpace
    StrictFactorCommonRadiusCertificate
      (reparameterizedBoundaryNodes endpoint rightTerminal N)
      (stage.precertificate.refinedRowNodes (N + 2)) endpoint.root (N + 1)
      stage.precertificate.factor stage.histories.rightBoundaryChain
      (stage.precertificate.refinedRowChain (N + 2))
      stage.histories.rightInsertionChain := by
  letI : MetricSpace M := g.toMetricSpace
  apply ReachableChain.strictFactorCommonRadiusCertificate_of_curvature
    hcurv (reparameterizedBoundaryNodes endpoint rightTerminal N)
      (stage.precertificate.refinedRowNodes (N + 2)) (N + 1)
      stage.precertificate.factor stage.precertificate.factor_zero
  · intro n hn
    exact stage.precertificate.factor_strict n hn
  · intro n _hn
    exact stage.precertificate.refinedRightBoundaryNode_at_factor n

/-- The first scalar radius selected from the actual left insertion
histories. -/
noncomputable def leftFirstRadius
    (hcurv : HasConstantSectionalCurvature3 g 1) : ℝ := by
  letI : MetricSpace M := g.toMetricSpace
  exact Classical.choose (stage.leftCommonRadiusCertificate_of_curvature hcurv)

theorem leftFirstRadius_pos
    (hcurv : HasConstantSectionalCurvature3 g 1) :
    0 < stage.leftFirstRadius hcurv := by
  letI : MetricSpace M := g.toMetricSpace
  exact
    (Classical.choose_spec
      (stage.leftCommonRadiusCertificate_of_curvature hcurv)).1

/-- The first scalar radius selected from the actual right insertion
histories. -/
noncomputable def rightFirstRadius
    (hcurv : HasConstantSectionalCurvature3 g 1) : ℝ := by
  letI : MetricSpace M := g.toMetricSpace
  exact Classical.choose (stage.rightCommonRadiusCertificate_of_curvature hcurv)

theorem rightFirstRadius_pos
    (hcurv : HasConstantSectionalCurvature3 g 1) :
    0 < stage.rightFirstRadius hcurv := by
  letI : MetricSpace M := g.toMetricSpace
  exact
    (Classical.choose_spec
      (stage.rightCommonRadiusCertificate_of_curvature hcurv)).1

/-- The common first radius for the two boundary insertion schedules. -/
noncomputable def firstRadius
    (hcurv : HasConstantSectionalCurvature3 g 1) : ℝ :=
  min (stage.leftFirstRadius hcurv) (stage.rightFirstRadius hcurv)

theorem firstRadius_pos
    (hcurv : HasConstantSectionalCurvature3 g 1) :
    0 < stage.firstRadius hcurv :=
  lt_min (stage.leftFirstRadius_pos hcurv) (stage.rightFirstRadius_pos hcurv)

theorem leftFirstDefect_lt_leftFirstRadius_of_first
    (hcurv : HasConstantSectionalCurvature3 g 1)
    (hfirst : stage.firstDefect < stage.firstRadius hcurv) :
    stage.leftFirstDefect < stage.leftFirstRadius hcurv :=
  (le_max_left _ _).trans_lt
    (hfirst.trans_le (min_le_left _ _))

theorem rightFirstDefect_lt_rightFirstRadius_of_first
    (hcurv : HasConstantSectionalCurvature3 g 1)
    (hfirst : stage.firstDefect < stage.firstRadius hcurv) :
    stage.rightFirstDefect < stage.rightFirstRadius hcurv :=
  (le_max_right _ _).trans_lt
    (hfirst.trans_le (min_le_right _ _))

/-- After the measured left first defect passes its chosen scalar radius,
the certificate exposes a positive scalar second radius whose measured
second-defect bound gives the actual factor-index state equality. -/
theorem exists_leftSecondRadius_of_first
    (hcurv : HasConstantSectionalCurvature3 g 1)
    (hfirst : stage.firstDefect < stage.firstRadius hcurv) :
    ∃ radius > (0 : ℝ),
      stage.leftSecondDefect < radius →
        stage.histories.leftBoundaryChain.state (N + 1) =
          (stage.precertificate.refinedRowChain 0).state
            (stage.precertificate.factor (N + 1)) := by
  letI : MetricSpace M := g.toMetricSpace
  have hfirstPointwise :
      ∀ n : Fin (N + 1),
        ∀ i : Fin
          (factorGapNodes (stage.precertificate.refinedRowNodes 0)
            stage.precertificate.factor n).length,
          strictFactorFirstDistance
            (reparameterizedBoundaryNodes endpoint leftTerminal N)
            (stage.precertificate.refinedRowNodes 0) (N + 1)
            stage.precertificate.factor stage.histories.leftInsertionChain
            ⟨n, i⟩ < stage.leftFirstRadius hcurv := by
    have hpoint :=
      (strictFactorFirstDefect_lt_iff
        (reparameterizedBoundaryNodes endpoint leftTerminal N)
        (stage.precertificate.refinedRowNodes 0) (N + 1)
        stage.precertificate.factor stage.histories.leftInsertionChain
        (stage.leftFirstRadius_pos hcurv)).1
          (stage.leftFirstDefect_lt_leftFirstRadius_of_first hcurv hfirst)
    intro n i
    exact hpoint ⟨n, i⟩
  have hfirstCertificate :
      ∀ n : Fin (N + 1),
        ∀ i : Fin
          (factorGapNodes (stage.precertificate.refinedRowNodes 0)
            stage.precertificate.factor n).length,
        dist
            (insertNodeListSchedule
              (factorRefinementStage
                (reparameterizedBoundaryNodes endpoint leftTerminal N)
                (stage.precertificate.refinedRowNodes 0)
                stage.precertificate.factor n)
              (stage.precertificate.factor n)
              (factorGapNodes (stage.precertificate.refinedRowNodes 0)
                stage.precertificate.factor n) (i + 1)
              (stage.precertificate.factor n + i + 1))
            ((stage.histories.leftInsertionChain n (i + 1)).state
              (stage.precertificate.factor n + i)).anchor <
          stage.leftFirstRadius hcurv := by
    intro n i
    simpa [strictFactorFirstDistance] using hfirstPointwise n i
  rcases
      (Classical.choose_spec
        (stage.leftCommonRadiusCertificate_of_curvature hcurv)).2
        hfirstCertificate with
    ⟨radius, hradius, hafterSecond⟩
  refine ⟨radius, hradius, ?_⟩
  intro hsecond
  apply hafterSecond
  have hsecondPointwise :=
    (strictFactorSecondDefect_lt_iff
      (reparameterizedBoundaryNodes endpoint leftTerminal N)
      (stage.precertificate.refinedRowNodes 0) (N + 1)
      stage.precertificate.factor stage.histories.leftInsertionChain
      hradius).1 hsecond
  intro n i
  simpa [strictFactorSecondDistance] using hsecondPointwise ⟨n, i⟩

/-- The right boundary analogue of `exists_leftSecondRadius_of_first`. -/
theorem exists_rightSecondRadius_of_first
    (hcurv : HasConstantSectionalCurvature3 g 1)
    (hfirst : stage.firstDefect < stage.firstRadius hcurv) :
    ∃ radius > (0 : ℝ),
      stage.rightSecondDefect < radius →
        stage.histories.rightBoundaryChain.state (N + 1) =
          (stage.precertificate.refinedRowChain (N + 2)).state
            (stage.precertificate.factor (N + 1)) := by
  letI : MetricSpace M := g.toMetricSpace
  have hfirstPointwise :
      ∀ n : Fin (N + 1),
        ∀ i : Fin
          (factorGapNodes
            (stage.precertificate.refinedRowNodes (N + 2))
            stage.precertificate.factor n).length,
          strictFactorFirstDistance
            (reparameterizedBoundaryNodes endpoint rightTerminal N)
            (stage.precertificate.refinedRowNodes (N + 2)) (N + 1)
            stage.precertificate.factor stage.histories.rightInsertionChain
            ⟨n, i⟩ < stage.rightFirstRadius hcurv := by
    have hpoint :=
      (strictFactorFirstDefect_lt_iff
        (reparameterizedBoundaryNodes endpoint rightTerminal N)
        (stage.precertificate.refinedRowNodes (N + 2)) (N + 1)
        stage.precertificate.factor stage.histories.rightInsertionChain
        (stage.rightFirstRadius_pos hcurv)).1
          (stage.rightFirstDefect_lt_rightFirstRadius_of_first hcurv hfirst)
    intro n i
    exact hpoint ⟨n, i⟩
  have hfirstCertificate :
      ∀ n : Fin (N + 1),
        ∀ i : Fin
          (factorGapNodes
            (stage.precertificate.refinedRowNodes (N + 2))
            stage.precertificate.factor n).length,
        dist
            (insertNodeListSchedule
              (factorRefinementStage
                (reparameterizedBoundaryNodes endpoint rightTerminal N)
                (stage.precertificate.refinedRowNodes (N + 2))
                stage.precertificate.factor n)
              (stage.precertificate.factor n)
              (factorGapNodes
                (stage.precertificate.refinedRowNodes (N + 2))
                stage.precertificate.factor n) (i + 1)
              (stage.precertificate.factor n + i + 1))
            ((stage.histories.rightInsertionChain n (i + 1)).state
              (stage.precertificate.factor n + i)).anchor <
          stage.rightFirstRadius hcurv := by
    intro n i
    simpa [strictFactorFirstDistance] using hfirstPointwise n i
  rcases
      (Classical.choose_spec
        (stage.rightCommonRadiusCertificate_of_curvature hcurv)).2
        hfirstCertificate with
    ⟨radius, hradius, hafterSecond⟩
  refine ⟨radius, hradius, ?_⟩
  intro hsecond
  apply hafterSecond
  have hsecondPointwise :=
    (strictFactorSecondDefect_lt_iff
      (reparameterizedBoundaryNodes endpoint rightTerminal N)
      (stage.precertificate.refinedRowNodes (N + 2)) (N + 1)
      stage.precertificate.factor stage.histories.rightInsertionChain
      hradius).1 hsecond
  intro n i
  simpa [strictFactorSecondDistance] using hsecondPointwise ⟨n, i⟩

noncomputable def leftSecondRadius
    (hcurv : HasConstantSectionalCurvature3 g 1)
    (hfirst : stage.firstDefect < stage.firstRadius hcurv) : ℝ :=
  Classical.choose (stage.exists_leftSecondRadius_of_first hcurv hfirst)

theorem leftSecondRadius_pos
    (hcurv : HasConstantSectionalCurvature3 g 1)
    (hfirst : stage.firstDefect < stage.firstRadius hcurv) :
    0 < stage.leftSecondRadius hcurv hfirst :=
  (Classical.choose_spec
    (stage.exists_leftSecondRadius_of_first hcurv hfirst)).1

theorem left_factor_state_eq_of_second
    (hcurv : HasConstantSectionalCurvature3 g 1)
    (hfirst : stage.firstDefect < stage.firstRadius hcurv)
    (hsecond : stage.leftSecondDefect <
      stage.leftSecondRadius hcurv hfirst) :
    stage.histories.leftBoundaryChain.state (N + 1) =
      (stage.precertificate.refinedRowChain 0).state
        (stage.precertificate.factor (N + 1)) :=
  (Classical.choose_spec
    (stage.exists_leftSecondRadius_of_first hcurv hfirst)).2 hsecond

noncomputable def rightSecondRadius
    (hcurv : HasConstantSectionalCurvature3 g 1)
    (hfirst : stage.firstDefect < stage.firstRadius hcurv) : ℝ :=
  Classical.choose (stage.exists_rightSecondRadius_of_first hcurv hfirst)

theorem rightSecondRadius_pos
    (hcurv : HasConstantSectionalCurvature3 g 1)
    (hfirst : stage.firstDefect < stage.firstRadius hcurv) :
    0 < stage.rightSecondRadius hcurv hfirst :=
  (Classical.choose_spec
    (stage.exists_rightSecondRadius_of_first hcurv hfirst)).1

theorem right_factor_state_eq_of_second
    (hcurv : HasConstantSectionalCurvature3 g 1)
    (hfirst : stage.firstDefect < stage.firstRadius hcurv)
    (hsecond : stage.rightSecondDefect <
      stage.rightSecondRadius hcurv hfirst) :
    stage.histories.rightBoundaryChain.state (N + 1) =
      (stage.precertificate.refinedRowChain (N + 2)).state
        (stage.precertificate.factor (N + 1)) :=
  (Classical.choose_spec
    (stage.exists_rightSecondRadius_of_first hcurv hfirst)).2 hsecond

/-! ### The post-realization arbitrary-grid radius -/

noncomputable def gridRadius
    (hcurv : HasConstantSectionalCurvature3 g 1) : ℝ := by
  letI : MetricSpace M := g.toMetricSpace
  exact Classical.choose (stage.precertificate.grid.exists_commonMeshRadius hcurv)

theorem gridRadius_pos
    (hcurv : HasConstantSectionalCurvature3 g 1) :
    0 < stage.gridRadius hcurv := by
  letI : MetricSpace M := g.toMetricSpace
  exact
    (Classical.choose_spec
      (stage.precertificate.grid.exists_commonMeshRadius hcurv)).1

/-- The dependent second radius is the minimum of the two exposed insertion
radii and the independently selected post-realization grid radius. -/
noncomputable def secondRadius
    (hcurv : HasConstantSectionalCurvature3 g 1)
    (hfirst : stage.firstDefect < stage.firstRadius hcurv) : ℝ :=
  min (stage.leftSecondRadius hcurv hfirst)
    (min (stage.rightSecondRadius hcurv hfirst) (stage.gridRadius hcurv))

theorem secondRadius_pos
    (hcurv : HasConstantSectionalCurvature3 g 1)
    (hfirst : stage.firstDefect < stage.firstRadius hcurv) :
    0 < stage.secondRadius hcurv hfirst :=
  lt_min (stage.leftSecondRadius_pos hcurv hfirst)
    (lt_min (stage.rightSecondRadius_pos hcurv hfirst)
      (stage.gridRadius_pos hcurv))

/-! ### Moving retained states to the arbitrary grid's terminal indices -/

/-- Since the retained old terminal column has parameter one, monotonicity
forces every later refined subdivision parameter to equal one. -/
theorem subdivision_nodes_eq_one_of_factor_terminal_le
    {q : ℕ}
    (hq : stage.precertificate.factor (N + 1) ≤ q) :
    stage.precertificate.subdivision.nodes q = 1 := by
  apply le_antisymm
  · exact le_top
  · have hmono := stage.precertificate.subdivision.nodes_monotone hq
    have hfactorOne :
        stage.precertificate.subdivision.nodes
            (stage.precertificate.factor (N + 1)) = 1 := by
      rw [stage.precertificate.subdivision_nodes_factor (N + 1)]
      exact commonUniformSubdivision_terminal N (N + 1) le_rfl
    rw [hfactorOne] at hmono
    exact hmono

theorem refinedRowNodes_stationary_from_factor_terminal
    (m q : ℕ)
    (hq : stage.precertificate.factor (N + 1) ≤ q) :
    stage.precertificate.refinedRowNodes m q =
      stage.precertificate.refinedRowNodes m
        (stage.precertificate.factor (N + 1)) := by
  simp only [RefinedUniformRadiusGridPrecertificate.refinedRowNodes,
    homotopyGridRow]
  rw [stage.subdivision_nodes_eq_one_of_factor_terminal_le hq,
    stage.subdivision_nodes_eq_one_of_factor_terminal_le le_rfl]

/-- Every retained boundary-row state at the old terminal factor equals the
same row's state at the arbitrary grid's final comparison column. -/
theorem refinedRowChain_terminal_eq_factorTerminal
    (m : ℕ) :
    (stage.precertificate.refinedRowChain m).state
        (stage.precertificate.subdivision.terminalIndex + 1) =
      (stage.precertificate.refinedRowChain m).state
        (stage.precertificate.factor (N + 1)) := by
  have hroot : endpoint.root.anchor =
      stage.precertificate.refinedRowNodes m 0 := by
    simp [RefinedUniformRadiusGridPrecertificate.refinedRowNodes,
      homotopyGridRow, stage.precertificate.subdivision.nodes_zero]
  have hle : stage.precertificate.factor (N + 1) ≤
      stage.precertificate.subdivision.terminalIndex + 1 := by
    have hfactor := stage.precertificate.factor_le_terminalIndex (N + 1)
    omega
  exact ReachableChain.state_eq_of_nodes_stationary_from
    (stage.precertificate.refinedRowChain m) hroot
    (stage.precertificate.factor (N + 1))
    (stage.precertificate.subdivision.terminalIndex + 1) hle
    (fun q hq ↦
      stage.refinedRowNodes_stationary_from_factor_terminal m q hq)

/-- The retained zeroth row chain is the arbitrary realized grid's zeroth
row chain, up to proof-irrelevant spelling of its finite row index. -/
theorem refinedLeftRow_state_eq_gridZero (q : ℕ) :
    (stage.precertificate.refinedRowChain 0).state q =
      (stage.precertificate.grid.rowChain 0).state q := by
  have hindex : stage.precertificate.refinedRowIndex 0 =
      (0 : Fin (stage.precertificate.subdivision.terminalIndex + 2)) := by
    apply Fin.ext
    exact stage.precertificate.factor_zero
  change
    (stage.precertificate.grid.rowChain
      (stage.precertificate.refinedRowIndex 0)).state q =
      (stage.precertificate.grid.rowChain 0).state q
  rw [hindex]

/-- The retained old final homotopy row has parameter one, so its realized
states agree with those on the arbitrary grid's last row. -/
theorem refinedRightRow_state_eq_gridLast (q : ℕ) :
    (stage.precertificate.refinedRowChain (N + 2)).state q =
      (stage.precertificate.grid.rowChain
        (Fin.last (stage.precertificate.subdivision.terminalIndex + 1))).state q := by
  apply ReachableChain.state_eq_of_prefix_nodes
  intro j _hj
  have hfactorOuter :
      stage.precertificate.subdivision.nodes
          (stage.precertificate.factor (N + 2)) = 1 := by
    rw [stage.precertificate.subdivision_nodes_factor (N + 2)]
    exact commonUniformSubdivision_terminal N (N + 2) (by omega)
  have hlastOuter :
      stage.precertificate.subdivision.nodes
          (Fin.last (stage.precertificate.subdivision.terminalIndex + 1)) = 1 := by
    apply stage.precertificate.subdivision.nodes_one
    simp
  simp only [RefinedUniformRadiusGridPrecertificate.refinedRowNodes,
    homotopyGridRow]
  rw [hfactorOuter, hlastOuter]

/-- Bounds on the two actual finite grid maxima invoke the chosen common
radius theorem on this exact realized arbitrary grid. -/
theorem grid_boundary_state_eq_of_finiteMaxima
    (hcurv : HasConstantSectionalCurvature3 g 1)
    (hhorizontal : letI : MetricSpace M := g.toMetricSpace
      stage.precertificate.subdivision.horizontalMaximum
          (reparameterizedOverlapHomotopy endpoint leftTerminal rightTerminal N) <
        stage.gridRadius hcurv)
    (hvertical : letI : MetricSpace M := g.toMetricSpace
      stage.precertificate.subdivision.verticalMaximum
          (reparameterizedOverlapHomotopy endpoint leftTerminal rightTerminal N) <
        stage.gridRadius hcurv) :
    (stage.precertificate.grid.rowChain 0).state
        (stage.precertificate.subdivision.terminalIndex + 1) =
      (stage.precertificate.grid.rowChain
        (Fin.last (stage.precertificate.subdivision.terminalIndex + 1))).state
          (stage.precertificate.subdivision.terminalIndex + 1) := by
  letI : MetricSpace M := g.toMetricSpace
  apply
    (Classical.choose_spec
      (stage.precertificate.grid.exists_commonMeshRadius hcurv)).2
  · rw [FiniteHomotopySubdivision.horizontalMaximum_lt_iff] at hhorizontal
    intro m j
    simpa [FiniteHomotopySubdivision.horizontalEdgeDistance] using
      hhorizontal (m, j)
  · rw [FiniteHomotopySubdivision.verticalMaximum_lt_iff] at hvertical
    intro m j
    simpa [FiniteHomotopySubdivision.verticalEdgeDistance] using
      hvertical (m, j)

/-! ### A validated stage gives concrete terminal transport -/

theorem boundary_terminal_state_eq_of_validated
    (hcurv : HasConstantSectionalCurvature3 g 1)
    (hfirst : stage.firstDefect < stage.firstRadius hcurv)
    (hsecond : stage.secondDefect < stage.secondRadius hcurv hfirst) :
    stage.histories.leftBoundaryChain.state (N + 1) =
      stage.histories.rightBoundaryChain.state (N + 1) := by
  letI : MetricSpace M := g.toMetricSpace
  have hleftSecond : stage.leftSecondDefect <
      stage.leftSecondRadius hcurv hfirst := by
    exact (le_max_left _ _).trans_lt
      ((le_max_left _ _).trans_lt
        (hsecond.trans_le (min_le_left _ _)))
  have hrightSecond : stage.rightSecondDefect <
      stage.rightSecondRadius hcurv hfirst := by
    exact (le_max_right _ _).trans_lt
      ((le_max_left _ _).trans_lt
        (hsecond.trans_le ((min_le_right _ _).trans (min_le_left _ _))))
  have hhorizontal :
      stage.precertificate.subdivision.horizontalMaximum
          (reparameterizedOverlapHomotopy endpoint leftTerminal rightTerminal N) <
        stage.gridRadius hcurv := by
    have hleGrid : stage.secondRadius hcurv hfirst ≤ stage.gridRadius hcurv :=
      (min_le_right _ _).trans (min_le_right _ _)
    exact (le_max_left _ _).trans_lt
      ((le_max_right _ _).trans_lt (hsecond.trans_le hleGrid))
  have hvertical :
      stage.precertificate.subdivision.verticalMaximum
          (reparameterizedOverlapHomotopy endpoint leftTerminal rightTerminal N) <
        stage.gridRadius hcurv := by
    have hleGrid : stage.secondRadius hcurv hfirst ≤ stage.gridRadius hcurv :=
      (min_le_right _ _).trans (min_le_right _ _)
    exact (le_max_right _ _).trans_lt
      ((le_max_right _ _).trans_lt (hsecond.trans_le hleGrid))
  have hleftFactor :=
    stage.left_factor_state_eq_of_second hcurv hfirst hleftSecond
  have hrightFactor :=
    stage.right_factor_state_eq_of_second hcurv hfirst hrightSecond
  have hleftStationary := stage.refinedRowChain_terminal_eq_factorTerminal 0
  have hrightStationary :=
    stage.refinedRowChain_terminal_eq_factorTerminal (N + 2)
  have hleftGrid := stage.refinedLeftRow_state_eq_gridZero
    (stage.precertificate.subdivision.terminalIndex + 1)
  have hrightGrid := stage.refinedRightRow_state_eq_gridLast
    (stage.precertificate.subdivision.terminalIndex + 1)
  have hgrid :=
    stage.grid_boundary_state_eq_of_finiteMaxima hcurv hhorizontal hvertical
  calc
    stage.histories.leftBoundaryChain.state (N + 1) =
        (stage.precertificate.refinedRowChain 0).state
          (stage.precertificate.factor (N + 1)) := hleftFactor
    _ = (stage.precertificate.refinedRowChain 0).state
          (stage.precertificate.subdivision.terminalIndex + 1) :=
      hleftStationary.symm
    _ = (stage.precertificate.grid.rowChain 0).state
          (stage.precertificate.subdivision.terminalIndex + 1) := hleftGrid
    _ = (stage.precertificate.grid.rowChain
          (Fin.last (stage.precertificate.subdivision.terminalIndex + 1))).state
          (stage.precertificate.subdivision.terminalIndex + 1) := hgrid
    _ = (stage.precertificate.refinedRowChain (N + 2)).state
          (stage.precertificate.subdivision.terminalIndex + 1) :=
      hrightGrid.symm
    _ = (stage.precertificate.refinedRowChain (N + 2)).state
          (stage.precertificate.factor (N + 1)) := hrightStationary
    _ = stage.histories.rightBoundaryChain.state (N + 1) :=
      hrightFactor.symm

/-- A successful two-stage test produces the exact finite transport consumed
by Cartan germ compatibility.  The predecessor identities are derived from
the coarse boundary chains, and the terminal equality is the theorem above. -/
noncomputable def toCommonRootTerminalTransport_of_validated
    (hcurv : HasConstantSectionalCurvature3 g 1)
    (hfirst : stage.firstDefect < stage.firstRadius hcurv)
    (hsecond : stage.secondDefect < stage.secondRadius hcurv hfirst) :
    CommonRootTerminalTransport
      (endpoint.terminalState x) (endpoint.terminalState y) z where
  root := endpoint.root
  leftNodes := reparameterizedBoundaryNodes endpoint leftTerminal N
  rightNodes := reparameterizedBoundaryNodes endpoint rightTerminal N
  leftChain := stage.histories.leftBoundaryChain
  rightChain := stage.histories.rightBoundaryChain
  leftIndex := N
  rightIndex := N
  left_predecessor :=
    reachableChain_state_commonPredecessor_eq_terminalState
      endpoint leftTerminal N stage.precertificate.left_terminalIndex_le
        stage.histories.leftBoundaryChain
  right_predecessor :=
    reachableChain_state_commonPredecessor_eq_terminalState
      endpoint rightTerminal N stage.precertificate.right_terminalIndex_le
        stage.histories.rightBoundaryChain
  left_next_node :=
    reparameterizedBoundaryNodes_terminal endpoint leftTerminal N (N + 1)
      le_rfl
  right_next_node :=
    reparameterizedBoundaryNodes_terminal endpoint rightTerminal N (N + 1)
      le_rfl
  terminal_eq :=
    stage.boundary_terminal_state_eq_of_validated hcurv hfirst hsecond

theorem germ_value_eq_of_validated
    (hcurv : HasConstantSectionalCurvature3 g 1)
    (hfirst : stage.firstDefect < stage.firstRadius hcurv)
    (hsecond : stage.secondDefect < stage.secondRadius hcurv hfirst) :
    (endpoint.terminalState x).germ z =
      (endpoint.terminalState y).germ z :=
  germ_value_eq_of_commonRootTerminalTransport
    (endpoint.terminalState x) (endpoint.terminalState y) z
    (stage.toCommonRootTerminalTransport_of_validated hcurv hfirst hsecond)

end RefinedBoundaryInsertionStage

/-! ## Compact history of actual insertion stages -/

/-- Honest adaptive feedback for a sequence of refined boundary insertion
stages.  The insertion and geometric vanishing hypotheses are separate: the
verified finite-maxima refinement theorem supplies the latter, whereas the
former is genuinely additional history-dependent input. -/
structure RefinedBoundaryInsertionCompactHistory
    (successor : UniformGenericSuccessorRadiusCertificate g)
    (endpoint : RootedPathContinuedEndpointFamily g)
    (hcurv : HasConstantSectionalCurvature3 g 1)
    {x y z : M} {leftMesh rightMesh : ℝ}
    (leftTerminal : TerminalShortPathCertificate g x z leftMesh)
    (rightTerminal : TerminalShortPathCertificate g y z rightMesh)
    (N : ℕ) where
  History : Type u
  [historyTopology : TopologicalSpace History]
  compactHistory : Set History
  isCompact_compactHistory : IsCompact compactHistory
  historyPoint : ℕ → History
  historyPoint_mem : ∀ n, historyPoint n ∈ compactHistory
  threshold : History → ℝ
  threshold_lowerSemicontinuous :
    LowerSemicontinuousOn threshold compactHistory
  threshold_pos : ∀ a ∈ compactHistory, 0 < threshold a
  insertionStage : ℕ → RefinedBoundaryInsertionStage successor endpoint
    leftTerminal rightTerminal N
  activeThreshold_eq : ∀ n,
    twoStageActiveThreshold
        (fun j ↦ (insertionStage j).firstRadius hcurv)
        (fun j ↦ (insertionStage j).firstDefect)
        (fun j hfirst ↦
          (insertionStage j).secondRadius hcurv hfirst) n =
      threshold (historyPoint n)
  insertionDefects_vanish : ∀ delta > (0 : ℝ), ∃ stageIndex, ∀ n ≥ stageIndex,
    (insertionStage n).firstDefect < delta ∧
      (insertionStage n).insertionSecondDefect < delta
  finiteGridMaxima_vanish : ∀ delta > (0 : ℝ), ∃ stageIndex, ∀ n ≥ stageIndex,
    letI : MetricSpace M := g.toMetricSpace
    let F := reparameterizedOverlapHomotopy endpoint leftTerminal rightTerminal N
    ((insertionStage n).precertificate.subdivision.horizontalMaximum F < delta) ∧
      ((insertionStage n).precertificate.subdivision.verticalMaximum F < delta)

namespace RefinedBoundaryInsertionCompactHistory

set_option linter.unusedVariables false in
/-- The exact two defects consumed by the abstract adaptive theorem vanish.
This combines, without identifying, the separate insertion-feedback and
finite-grid-maxima hypotheses. -/
theorem defects_vanish
    {hcurv : HasConstantSectionalCurvature3 g 1}
    (history : RefinedBoundaryInsertionCompactHistory successor endpoint hcurv
      leftTerminal rightTerminal N) :
    ∀ delta > (0 : ℝ), ∃ stageIndex, ∀ n ≥ stageIndex,
      (history.insertionStage n).firstDefect < delta ∧
        (history.insertionStage n).secondDefect < delta := by
  intro delta hdelta
  rcases history.insertionDefects_vanish delta hdelta with
    ⟨N₁, hN₁⟩
  rcases history.finiteGridMaxima_vanish delta hdelta with
    ⟨N₂, hN₂⟩
  refine ⟨max N₁ N₂, ?_⟩
  intro n hn
  have hn₁ : N₁ ≤ n := (le_max_left N₁ N₂).trans hn
  have hn₂ : N₂ ≤ n := (le_max_right N₁ N₂).trans hn
  have hinsertion := hN₁ n hn₁
  have hgrid := hN₂ n hn₂
  refine ⟨hinsertion.1, ?_⟩
  rw [RefinedBoundaryInsertionStage.secondDefect]
  exact max_lt hinsertion.2 (max_lt hgrid.1 hgrid.2)

/-- Compact lower-semicontinuity selects one stage whose actual insertion
defects and actual grid maxima pass their own dependent radii. -/
theorem exists_validated_stage
    {hcurv : HasConstantSectionalCurvature3 g 1}
    (history : RefinedBoundaryInsertionCompactHistory successor endpoint hcurv
      leftTerminal rightTerminal N) :
    ∃ n,
      TwoStageValidated
        (fun j ↦ (history.insertionStage j).firstRadius hcurv)
        (fun j ↦ (history.insertionStage j).firstDefect)
        (fun j ↦ (history.insertionStage j).secondDefect)
        (fun j hfirst ↦
          (history.insertionStage j).secondRadius hcurv hfirst) n := by
  letI : TopologicalSpace history.History := history.historyTopology
  apply exists_twoStageValidated_of_compact_history_lowerSemicontinuous_threshold
    history.isCompact_compactHistory history.historyPoint
      history.historyPoint_mem history.threshold
      history.threshold_lowerSemicontinuous history.threshold_pos
      (fun j ↦ (history.insertionStage j).firstRadius hcurv)
      (fun j ↦ (history.insertionStage j).firstDefect)
      (fun j ↦ (history.insertionStage j).secondDefect)
      (fun j hfirst ↦
        (history.insertionStage j).secondRadius hcurv hfirst)
      history.activeThreshold_eq history.defects_vanish

/-- The selected validated stage produces a concrete common-root terminal
transport, not merely a renamed compatibility proposition. -/
theorem nonempty_commonRootTerminalTransport
    {hcurv : HasConstantSectionalCurvature3 g 1}
    (history : RefinedBoundaryInsertionCompactHistory successor endpoint hcurv
      leftTerminal rightTerminal N) :
    Nonempty
      (CommonRootTerminalTransport
        (endpoint.terminalState x) (endpoint.terminalState y) z) := by
  rcases history.exists_validated_stage with ⟨n, hvalidated⟩
  rcases hvalidated with ⟨hfirst, hsecond⟩
  exact ⟨(history.insertionStage n).toCommonRootTerminalTransport_of_validated
    hcurv hfirst hsecond⟩

/-- Honest compact-history feedback on the actual insertion histories and
actual finite grid maxima identifies the two terminal Cartan germ values. -/
theorem germ_value_eq
    {hcurv : HasConstantSectionalCurvature3 g 1}
    (history : RefinedBoundaryInsertionCompactHistory successor endpoint hcurv
      leftTerminal rightTerminal N) :
    (endpoint.terminalState x).germ z =
      (endpoint.terminalState y).germ z := by
  exact germ_value_eq_of_commonRootTerminalTransport
    (endpoint.terminalState x) (endpoint.terminalState y) z
    (Classical.choice history.nonempty_commonRootTerminalTransport)

end RefinedBoundaryInsertionCompactHistory

end CartanRootedOverlapRefinedInsertionCompactHistoryReduction
end Poincare
