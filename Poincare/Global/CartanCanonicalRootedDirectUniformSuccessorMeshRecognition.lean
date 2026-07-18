import Poincare.Global.CartanRootedOverlapDirectBoundarySubdivision
import Poincare.Global.DifferentialUniformSuccessorPathStrictFactorGeometry
import Poincare.Global.CartanCanonicalFamilyComparedToGenericSuccessorRadius
import Poincare.Global.DifferentialSuccessorJointEqualityNeighborhood

/-!
# Contract-free canonical rooted transport from uniform successor geometry

The direct boundary subdivision retains the original rooted predecessor and
adds exactly one terminal edge to the overlap point.  A common parameter
refinement of the two direct boundaries is refined once more to a uniformly
small homotopy grid.  Each direct boundary factors strictly into that final
grid after its terminal edge is pinned to the grid endpoint column.

Uniform successor data and equality balls therefore transport both original
rooted terminal states to the two fine boundary rows, whose endpoint states
are equal by the automatic homotopy-grid theorem.  The resulting
`CommonRootTerminalTransport` is constructed without a
`FiniteStrictFactorBoundaryTransportContract`.
-/

noncomputable section

open Filter Metric Set
open scoped Manifold ContDiff Topology unitInterval

namespace Poincare
namespace CartanCanonicalRootedDirectUniformSuccessorMeshRecognition

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

open CartanAtlasRealizedEndpointTransport
open CartanAtlasRootedReachableEndpointTransport
open CartanCanonicalRootedEndpointAssembly
open CartanCanonicalRootedEndpointAssembly.CanonicalRootedRealizationPackage
open CartanCanonicalFamilyComparedToGenericSuccessorRadius
open CartanCanonicalFamilyComparedWholeCellRealization
open CartanCanonicalRootedUniformSuccessorMeshRecognition
open CartanRootedOverlapDirectBoundarySubdivision
open CartanRootedOverlapHomotopyGrid
open DifferentialInducedSuccessor.Chain
open DifferentialSuccessorAdjacentContinuation
open DifferentialSuccessorAdaptiveGridRefinement
open DifferentialSuccessorFiniteSubdivisionRefinement
open DifferentialSuccessorJointEqualityNeighborhood
open DifferentialSuccessorReachableChainRefinement
open DifferentialUniformSuccessorMesh
open DifferentialUniformSuccessorPathStrictFactorGeometry
open DifferentialUniformSuccessorStrictFactorGeometry

universe u

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace E M]
variable [IsManifold I ∞ M]
variable [CompactSpace M] [ConnectedSpace M]

variable {g : ClosedSmoothRiemannianMetric 3 M}

/-! ## Direct boundary transport -/

/-- Uniform successor geometry constructs a common-root terminal transport
between two direct rooted-overlap boundaries.

The two rooted subdivisions are first merged, then the common subdivision is
refined to a uniformly small homotopy grid.  The factor maps retained by those
two refinements are composed only on the original rooted prefix.  Their
terminal-pinned extensions send each added overlap edge exactly to the fine
grid's `K + 1` endpoint column. -/
theorem nonempty_commonRootTerminalTransport_of_directBoundaryGeometry
    [SimplyConnectedSpace M]
    (certificate : JointUniformSuccessorRadiusCertificate g)
    (endpoint : RootedPathContinuedEndpointFamily g)
    {x y z : M}
    (leftTerminal :
      TerminalShortPathCertificate g x z certificate.meshRadius)
    (rightTerminal :
      TerminalShortPathCertificate g y z certificate.meshRadius)
    (hleftMono : Monotone (endpoint.nodeTime x))
    (hrightMono : Monotone (endpoint.nodeTime y))
    (hleftStrict : ∀ n < endpoint.terminalIndex x,
      endpoint.nodeTime x n < endpoint.nodeTime x (n + 1))
    (hrightStrict : ∀ n < endpoint.terminalIndex y,
      endpoint.nodeTime y n < endpoint.nodeTime y (n + 1))
    (hleftCell :
      letI : MetricSpace M := g.toMetricSpace
      ∀ (n : ℕ) (a b : unitInterval),
        a ∈ Icc (endpoint.nodeTime x n) (endpoint.nodeTime x (n + 1)) →
        b ∈ Icc (endpoint.nodeTime x n) (endpoint.nodeTime x (n + 1)) →
        dist (endpoint.path x a) (endpoint.path x b) <
          certificate.meshRadius)
    (hrightCell :
      letI : MetricSpace M := g.toMetricSpace
      ∀ (n : ℕ) (a b : unitInterval),
        a ∈ Icc (endpoint.nodeTime y n) (endpoint.nodeTime y (n + 1)) →
        b ∈ Icc (endpoint.nodeTime y n) (endpoint.nodeTime y (n + 1)) →
        dist (endpoint.path y a) (endpoint.path y b) <
          certificate.meshRadius) :
    Nonempty (CommonRootTerminalTransport
      (endpoint.terminalState x) (endpoint.terminalState y) z) := by
  classical
  letI : MetricSpace M := g.toMetricSpace
  let leftSeed := directBoundarySubdivision endpoint x
  let rightSeed := directBoundarySubdivision endpoint y
  let leftLength := endpoint.terminalIndex x + 1
  let rightLength := endpoint.terminalIndex y + 1
  have hleftZero : leftSeed 0 = 0 :=
    directBoundarySubdivision_zero endpoint x
  have hrightZero : rightSeed 0 = 0 :=
    directBoundarySubdivision_zero endpoint y
  have hleftSeedMono : Monotone leftSeed :=
    directBoundarySubdivision_monotone endpoint x hleftMono
  have hrightSeedMono : Monotone rightSeed :=
    directBoundarySubdivision_monotone endpoint y hrightMono
  have hleftSeedOne : ∀ n ≥ leftLength, leftSeed n = 1 := by
    intro n hn
    exact directBoundarySubdivision_terminal endpoint x n hn
  have hrightSeedOne : ∀ n ≥ rightLength, rightSeed n = 1 := by
    intro n hn
    exact directBoundarySubdivision_terminal endpoint y n hn
  rcases exists_common_monotone_refinement
      leftSeed rightSeed hleftZero hrightZero
      hleftSeedMono hrightSeedMono leftLength rightLength
      hleftSeedOne hrightSeedOne with
    ⟨common, commonK, leftToCommon, rightToCommon,
      _hcommonK, hcommonZero, hcommonMono, hcommonOne,
      hleftToCommonMono, hrightToCommonMono,
      hleftToCommonZero, hrightToCommonZero,
      hleftToCommonBound, hrightToCommonBound,
      hleftToCommonValue, hrightToCommonValue,
      _hleftCommonBracket, _hrightCommonBracket⟩
  let homotopy := overlapHomotopy endpoint leftTerminal rightTerminal
  rcases exists_refining_homotopy_grid_adjacent_dist_lt
      g homotopy certificate.meshRadius_pos common hcommonZero
      hcommonMono commonK hcommonOne with
    ⟨fine, fineK, commonToFine, hfineK, hfineZero, hfineMono,
      hfineOne, hcommonToFineMono, hcommonToFineZero,
      hcommonToFineBound, hcommonToFineValue,
      hhorizontal, hvertical⟩
  let leftRawFactor : ℕ → ℕ := commonToFine ∘ leftToCommon
  let rightRawFactor : ℕ → ℕ := commonToFine ∘ rightToCommon
  have hleftRawZero : leftRawFactor 0 = 0 := by
    simp [leftRawFactor, Function.comp_apply, hleftToCommonZero,
      hcommonToFineZero]
  have hrightRawZero : rightRawFactor 0 = 0 := by
    simp [rightRawFactor, Function.comp_apply, hrightToCommonZero,
      hcommonToFineZero]
  have hleftRawMono : Monotone leftRawFactor :=
    hcommonToFineMono.comp hleftToCommonMono
  have hrightRawMono : Monotone rightRawFactor :=
    hcommonToFineMono.comp hrightToCommonMono
  have hleftRawValue : ∀ n : ℕ,
      fine (leftRawFactor n) = leftSeed n := by
    intro n
    simp only [leftRawFactor, Function.comp_apply,
      hcommonToFineValue, hleftToCommonValue]
  have hrightRawValue : ∀ n : ℕ,
      fine (rightRawFactor n) = rightSeed n := by
    intro n
    simp only [rightRawFactor, Function.comp_apply,
      hcommonToFineValue, hrightToCommonValue]
  have hleftRawBound : ∀ n ≤ endpoint.terminalIndex x,
      leftRawFactor n ≤ fineK := by
    intro n _hn
    exact hcommonToFineBound (leftToCommon n)
  have hrightRawBound : ∀ n ≤ endpoint.terminalIndex y,
      rightRawFactor n ≤ fineK := by
    intro n _hn
    exact hcommonToFineBound (rightToCommon n)
  let leftGamma : C(unitInterval, M) :=
    rootToOverlapPath endpoint leftTerminal
  let rightGamma : C(unitInterval, M) :=
    rootToOverlapPath endpoint rightTerminal
  let leftGeometry :
      PathStrictFactorGeometry certificate leftGamma leftSeed fine
        endpoint.root leftLength := by
    apply PathStrictFactorGeometry.ofTerminalPinnedFiniteFactor
      certificate leftGamma leftSeed fine endpoint.root
      (endpoint.terminalIndex x) fineK leftRawFactor
      hleftRawZero hleftRawMono
      (fun n _hn ↦ hleftRawValue n) hleftRawBound
    · intro n hn
      exact directBoundarySubdivision_strict endpoint x hleftStrict n (by omega)
    · exact hleftSeedMono
    · exact hfineMono
    · exact hleftSeedOne
    · exact hfineOne
    · intro j
      simpa [leftGamma, homotopy, homotopyGridRow, hfineZero] using
        hhorizontal 0 j
    · intro n a b ha hb
      exact directBoundarySubdivision_cellDiameter endpoint leftTerminal
        hleftCell n a b ha hb
    · change endpoint.root.anchor =
        directBoundaryNodes endpoint leftTerminal 0
      exact (directBoundaryNodes_zero endpoint leftTerminal).symm
  let rightGeometry :
      PathStrictFactorGeometry certificate rightGamma rightSeed fine
        endpoint.root rightLength := by
    apply PathStrictFactorGeometry.ofTerminalPinnedFiniteFactor
      certificate rightGamma rightSeed fine endpoint.root
      (endpoint.terminalIndex y) fineK rightRawFactor
      hrightRawZero hrightRawMono
      (fun n _hn ↦ hrightRawValue n) hrightRawBound
    · intro n hn
      exact directBoundarySubdivision_strict endpoint y hrightStrict n (by omega)
    · exact hrightSeedMono
    · exact hfineMono
    · exact hrightSeedOne
    · exact hfineOne
    · intro j
      simpa [rightGamma, homotopy, homotopyGridRow,
        hfineOne (fineK + 1) (by omega)] using
          hhorizontal (fineK + 1) j
    · intro n a b ha hb
      exact directBoundarySubdivision_cellDiameter endpoint rightTerminal
        hrightCell n a b ha hb
    · change endpoint.root.anchor =
        directBoundaryNodes endpoint rightTerminal 0
      exact (directBoundaryNodes_zero endpoint rightTerminal).symm
  have hleftFactorTerminal :
      leftGeometry.factor leftLength = fineK + 1 := by
    simp [leftGeometry, leftLength,
      PathStrictFactorGeometry.ofTerminalPinnedFiniteFactor]
  have hrightFactorTerminal :
      rightGeometry.factor rightLength = fineK + 1 := by
    simp [rightGeometry, rightLength,
      PathStrictFactorGeometry.ofTerminalPinnedFiniteFactor]
  let leftUniform := leftGeometry.toUniformStrictFactorGeometry
  let rightUniform := rightGeometry.toUniformStrictFactorGeometry
  have hleftCoarseFine :
      leftUniform.coarseChain.state leftLength =
        leftUniform.refinedChain.state (fineK + 1) := by
    have h := leftUniform.coarse_state_eq_refined_state
    have hfactor : leftUniform.factor leftLength = fineK + 1 :=
      hleftFactorTerminal
    rw [hfactor] at h
    exact h
  have hrightCoarseFine :
      rightUniform.coarseChain.state rightLength =
        rightUniform.refinedChain.state (fineK + 1) := by
    have h := rightUniform.coarse_state_eq_refined_state
    have hfactor : rightUniform.factor rightLength = fineK + 1 :=
      hrightFactorTerminal
    rw [hfactor] at h
    exact h
  let leftRow := certificate.realizedRowChain homotopy endpoint.root
    fine fineK hfineZero hfineOne hhorizontal rfl 0
  let rightRow := certificate.realizedRowChain homotopy endpoint.root
    fine fineK hfineZero hfineOne hhorizontal rfl (fineK + 1)
  have hleftRefinedRow :
      leftUniform.refinedChain.state (fineK + 1) =
        leftRow.state (fineK + 1) := by
    apply ReachableChain.state_eq_of_prefix_nodes
    intro j hj
    simp [leftGamma, homotopy,
      homotopyGridRow, hfineZero]
  have hrightRefinedRow :
      rightUniform.refinedChain.state (fineK + 1) =
        rightRow.state (fineK + 1) := by
    apply ReachableChain.state_eq_of_prefix_nodes
    intro j hj
    simp [rightGamma, homotopy,
      homotopyGridRow, hfineOne (fineK + 1) (by omega)]
  have hgrid : leftRow.state (fineK + 1) =
      rightRow.state (fineK + 1) := by
    have h := certificate.boundaryEndpointEq_of_mesh_small
      homotopy endpoint.root rfl fine fineK hfineZero hfineOne
        hhorizontal hvertical
    change leftRow.state (fineK + 1) = rightRow.state (fineK + 1) at h
    exact h
  refine ⟨
    { root := endpoint.root
      leftNodes := directBoundaryNodes endpoint leftTerminal
      rightNodes := directBoundaryNodes endpoint rightTerminal
      leftChain := leftUniform.coarseChain
      rightChain := rightUniform.coarseChain
      leftIndex := endpoint.terminalIndex x
      rightIndex := endpoint.terminalIndex y
      left_predecessor := ?_
      right_predecessor := ?_
      left_next_node := ?_
      right_next_node := ?_
      terminal_eq := ?_ }⟩
  · exact reachableChain_state_predecessor_eq_terminalState
      endpoint leftTerminal leftUniform.coarseChain
  · exact reachableChain_state_predecessor_eq_terminalState
      endpoint rightTerminal rightUniform.coarseChain
  · exact directBoundaryNodes_terminal endpoint leftTerminal
      leftLength le_rfl
  · exact directBoundaryNodes_terminal endpoint rightTerminal
      rightLength le_rfl
  · change leftUniform.coarseChain.state leftLength =
      rightUniform.coarseChain.state rightLength
    exact hleftCoarseFine.trans
      (hleftRefinedRow.trans
        (hgrid.trans
          (hrightRefinedRow.symm.trans hrightCoarseFine.symm)))

/-! ## Canonical package and recognition assembly -/

/-- A compared rooted realization with whole-cell mesh control produces the
restricted compatible Cartan atlas directly from the two uniform successor
radii.  No per-overlap transport contract or realized grid is retained in the
result. -/
noncomputable def
    restrictedCompatibleCartanAtlasData3_of_directBoundaryGeometry
    [SimplyConnectedSpace M]
    (certificate : JointUniformSuccessorRadiusCertificate g)
    {skeleton : CartanAtlasRootedPathSkeleton.RootedCartanPathSkeleton g}
    (package : CanonicalRootedRealizationPackage skeleton)
    (hnodeMono : ∀ x : M, Monotone (package.endpoint.nodeTime x))
    (hnodeStrict : ∀ x : M,
      ∀ n < package.endpoint.terminalIndex x,
        package.endpoint.nodeTime x n <
          package.endpoint.nodeTime x (n + 1))
    (hwholeCell :
      letI : MetricSpace M := g.toMetricSpace
      ∀ (x : M) (n : ℕ) (a b : unitInterval),
        a ∈ Icc (package.endpoint.nodeTime x n)
          (package.endpoint.nodeTime x (n + 1)) →
        b ∈ Icc (package.endpoint.nodeTime x n)
          (package.endpoint.nodeTime x (n + 1)) →
        dist (package.endpoint.path x a) (package.endpoint.path x b) <
          certificate.meshRadius) :
    UnitRecognitionNext.RestrictedCompatibleCartanAtlasData3 g where
  target := package.endpoint.target
  alignment := package.endpoint.alignment
  domain := CartanTerminalShortPathScheduleFree.scheduleFreeTerminalRestrictedDomain
    package certificate.meshRadius_pos
  isOpen_domain :=
    CartanTerminalShortPathScheduleFree.isOpen_scheduleFreeTerminalRestrictedDomain
      package certificate.meshRadius_pos
  anchor_mem_domain :=
    CartanTerminalShortPathScheduleFree.anchor_mem_scheduleFreeTerminalRestrictedDomain
      package certificate.meshRadius_pos
  domain_subset_source := by
    intro x z hz
    have hterminal :
        z ∈ (package.endpoint.terminalState x).germ.source :=
      CartanTerminalShortPathScheduleFree.scheduleFreeTerminalRestrictedDomain_subset_source
        package certificate.meshRadius_pos x hz
    have hx := package.endpoint_anchoredFamilyState_eq_terminalState x
    change z ∈
      (CartanLocalRigidity.anchoredFamilyState g package.endpoint.target
        package.endpoint.alignment x).germ.source
    simpa only [hx] using hterminal
  compatible := by
    intro x y z hz
    let leftTerminal := derivedTerminalPath package certificate.meshRadius_pos hz.1
    let rightTerminal := derivedTerminalPath package certificate.meshRadius_pos hz.2
    let transport : CommonRootTerminalTransport
        (package.endpoint.terminalState x)
        (package.endpoint.terminalState y) z :=
      Classical.choice
        (nonempty_commonRootTerminalTransport_of_directBoundaryGeometry
          certificate package.endpoint leftTerminal rightTerminal
          (hnodeMono x) (hnodeMono y) (hnodeStrict x) (hnodeStrict y)
          (hwholeCell x) (hwholeCell y))
    have hvalue := germ_value_eq_of_commonRootTerminalTransport
      (package.endpoint.terminalState x)
      (package.endpoint.terminalState y) z transport
    have hx := package.endpoint_anchoredFamilyState_eq_terminalState x
    have hy := package.endpoint_anchoredFamilyState_eq_terminalState y
    change
      (CartanLocalRigidity.anchoredFamilyState g package.endpoint.target
          package.endpoint.alignment x).germ z =
        (CartanLocalRigidity.anchoredFamilyState g package.endpoint.target
          package.endpoint.alignment y).germ z
    simpa only [hx, hy] using hvalue

/-- Canonical compared-successor stability and joint actual-data equality
stability now imply unit-curvature sphere recognition with no completion
provider.

The compared neighborhood constructs a whole-cell controlled rooted
realization at the joint mesh radius.  The equality neighborhood supplies the
state-uniform equality ball.  The preceding direct-boundary construction then
discharges every overlap transport internally. -/
theorem unitConstantCurvatureSphereRecognition3_of_canonicalComparedNeighborhood_jointEqualityNeighborhood
    [SecondCountableTopology M] [SimplyConnectedSpace M]
    (comparedStability : ∀ (g : ClosedSmoothRiemannianMetric 3 M),
      HasConstantSectionalCurvature3 g 1 →
        CartanCanonicalFamilyProvenanceRootedAssembly.UniversalComparedSuccessorLocus g ∈
          nhdsSet
            (CartanTargetExponential.successorParameterDiagonal (M := M)))
    (equalityStability : ∀ (g : ClosedSmoothRiemannianMetric 3 M),
      HasConstantSectionalCurvature3 g 1 →
        UniversalSuccessorEqualityNeighborhood g) :
    UnitConstantCurvatureSphereRecognition3 M := by
  apply
    RoundSphereSimpleConnected.unitConstantCurvatureSphereRecognition3_of_restrictedCompatibleCartanAtlas
  intro g hcurv
  let comparedNeighborhood := comparedStability g hcurv
  let successor :=
    CartanCanonicalRootedReparameterizedUniformRadiusGridAssembly.uniformGenericSuccessorRadiusCertificateOfNeighborhood
      g
      (universalSuccessorDataNeighborhood_of_comparedNeighborhood
        comparedNeighborhood)
  rcases exists_uniformSuccessorEqOnBall_of_jointNeighborhood
      g (equalityStability g hcurv) with
    ⟨eta, heta, heq⟩
  let certificate : JointUniformSuccessorRadiusCertificate g :=
    { successorData := successor
      equalityRadius := eta
      equalityRadius_pos := heta
      successorEqOnBall := heq }
  let skeleton := Classical.choice
    (CartanAtlasRootedPathSkeleton.nonempty_rootedCartanPathSkeleton g)
  rcases
      exists_comparedRootedRealization_with_prescribed_wholeCellMesh_of_neighborhood
        skeleton comparedNeighborhood certificate.meshRadius
          certificate.meshRadius_pos with
    ⟨realization, comparison, _hterminalPos, hmono, hstrict,
      _heventual, hwhole⟩
  let package : CanonicalRootedRealizationPackage skeleton :=
    { realization := realization
      comparison := comparison }
  have hendpointMono : ∀ x : M,
      Monotone (package.endpoint.nodeTime x) := by
    exact hmono
  have hendpointStrict : ∀ x : M,
      ∀ n < package.endpoint.terminalIndex x,
        package.endpoint.nodeTime x n <
          package.endpoint.nodeTime x (n + 1) := by
    exact hstrict
  have hendpointWhole :
      letI : MetricSpace M := g.toMetricSpace
      ∀ (x : M) (n : ℕ) (a b : unitInterval),
        a ∈ Icc (package.endpoint.nodeTime x n)
          (package.endpoint.nodeTime x (n + 1)) →
        b ∈ Icc (package.endpoint.nodeTime x n)
          (package.endpoint.nodeTime x (n + 1)) →
        dist (package.endpoint.path x a) (package.endpoint.path x b) <
          certificate.meshRadius := by
    exact hwhole
  exact ⟨restrictedCompatibleCartanAtlasData3_of_directBoundaryGeometry
    certificate package hendpointMono hendpointStrict hendpointWhole⟩

end CartanCanonicalRootedDirectUniformSuccessorMeshRecognition
end Poincare
