import Poincare.Global.CartanCanonicalRootedReparameterizedUniformRadiusGridAssembly
import Poincare.Global.DifferentialUniformSuccessorMesh
import Poincare.Global.DifferentialSuccessorAdaptiveGridRefinement
import Poincare.Global.DifferentialSuccessorFiniteRealizedHomotopyGrid

/-!
# Canonical rooted coherence from state-uniform successor balls

Two genuinely uniform inputs close the geometric/recursive mesh loop:

* one positive radius supplies differential-successor data at every reached
  state whose next anchor is sufficiently close; and
* one positive radius gives successor-germ equality on a ball, uniformly over
  every Cartan state and every actual successor datum.

Their common mesh radius chooses a homotopy subdivision before any successor
history is realized.  All row, rung, and cross-cell data are then constructed
internally, and the state-uniform equality ball proves the boundary endpoint
equality.  No realized grid data are stored.

For canonical rooted endpoints, one honest boundary remains: a new adaptive
subdivision must be transported back to the already fixed rooted terminal
states.  This file exposes that finite strict-factor provenance as one
proof-bearing transport contract.  It does not retain per-overlap half-radius
or post-realization mesh-feedback assumptions.
-/

noncomputable section

open Metric Set
open scoped Manifold ContDiff Topology unitInterval

namespace Poincare
namespace CartanCanonicalRootedUniformSuccessorMeshRecognition

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

open CartanAtlasRealizedEndpointTransport
open CartanAtlasRootedPathCurvatureSuccessorRadius
open CartanAtlasRootedPathSkeleton
open CartanCanonicalRootedEndpointAssembly
open CartanCanonicalRootedEndpointAssembly.CanonicalRootedRealizationPackage
open CartanCanonicalRootedReparameterizedUniformRadiusGridAssembly
open CartanRootedOverlapReparameterizedBoundary
open CartanTerminalShortPathScheduleFree
open DifferentialInducedSuccessor
open DifferentialInducedSuccessor.Chain
open DifferentialSuccessorAdjacentContinuation
open DifferentialSuccessorAdaptiveHomotopyGrid
open DifferentialSuccessorAdaptiveMeshCoordinates
open DifferentialSuccessorFiniteRealizedHomotopyGrid
open DifferentialUniformSuccessorMesh

universe u

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace E M]
variable [IsManifold I ∞ M]
variable [CompactSpace M] [ConnectedSpace M]

variable {g : ClosedSmoothRiemannianMetric 3 M}

/-- The two uniform successor radii needed by the automatic realized-grid
argument. -/
structure JointUniformSuccessorRadiusCertificate
    (g : ClosedSmoothRiemannianMetric 3 M) where
  successorData : UniformGenericSuccessorRadiusCertificate g
  equalityRadius : ℝ
  equalityRadius_pos : 0 < equalityRadius
  successorEqOnBall : UniformSuccessorEqOnBall g equalityRadius

namespace JointUniformSuccessorRadiusCertificate

/-- A mesh radius small enough for both individual edges and the diagonal
data query used at an opposite cell vertex. -/
def meshRadius (certificate : JointUniformSuccessorRadiusCertificate g) : ℝ :=
  min (certificate.successorData.radius / 2) certificate.equalityRadius

theorem meshRadius_pos
    (certificate : JointUniformSuccessorRadiusCertificate g) :
    0 < certificate.meshRadius := by
  exact lt_min (half_pos certificate.successorData.radius_pos)
    certificate.equalityRadius_pos

theorem meshRadius_lt_dataRadius
    (certificate : JointUniformSuccessorRadiusCertificate g) :
    certificate.meshRadius < certificate.successorData.radius := by
  exact (min_le_left _ _).trans_lt
    (half_lt_self certificate.successorData.radius_pos)

theorem meshRadius_le_half_dataRadius
    (certificate : JointUniformSuccessorRadiusCertificate g) :
    certificate.meshRadius ≤ certificate.successorData.radius / 2 :=
  min_le_left _ _

theorem meshRadius_le_equalityRadius
    (certificate : JointUniformSuccessorRadiusCertificate g) :
    certificate.meshRadius ≤ certificate.equalityRadius :=
  min_le_right _ _

/-- The reachable chain on one selected homotopy row.  Its successor data are
computed only at actually reached states; after the terminal subdivision
index, zero successors extend the chain along the stationary row. -/
noncomputable def realizedRowChain
    (certificate : JointUniformSuccessorRadiusCertificate g)
    {x y : M} {p₀ p₁ : Path x y} (F : p₀.Homotopy p₁)
    (initial : CartanChain.ChainState g)
    (t : ℕ → unitInterval) (k : ℕ)
    (htzero : t 0 = 0) (htone : ∀ n ≥ k, t n = 1)
    (hhorizontal :
      letI : MetricSpace M := g.toMetricSpace
      ∀ n m : ℕ,
        dist (homotopyGridRow F t n (m + 1))
          (homotopyGridRow F t n m) < certificate.meshRadius)
    (hinitial : initial.anchor = x) (m : ℕ) :
    ReachableChain (homotopyGridRow F t m) initial := by
  letI : MetricSpace M := g.toMetricSpace
  apply
    CartanAtlasRootedPathAdaptiveMeshRealization.reachableChain_of_finite_anchored_step_supply
      (homotopyGridRow F t m) initial k
  · simpa [homotopyGridRow, htzero] using hinitial
  · intro n hn
    simp only [homotopyGridRow, htone n hn, htone k le_rfl]
  · intro i s hs
    apply certificate.successorData.data s
    rw [hs]
    exact (hhorizontal m i).trans certificate.meshRadius_lt_dataRadius

/-- The proposition that the two boundary rows selected by one fine grid
reach the same terminal state. -/
def BoundaryEndpointEq
    (certificate : JointUniformSuccessorRadiusCertificate g)
    {x y : M} {p₀ p₁ : Path x y} (F : p₀.Homotopy p₁)
    (initial : CartanChain.ChainState g)
    (t : ℕ → unitInterval) (k : ℕ)
    (htzero : t 0 = 0) (htone : ∀ n ≥ k, t n = 1)
    (hhorizontal :
      letI : MetricSpace M := g.toMetricSpace
      ∀ n m : ℕ,
        dist (homotopyGridRow F t n (m + 1))
          (homotopyGridRow F t n m) < certificate.meshRadius)
    (hinitial : initial.anchor = x) : Prop :=
  (certificate.realizedRowChain F initial t k htzero htone
      hhorizontal hinitial 0).state (k + 1) =
    (certificate.realizedRowChain F initial t k htzero htone
      hhorizontal hinitial (k + 1)).state (k + 1)

/-- Fixed-grid endpoint equality from the two state-uniform radii.

All realized rows and cell data in the proof are local definitions.  The
public conclusion mentions only the two canonically computed boundary-row
states. -/
theorem boundaryEndpointEq_of_mesh_small
    (certificate : JointUniformSuccessorRadiusCertificate g)
    {x y : M} {p₀ p₁ : Path x y} (F : p₀.Homotopy p₁)
    (initial : CartanChain.ChainState g) (hinitial : initial.anchor = x)
    (t : ℕ → unitInterval) (k : ℕ)
    (htzero : t 0 = 0) (htone : ∀ n ≥ k, t n = 1)
    (hhorizontal :
      letI : MetricSpace M := g.toMetricSpace
      ∀ n m : ℕ,
        dist (homotopyGridRow F t n (m + 1))
          (homotopyGridRow F t n m) < certificate.meshRadius)
    (hvertical :
      letI : MetricSpace M := g.toMetricSpace
      ∀ n m : ℕ,
        dist (homotopyGridRow F t (n + 1) (m + 1))
          (homotopyGridRow F t n (m + 1)) < certificate.meshRadius) :
    certificate.BoundaryEndpointEq F initial t k htzero htone
      hhorizontal hinitial := by
  classical
  letI : MetricSpace M := g.toMetricSpace
  let rowChain : ∀ m : Fin (k + 2),
      ReachableChain (homotopyGridRow F t m) initial := fun m ↦
    certificate.realizedRowChain F initial t k htzero htone
      hhorizontal hinitial m
  have hroot : ∀ m : ℕ,
      initial.anchor = homotopyGridRow F t m 0 := by
    intro m
    simpa [homotopyGridRow, htzero] using hinitial
  let rungData : ∀ m : Fin (k + 1), ∀ j : Fin (k + 1),
      Data ((rowChain m.castSucc).state (j + 1))
        (homotopyGridRow F t (m + 1) (j + 1)) := by
    intro m j
    apply Classical.choice
    apply certificate.successorData.data
    rw [(rowChain m.castSucc).state_anchor_eq_node (hroot m) (j + 1)]
    exact (hvertical m j).trans certificate.meshRadius_lt_dataRadius
  let bottomAtUpper : ∀ m : Fin (k + 1), ∀ j : Fin (k + 1),
      Data ((rowChain m.castSucc).state j)
        (homotopyGridRow F t (m + 1) (j + 1)) := by
    intro m j
    apply Classical.choice
    apply certificate.successorData.data
    rw [(rowChain m.castSucc).state_anchor_eq_node (hroot m) j]
    calc
      dist (homotopyGridRow F t (m + 1) (j + 1))
          (homotopyGridRow F t m j) ≤
          dist (homotopyGridRow F t (m + 1) (j + 1))
              (homotopyGridRow F t m (j + 1)) +
            dist (homotopyGridRow F t m (j + 1))
              (homotopyGridRow F t m j) :=
        dist_triangle _ _ _
      _ < certificate.meshRadius + certificate.meshRadius :=
        add_lt_add (hvertical m j) (hhorizontal m j)
      _ ≤ certificate.successorData.radius / 2 +
          (certificate.successorData.radius / 2) :=
        add_le_add certificate.meshRadius_le_half_dataRadius
          certificate.meshRadius_le_half_dataRadius
      _ = certificate.successorData.radius := by ring
  let rungAtNext : ∀ m : Fin (k + 1), ∀ j : Fin k,
      Data (rungData m j.castSucc).successor
        (homotopyGridRow F t (m + 1) (j + 2)) := by
    intro m j
    apply Classical.choice
    apply certificate.successorData.data
    rw [(rungData m j.castSucc).successor_anchor]
    exact (hhorizontal (m + 1) (j + 1)).trans
      certificate.meshRadius_lt_dataRadius
  have hEq := certificate.successorEqOnBall
  change ∀ (s : CartanChain.ChainState g) {z : M}
      (d : Data s z), dist z s.anchor < certificate.equalityRadius →
        EqOn s.germ d.successor.germ
          (Metric.ball z certificate.equalityRadius) at hEq
  have hterminal :
      (rowChain 0).state (k + 1) =
        (rowChain (Fin.last (k + 1))).state (k + 1) := by
    apply
      reachableHomotopyGridChains_endpoint_eq_of_finite_common_metricBall_patches
        F initial t k htone rowChain rungData bottomAtUpper rungAtNext
          (fun _ ↦ certificate.equalityRadius)
    · intro m j
      rw [(rowChain m.castSucc).state_succ j]
      apply hEq
      rw [(rowChain m.castSucc).state_anchor_eq_node (hroot m) j]
      exact (hhorizontal m j).trans_le
        certificate.meshRadius_le_equalityRadius
    · intro m j
      rw [Metric.mem_ball]
      exact (hvertical m j).trans_le
        certificate.meshRadius_le_equalityRadius
    · intro m j
      apply hEq
      rw [(rowChain m.castSucc).state_anchor_eq_node (hroot m) (j + 1)]
      exact (hvertical m j).trans_le
        certificate.meshRadius_le_equalityRadius
    · intro m j
      rw [Metric.mem_ball]
      exact (hhorizontal (m + 1) (j + 1)).trans_le
        certificate.meshRadius_le_equalityRadius
  simpa [BoundaryEndpointEq, rowChain] using hterminal

/-- A finite homotopy endpoint certificate containing no realized row, rung,
or cross data. -/
structure UniformHomotopyEndpointCertificate
    (certificate : JointUniformSuccessorRadiusCertificate g)
    {x y : M} {p₀ p₁ : Path x y} (F : p₀.Homotopy p₁)
    (initial : CartanChain.ChainState g) (hinitial : initial.anchor = x) where
  subdivision : ℕ → unitInterval
  gridSize : ℕ
  subdivision_zero : subdivision 0 = 0
  subdivision_monotone : Monotone subdivision
  subdivision_terminal : ∀ n ≥ gridSize, subdivision n = 1
  horizontal_small :
    letI : MetricSpace M := g.toMetricSpace
    ∀ n m : ℕ,
      dist (homotopyGridRow F subdivision n (m + 1))
        (homotopyGridRow F subdivision n m) < certificate.meshRadius
  vertical_small :
    letI : MetricSpace M := g.toMetricSpace
    ∀ n m : ℕ,
      dist (homotopyGridRow F subdivision (n + 1) (m + 1))
        (homotopyGridRow F subdivision n (m + 1)) < certificate.meshRadius
  endpoint_eq : certificate.BoundaryEndpointEq F initial subdivision gridSize
    subdivision_zero subdivision_terminal horizontal_small hinitial

/-- Compactness of the homotopy square selects a fine grid, and the joint
uniform successor certificate automatically supplies its endpoint equality. -/
theorem nonempty_uniformHomotopyEndpointCertificate
    (certificate : JointUniformSuccessorRadiusCertificate g)
    {x y : M} {p₀ p₁ : Path x y} (F : p₀.Homotopy p₁)
    (initial : CartanChain.ChainState g) (hinitial : initial.anchor = x) :
    Nonempty (UniformHomotopyEndpointCertificate certificate F initial hinitial) := by
  letI : MetricSpace M := g.toMetricSpace
  rcases exists_homotopy_grid_adjacent_dist_lt
      g F certificate.meshRadius_pos with
    ⟨t, k, htzero, htmono, htone, hhorizontal, hvertical⟩
  refine ⟨{
    subdivision := t
    gridSize := k
    subdivision_zero := htzero
    subdivision_monotone := htmono
    subdivision_terminal := htone
    horizontal_small := hhorizontal
    vertical_small := hvertical
    endpoint_eq := ?_
  }⟩
  exact certificate.boundaryEndpointEq_of_mesh_small F initial hinitial
    t k htzero htone hhorizontal hvertical

end JointUniformSuccessorRadiusCertificate

/-- Assemble the joint uniform certificate from the generic diagonal-
neighborhood radius and an independently supplied state-uniform equality
ball. -/
noncomputable def jointUniformSuccessorRadiusCertificateOfNeighborhood
    (g : ClosedSmoothRiemannianMetric 3 M)
    (hneighborhood : UniversalSuccessorDataNeighborhood g)
    (eta : ℝ) (heta : 0 < eta)
    (heq : UniformSuccessorEqOnBall g eta) :
    JointUniformSuccessorRadiusCertificate g where
  successorData :=
    uniformGenericSuccessorRadiusCertificateOfNeighborhood g hneighborhood
  equalityRadius := eta
  equalityRadius_pos := heta
  successorEqOnBall := heq

namespace CanonicalRootedRealizationPackage

variable [SimplyConnectedSpace M]
variable {skeleton : RootedCartanPathSkeleton g}

/-- One common predecessor bound used only to define the two reparameterized
root-to-overlap boundary paths. -/
def uniformOverlapPredecessor
    (package : CanonicalRootedRealizationPackage skeleton)
    (x y : M) : ℕ :=
  max (package.endpoint.terminalIndex x) (package.endpoint.terminalIndex y)

/-- The canonical homotopy between the two reparameterized root-to-overlap
paths at a schedule-free overlap point. -/
noncomputable def uniformOverlapHomotopy
    (package : CanonicalRootedRealizationPackage skeleton)
    {mesh : ℝ} (hmesh : 0 < mesh)
    (x y z : M)
    (hz : z ∈
      scheduleFreeTerminalRestrictedDomain package hmesh x ∩
        scheduleFreeTerminalRestrictedDomain package hmesh y) :=
  reparameterizedOverlapHomotopy package.endpoint
    (derivedTerminalPath package hmesh hz.1)
    (derivedTerminalPath package hmesh hz.2)
    (uniformOverlapPredecessor package x y)

/-- The automatically selected fine-grid endpoint certificate for one
canonical rooted overlap. -/
noncomputable def automaticUniformOverlapEndpointCertificate
    (certificate : JointUniformSuccessorRadiusCertificate g)
    (package : CanonicalRootedRealizationPackage skeleton)
    {mesh : ℝ} (hmesh : 0 < mesh)
    (x y z : M)
    (hz : z ∈
      scheduleFreeTerminalRestrictedDomain package hmesh x ∩
        scheduleFreeTerminalRestrictedDomain package hmesh y) :
    JointUniformSuccessorRadiusCertificate.UniformHomotopyEndpointCertificate
      certificate (uniformOverlapHomotopy package hmesh x y z hz)
        package.endpoint.root rfl :=
  Classical.choice
    (certificate.nonempty_uniformHomotopyEndpointCertificate
      (uniformOverlapHomotopy package hmesh x y z hz)
      package.endpoint.root rfl)

/-- The endpoint-equality proposition carried by the automatically selected
fine overlap grid. -/
def AutomaticUniformOverlapBoundaryEndpointEq
    (certificate : JointUniformSuccessorRadiusCertificate g)
    (package : CanonicalRootedRealizationPackage skeleton)
    {mesh : ℝ} (hmesh : 0 < mesh)
    (x y z : M)
    (hz : z ∈
      scheduleFreeTerminalRestrictedDomain package hmesh x ∩
        scheduleFreeTerminalRestrictedDomain package hmesh y) : Prop :=
  let automatic :=
    automaticUniformOverlapEndpointCertificate certificate package hmesh
      x y z hz
  certificate.BoundaryEndpointEq
    (uniformOverlapHomotopy package hmesh x y z hz)
    package.endpoint.root automatic.subdivision automatic.gridSize
    automatic.subdivision_zero automatic.subdivision_terminal
    automatic.horizontal_small rfl

/-- The automatic grid really supplies its advertised boundary endpoint
equality. -/
theorem automaticUniformOverlapBoundaryEndpointEq
    (certificate : JointUniformSuccessorRadiusCertificate g)
    (package : CanonicalRootedRealizationPackage skeleton)
    {mesh : ℝ} (hmesh : 0 < mesh)
    (x y z : M)
    (hz : z ∈
      scheduleFreeTerminalRestrictedDomain package hmesh x ∩
        scheduleFreeTerminalRestrictedDomain package hmesh y) :
    AutomaticUniformOverlapBoundaryEndpointEq certificate package hmesh
      x y z hz := by
  exact
    (automaticUniformOverlapEndpointCertificate certificate package hmesh
      x y z hz).endpoint_eq

/-- The sole remaining canonical-boundary provenance contract.

The uniform radii automatically prove equality of the two newly refined
boundary endpoint states.  A strict-factor insertion argument must transport
that equality back to the two previously fixed rooted terminal states and
produce the standard common-root terminal transport.  The contract stores no
row chain, rung datum, cross-cell datum, half-radius estimate, or mesh-feedback
bound. -/
structure FiniteStrictFactorBoundaryTransportContract
    (certificate : JointUniformSuccessorRadiusCertificate g)
    (package : CanonicalRootedRealizationPackage skeleton)
    {mesh : ℝ} (hmesh : 0 < mesh)
    (x y z : M)
    (hz : z ∈
      scheduleFreeTerminalRestrictedDomain package hmesh x ∩
        scheduleFreeTerminalRestrictedDomain package hmesh y) where
  transport :
    AutomaticUniformOverlapBoundaryEndpointEq certificate package hmesh
        x y z hz →
      CommonRootStrictFactorTransport
        (package.endpoint.terminalState x)
        (package.endpoint.terminalState y) z

/-- Canonical rooted overlap coherence with all mesh construction discharged
by the joint uniform radii.  Its only field is the finite strict-factor
boundary provenance contract. -/
structure UniformSuccessorRootedOverlapCoherence
    (certificate : JointUniformSuccessorRadiusCertificate g)
    (package : CanonicalRootedRealizationPackage skeleton)
    {mesh : ℝ} (hmesh : 0 < mesh) where
  boundaryTransport : ∀ x y z : M,
    ∀ hz : z ∈
      scheduleFreeTerminalRestrictedDomain package hmesh x ∩
        scheduleFreeTerminalRestrictedDomain package hmesh y,
      FiniteStrictFactorBoundaryTransportContract
        certificate package hmesh x y z hz

/-- The uniform-successor coherence constructs the restricted compatible
Cartan atlas without retaining any realized grid. -/
noncomputable def
    UniformSuccessorRootedOverlapCoherence.toRestrictedCompatibleCartanAtlasData3
    (certificate : JointUniformSuccessorRadiusCertificate g)
    (package : CanonicalRootedRealizationPackage skeleton)
    {mesh : ℝ} (hmesh : 0 < mesh)
    (coherence : UniformSuccessorRootedOverlapCoherence
      certificate package hmesh) :
    UnitRecognitionNext.RestrictedCompatibleCartanAtlasData3 g where
  target := package.endpoint.target
  alignment := package.endpoint.alignment
  domain := scheduleFreeTerminalRestrictedDomain package hmesh
  isOpen_domain :=
    isOpen_scheduleFreeTerminalRestrictedDomain package hmesh
  anchor_mem_domain :=
    anchor_mem_scheduleFreeTerminalRestrictedDomain package hmesh
  domain_subset_source := by
    intro x z hz
    have hterminal :
        z ∈ (package.endpoint.terminalState x).germ.source :=
      scheduleFreeTerminalRestrictedDomain_subset_source package hmesh x hz
    have hx := package.endpoint_anchoredFamilyState_eq_terminalState x
    change z ∈
      (CartanLocalRigidity.anchoredFamilyState g package.endpoint.target
        package.endpoint.alignment x).germ.source
    simpa only [hx] using hterminal
  compatible := by
    intro x y z hz
    let boundary := coherence.boundaryTransport x y z hz
    have hstrict : CommonRootStrictFactorTransport
        (package.endpoint.terminalState x)
        (package.endpoint.terminalState y) z :=
      boundary.transport
        (automaticUniformOverlapBoundaryEndpointEq certificate package hmesh
          x y z hz)
    have htransport : CommonRootTerminalTransport
        (package.endpoint.terminalState x)
        (package.endpoint.terminalState y) z :=
      hstrict.toTerminalTransport
    have hvalue := germ_value_eq_of_commonRootTerminalTransport
      (package.endpoint.terminalState x)
      (package.endpoint.terminalState y) z htransport
    have hx := package.endpoint_anchoredFamilyState_eq_terminalState x
    have hy := package.endpoint_anchoredFamilyState_eq_terminalState y
    change
      (CartanLocalRigidity.anchoredFamilyState g package.endpoint.target
          package.endpoint.alignment x).germ z =
        (CartanLocalRigidity.anchoredFamilyState g package.endpoint.target
          package.endpoint.alignment y).germ z
    simpa only [hx, hy] using hvalue

end CanonicalRootedRealizationPackage

/-- Unit-curvature recognition from a uniform generic successor-data
neighborhood, a genuinely state-uniform successor equality radius, and the
single remaining finite strict-factor boundary transport contract.

In particular, the completion provider has no per-overlap half-radius field,
no realized grid, and no post-realization curvature-radius feedback premise. -/
theorem unitConstantCurvatureSphereRecognition3_of_canonicalRooted_uniformSuccessorData_uniformEqOnBall_strictFactorBoundaryTransport
    [SecondCountableTopology M] [SimplyConnectedSpace M]
    (jointStability : ∀ (g : ClosedSmoothRiemannianMetric 3 M),
      HasConstantSectionalCurvature3 g 1 →
        UniversalSuccessorDataNeighborhood g)
    (uniformEquality : ∀ (g : ClosedSmoothRiemannianMetric 3 M),
      HasConstantSectionalCurvature3 g 1 →
        ∃ eta > (0 : ℝ), UniformSuccessorEqOnBall g eta)
    (completion : ∀ (g : ClosedSmoothRiemannianMetric 3 M),
      ∀ _hcurv : HasConstantSectionalCurvature3 g 1,
      ∀ (successor : UniformGenericSuccessorRadiusCertificate g),
      ∀ (eta : ℝ), ∀ (heta : 0 < eta),
      ∀ (heq : UniformSuccessorEqOnBall g eta),
        ∃ skeleton : RootedCartanPathSkeleton g,
          ∃ package : CanonicalRootedRealizationPackage skeleton,
            ∃ mesh : ℝ,
              ∃ hmesh : 0 < mesh,
                Nonempty
                  (CanonicalRootedRealizationPackage.UniformSuccessorRootedOverlapCoherence
                    { successorData := successor
                      equalityRadius := eta
                      equalityRadius_pos := heta
                      successorEqOnBall := heq }
                    package hmesh)) :
    UnitConstantCurvatureSphereRecognition3 M := by
  apply
    RoundSphereSimpleConnected.unitConstantCurvatureSphereRecognition3_of_restrictedCompatibleCartanAtlas
  intro g hcurv
  let successor :=
    uniformGenericSuccessorRadiusCertificateOfNeighborhood g
      (jointStability g hcurv)
  rcases uniformEquality g hcurv with ⟨eta, heta, heq⟩
  rcases completion g hcurv successor eta heta heq with
    ⟨skeleton, package, mesh, hmesh, coherence⟩
  rcases coherence with ⟨coherence⟩
  let certificate : JointUniformSuccessorRadiusCertificate g :=
    { successorData := successor
      equalityRadius := eta
      equalityRadius_pos := heta
      successorEqOnBall := heq }
  exact
    ⟨coherence.toRestrictedCompatibleCartanAtlasData3
      certificate package hmesh⟩

end CartanCanonicalRootedUniformSuccessorMeshRecognition
end Poincare
