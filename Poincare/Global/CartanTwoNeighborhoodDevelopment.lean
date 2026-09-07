import Poincare.Global.CartanCanonicalRootedDirectGenericNeighborhoodRecognition
import Poincare.Global.RoundSphereSimpleConnected

/-!
# The two-neighborhood boundary of the Cartan development

This module records the smallest currently known set of open hypotheses from
which the total developing map `M → RoundSphere3` of the unit-curvature
recognition route follows by already checked theorems.

Both hypotheses are joint-uniformity statements about the differential-induced
successor construction of the Cartan chain:

* `UnitCurvatureSuccessorDataNeighborhood3` (H1): for every unit-curvature
  metric, the locus of parameters `((x, p), z)` at which a differential-induced
  successor datum exists for every tangent alignment at `(x, p)` is a
  neighborhood of the diagonal `z = x`.  Constant curvature proves only the
  fixed-anchor vertical slices
  (`universalSuccessorDataLocus_vertical_mem_nhds_of_curvature`); the joint
  neighborhood as the anchors move is open.
* `UnitCurvatureSuccessorEqualityNeighborhood3` (H2): for every unit-curvature
  metric, the locus at which the old germ and the successor germ agree is a
  neighborhood of the diagonal.  Constant curvature proves the fixed-anchor
  version with a datum-dependent radius
  (`fixedAnchorActualSuccessorEqualityNeighborhood_of_constantCurvature`); a
  radius persisting under motion of the anchors is open.

Neither hypothesis is proved here.  The theorems below only certify that these
two statements, together with the existing chain realization and overlap
compatibility theorems, produce `UnitCurvatureGlobalLocalDevelopment3`,
hence `UnitConstantCurvatureSphereRecognition3`, hence the conditional
`PoincareConjecture` composition with Hamilton convergence.
-/

noncomputable section

open scoped Manifold ContDiff Topology

universe u

namespace Poincare
namespace CartanTwoNeighborhoodDevelopment

open CartanCanonicalRootedDirectGenericNeighborhoodRecognition
open CartanCanonicalRootedReparameterizedUniformRadiusGridAssembly
open DifferentialSuccessorJointEqualityNeighborhood
open DifferentialUniformSuccessorMesh
open CartanCanonicalRootedUniformSuccessorMeshRecognition

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
variable [ChartedSpace (ClosedSmoothModel 3) M]
variable [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
variable [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M]

/--
H1: joint successor-data neighborhood for every unit-curvature metric.  This is
an open obligation; only its fixed-anchor slices are proved from curvature.
-/
def UnitCurvatureSuccessorDataNeighborhood3 : Prop :=
  ∀ g : ClosedSmoothRiemannianMetric 3 M,
    HasConstantSectionalCurvature3 g 1 →
      CartanAtlasRootedPathCurvatureSuccessorRadius.UniversalSuccessorDataNeighborhood g

/--
H2: joint successor-equality neighborhood for every unit-curvature metric.  This
is an open obligation; only the fixed-anchor, datum-dependent-radius version is
proved from curvature.
-/
def UnitCurvatureSuccessorEqualityNeighborhood3 : Prop :=
  ∀ g : ClosedSmoothRiemannianMetric 3 M,
    HasConstantSectionalCurvature3 g 1 →
      UniversalSuccessorEqualityNeighborhood g

omit [SecondCountableTopology M] [CompactSpace M] [ConnectedSpace M]
    [SimplyConnectedSpace M] in
/-- H1 expands to its universal successor-data-neighborhood payload. -/
theorem unitCurvatureSuccessorDataNeighborhood3_eq :
    UnitCurvatureSuccessorDataNeighborhood3 (M := M) =
      (∀ g : ClosedSmoothRiemannianMetric 3 M,
        HasConstantSectionalCurvature3 g 1 →
          CartanAtlasRootedPathCurvatureSuccessorRadius.UniversalSuccessorDataNeighborhood
            g) :=
  rfl

omit [SecondCountableTopology M] [CompactSpace M] [ConnectedSpace M]
    [SimplyConnectedSpace M] in
/-- H2 expands to its universal successor-equality-neighborhood payload. -/
theorem unitCurvatureSuccessorEqualityNeighborhood3_eq :
    UnitCurvatureSuccessorEqualityNeighborhood3 (M := M) =
      (∀ g : ClosedSmoothRiemannianMetric 3 M,
        HasConstantSectionalCurvature3 g 1 →
          UniversalSuccessorEqualityNeighborhood g) :=
  rfl

omit [SecondCountableTopology M] in
/--
H1 and H2 realize a rooted chain along every path with whole-cell mesh
control, which the canonical generic recognition turns into a restricted
compatible Cartan atlas.
-/
theorem restrictedCompatibleCartanAtlas_of_two_neighborhoods
    (dataStability : UnitCurvatureSuccessorDataNeighborhood3 (M := M))
    (equalityStability : UnitCurvatureSuccessorEqualityNeighborhood3 (M := M)) :
    UnitRecognitionNext.UnitCurvatureRestrictedCompatibleCartanAtlas3 (M := M) := by
  intro g hcurv
  let successor : UniformGenericSuccessorRadiusCertificate g :=
    uniformGenericSuccessorRadiusCertificateOfNeighborhood
      g (dataStability g hcurv)
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
      exists_genericRootedRealization_with_wholeCellMesh_of_certificate
        certificate skeleton with
    ⟨realization, hmono, hstrict, _heventual, hwhole⟩
  let endpoint := realization.toEndpointFamily
  have hendpointMono : ∀ x : M,
      Monotone (endpoint.nodeTime x) := hmono
  have hendpointStrict : ∀ x : M,
      ∀ n < endpoint.terminalIndex x,
        endpoint.nodeTime x n < endpoint.nodeTime x (n + 1) := hstrict
  have hendpointWhole :
      letI : MetricSpace M := g.toMetricSpace
      ∀ (x : M) (n : ℕ) (a b : unitInterval),
        a ∈ Set.Icc (endpoint.nodeTime x n) (endpoint.nodeTime x (n + 1)) →
        b ∈ Set.Icc (endpoint.nodeTime x n) (endpoint.nodeTime x (n + 1)) →
        dist (endpoint.path x a) (endpoint.path x b) <
          certificate.meshRadius := hwhole
  exact ⟨
    restrictedCompatibleCartanAtlasData3_of_genericDirectBoundaryGeometry
      certificate endpoint hendpointMono hendpointStrict hendpointWhole⟩

/-- H1 and H2 produce the total local developing map. -/
theorem globalLocalDevelopment_of_two_neighborhoods
    (dataStability : UnitCurvatureSuccessorDataNeighborhood3 (M := M))
    (equalityStability : UnitCurvatureSuccessorEqualityNeighborhood3 (M := M)) :
    UnitRecognitionNext.UnitCurvatureGlobalLocalDevelopment3 (M := M) :=
  UnitRecognitionNext.globalLocalDevelopment_of_restrictedCompatibleCartanAtlas
    (restrictedCompatibleCartanAtlas_of_two_neighborhoods dataStability equalityStability)

/-- H1 and H2 discharge unit-curvature sphere recognition. -/
theorem unitConstantCurvatureSphereRecognition3_of_two_neighborhoods
    (dataStability : UnitCurvatureSuccessorDataNeighborhood3 (M := M))
    (equalityStability : UnitCurvatureSuccessorEqualityNeighborhood3 (M := M)) :
    UnitConstantCurvatureSphereRecognition3 M :=
  RoundSphereSimpleConnected.unitConstantCurvatureSphereRecognition3_of_globalLocalDevelopment
    (globalLocalDevelopment_of_two_neighborhoods dataStability equalityStability)

end CartanTwoNeighborhoodDevelopment

namespace CartanTwoNeighborhoodDevelopment

/-- Universal closed form of H1 over every closed simply connected smooth
3-manifold: the registry obligation shape. -/
def UniversalUnitCurvatureSuccessorDataNeighborhoodStatement : Prop :=
  ∀ (N : Type u) [TopologicalSpace N] [T2Space N]
    [SecondCountableTopology N]
    [ChartedSpace (ClosedSmoothModel 3) N]
    [IsManifold (closedSmoothModelWithCorners 3) ∞ N]
    [CompactSpace N] [ConnectedSpace N] [SimplyConnectedSpace N],
      UnitCurvatureSuccessorDataNeighborhood3 (M := N)

/-- Universal closed form of H2 over every closed simply connected smooth
3-manifold: the registry obligation shape. -/
def UniversalUnitCurvatureSuccessorEqualityNeighborhoodStatement : Prop :=
  ∀ (N : Type u) [TopologicalSpace N] [T2Space N]
    [SecondCountableTopology N]
    [ChartedSpace (ClosedSmoothModel 3) N]
    [IsManifold (closedSmoothModelWithCorners 3) ∞ N]
    [CompactSpace N] [ConnectedSpace N] [SimplyConnectedSpace N],
      UnitCurvatureSuccessorEqualityNeighborhood3 (M := N)

/-- Universal unit-curvature sphere recognition: the Killing–Hopf style
endpoint of the Cartan development route, over every closed simply connected
smooth 3-manifold.  It is intentionally absent as a theorem. -/
def UniversalUnitConstantCurvatureSphereRecognitionStatement : Prop :=
  ∀ (N : Type u) [TopologicalSpace N] [T2Space N]
    [SecondCountableTopology N]
    [ChartedSpace (ClosedSmoothModel 3) N]
    [IsManifold (closedSmoothModelWithCorners 3) ∞ N]
    [CompactSpace N] [ConnectedSpace N] [SimplyConnectedSpace N],
      UnitConstantCurvatureSphereRecognition3 N

/-- The universal forms of H1 and H2 discharge universal unit recognition. -/
theorem universalUnitRecognition_of_two_neighborhood_statements
    (hData : UniversalUnitCurvatureSuccessorDataNeighborhoodStatement.{u})
    (hEquality : UniversalUnitCurvatureSuccessorEqualityNeighborhoodStatement.{u}) :
    UniversalUnitConstantCurvatureSphereRecognitionStatement.{u} :=
  fun N _ _ _ _ _ _ _ _ ↦
    unitConstantCurvatureSphereRecognition3_of_two_neighborhoods (hData N) (hEquality N)

end CartanTwoNeighborhoodDevelopment

open CartanTwoNeighborhoodDevelopment in
/--
Conditional Poincare composition on the two-neighborhood boundary: Hamilton
convergence together with the universal forms of H1 and H2 imply the smooth
global Poincare statement.  All three inputs remain explicit hypotheses.
-/
theorem poincareConjecture_of_hamiltonConvergence_of_two_neighborhoods
    (hHamilton :
      ∀ (N : Type u) [TopologicalSpace N] [T2Space N]
        [SecondCountableTopology N]
        [ChartedSpace (ClosedSmoothModel 3) N]
        [IsManifold (closedSmoothModelWithCorners 3) ∞ N]
        [CompactSpace N] [ConnectedSpace N] [SimplyConnectedSpace N],
          HamiltonConvergencePinchedLimit3 N)
    (hData :
      ∀ (N : Type u) [TopologicalSpace N] [T2Space N]
        [SecondCountableTopology N]
        [ChartedSpace (ClosedSmoothModel 3) N]
        [IsManifold (closedSmoothModelWithCorners 3) ∞ N]
        [CompactSpace N] [ConnectedSpace N] [SimplyConnectedSpace N],
          UnitCurvatureSuccessorDataNeighborhood3 (M := N))
    (hEquality :
      ∀ (N : Type u) [TopologicalSpace N] [T2Space N]
        [SecondCountableTopology N]
        [ChartedSpace (ClosedSmoothModel 3) N]
        [IsManifold (closedSmoothModelWithCorners 3) ∞ N]
        [CompactSpace N] [ConnectedSpace N] [SimplyConnectedSpace N],
          UnitCurvatureSuccessorEqualityNeighborhood3 (M := N)) :
    PoincareConjecture.{u} :=
  poincareConjecture_of_hamiltonConvergence_of_unitRecognition
    hHamilton
    (fun N _ _ _ _ _ _ _ _ ↦
      unitConstantCurvatureSphereRecognition3_of_two_neighborhoods (hData N) (hEquality N))

end Poincare
