import Poincare.Global.CartanCanonicalRootedDirectGenericNeighborhoodRecognition
import Poincare.Global.CartanGenericSuccessorDataLocalCover

/-!
# Generic rooted recognition from finite post-realization radii

The direct generic Cartan route does not intrinsically need a successor-germ
equality radius which is uniform over every Cartan state.  For one fixed
realized homotopy grid, constant curvature already supplies positive equality
radii for the finitely many *actual* differential successors occurring in
that grid.  Their finite minimum is the `commonMeshRadius` of
`ReparameterizedRootedOverlapRealizedHomotopyGrid`.

This file connects that pointwise theorem to the restricted Cartan-atlas
consumer without passing through a global successor-equality neighborhood.
The remaining hypothesis is stated geometrically and with its honest
post-realization quantifier order: for each restricted overlap, one realized
finite grid must be horizontally and vertically small relative to the common
radius selected from that very grid.  Thus the residual boundary is adaptive
mesh feedback, not local uniformity of a radius over moving successor data.

Unlike the earlier canonical-family package, every construction below is
generic in `RootedPathContinuedEndpointFamily`.  A uniform generic successor
data radius constructs such an endpoint family automatically.
-/

noncomputable section

open Metric Set
open scoped Manifold ContDiff Topology unitInterval

namespace Poincare
namespace CartanGenericRootedAdaptiveFiniteGridRecognition

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1200000

open CartanAtlasRootedPathAdaptiveMeshRealization
open CartanAtlasRootedPathCurvatureSuccessorRadius
open CartanAtlasRootedPathSkeleton
open CartanAtlasRootedReachableEndpointTransport
open CartanCanonicalRootedDirectGenericNeighborhoodRecognition
open CartanCanonicalRootedEndpointAssembly
open CartanCanonicalRootedReparameterizedUniformRadiusGridAssembly
open CartanGenericSuccessorDataLocalCover
open CartanRootedOverlapReparameterizedGridRealization
open CartanRootedOverlapReparameterizedHomotopyGrid
open DifferentialInducedSuccessor

universe u

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace E M]
variable [IsManifold I ∞ M]
variable [CompactSpace M] [ConnectedSpace M]

variable {g : ClosedSmoothRiemannianMetric 3 M}

/-! ## A generic rooted endpoint from one uniform successor-data radius -/

/--
A state-uniform generic successor-data radius constructs a rooted endpoint
family.  The path-realization theorem is applied with half of that radius:
two points in the same half-radius path ball are less than the full successor
radius apart, so data exist at every actually reached predecessor state.
-/
theorem nonempty_rootedPathContinuedEndpointFamily_of_uniformGenericSuccessorRadius
    (successor : UniformGenericSuccessorRadiusCertificate g) :
    Nonempty (RootedPathContinuedEndpointFamily g) := by
  classical
  letI : MetricSpace M := g.toMetricSpace
  let skeleton := Classical.choice
    (CartanAtlasRootedPathSkeleton.nonempty_rootedCartanPathSkeleton g)
  let radius : M → unitInterval → ℝ :=
    fun _ _ ↦ successor.radius / 2
  have hradius : ∀ x : M, ∀ c : unitInterval, 0 < radius x c := by
    intro x c
    exact half_pos successor.radius_pos
  have hlocal : ∀ (x : M) (c u v : unitInterval)
      (s : CartanChain.ChainState g),
      dist (skeleton.path x u) (skeleton.path x c) < radius x c →
      dist (skeleton.path x v) (skeleton.path x c) < radius x c →
      s.anchor = skeleton.path x u →
        Nonempty (Data s (skeleton.path x v)) := by
    intro x c u v s hu hv hs
    apply successor.data s (skeleton.path x v)
    rw [hs]
    calc
      dist (skeleton.path x v) (skeleton.path x u) ≤
          dist (skeleton.path x v) (skeleton.path x c) +
            dist (skeleton.path x u) (skeleton.path x c) :=
        dist_triangle_right _ _ _
      _ < successor.radius / 2 + successor.radius / 2 :=
        add_lt_add hv hu
      _ = successor.radius := by ring
  rcases
      exists_rootedPathChainRealization_with_prescribed_mesh_of_successor_radii
        skeleton radius hradius hlocal (successor.radius / 2)
          (half_pos successor.radius_pos) with
    ⟨realization, _hterminalPos, _hmono, _heventual, _hsmall⟩
  exact ⟨realization.toEndpointFamily⟩

/-- The classically selected generic rooted endpoint associated to one
uniform successor-data certificate. -/
noncomputable def rootedEndpointOfUniformGenericSuccessorRadius
    (successor : UniformGenericSuccessorRadiusCertificate g) :
    RootedPathContinuedEndpointFamily g :=
  Classical.choice
    (nonempty_rootedPathContinuedEndpointFamily_of_uniformGenericSuccessorRadius
      successor)

/-! ## One actual finite overlap grid -/

/-- The schedule-free restricted-domain membership supplies the terminal
short path used by the generic reparameterized overlap grid. -/
noncomputable def genericTerminalCertificate
    (endpoint : RootedPathContinuedEndpointFamily g)
    {mesh : ℝ} (hmesh : 0 < mesh) {y z : M}
    (hz : z ∈ genericScheduleFreeTerminalRestrictedDomain
      endpoint hmesh y) :
    TerminalShortPathCertificate g y z mesh :=
  Classical.choice
    (terminalShortPathCertificate_of_mem_genericRestrictedDomain
      endpoint hmesh hz)

/--
The actual reparameterized overlap grid generated from a uniform generic-data
radius.  No equality radius is an input: the grid's equality radius is chosen
later, from its finitely many realized differential successors.
-/
noncomputable def genericRealizedGridFromUniformRadius
    [SimplyConnectedSpace M]
    (successor : UniformGenericSuccessorRadiusCertificate g)
    (endpoint : RootedPathContinuedEndpointFamily g)
    {mesh : ℝ} (hmesh : 0 < mesh) {x y z : M}
    (hz : z ∈ genericScheduleFreeTerminalRestrictedDomain endpoint hmesh x ∩
      genericScheduleFreeTerminalRestrictedDomain endpoint hmesh y)
    (N : ℕ)
    (hleft : endpoint.terminalIndex x ≤ N)
    (hright : endpoint.terminalIndex y ≤ N)
    (hhorizontal : HorizontalHalfRadiusSmall endpoint
      (genericTerminalCertificate endpoint hmesh hz.1)
      (genericTerminalCertificate endpoint hmesh hz.2)
      N successor.radius)
    (hvertical : VerticalHalfRadiusSmall endpoint
      (genericTerminalCertificate endpoint hmesh hz.1)
      (genericTerminalCertificate endpoint hmesh hz.2)
      N successor.radius) :
    ReparameterizedRootedOverlapRealizedHomotopyGrid endpoint
      (genericTerminalCertificate endpoint hmesh hz.1)
      (genericTerminalCertificate endpoint hmesh hz.2) N :=
  realizedGrid_of_uniformSuccessorRadius endpoint
    (genericTerminalCertificate endpoint hmesh hz.1)
    (genericTerminalCertificate endpoint hmesh hz.2)
    N hleft hright successor.radius successor.radius_pos successor.data
      hhorizontal hvertical

/--
Proof-bearing finite-grid certificate for one restricted generic overlap.

The first two smallness fields construct all actual row, rung, and cross-cell
successor data.  Only after that grid exists does constant curvature select
`grid.commonMeshRadius`; the last two fields assert smallness at this
post-realization radius.  There is no equality-neighborhood or moving-data
radius in the record.
-/
structure GenericUniformRadiusPostRealizationGridCertificate
    [SimplyConnectedSpace M]
    (successor : UniformGenericSuccessorRadiusCertificate g)
    (endpoint : RootedPathContinuedEndpointFamily g)
    (hcurv : HasConstantSectionalCurvature3 g 1)
    {mesh : ℝ} (hmesh : 0 < mesh)
    (x y z : M)
    (hz : z ∈ genericScheduleFreeTerminalRestrictedDomain endpoint hmesh x ∩
      genericScheduleFreeTerminalRestrictedDomain endpoint hmesh y) where
  commonPredecessor : ℕ
  left_terminalIndex_le :
    endpoint.terminalIndex x ≤ commonPredecessor
  right_terminalIndex_le :
    endpoint.terminalIndex y ≤ commonPredecessor
  horizontalHalfRadius : HorizontalHalfRadiusSmall endpoint
    (genericTerminalCertificate endpoint hmesh hz.1)
    (genericTerminalCertificate endpoint hmesh hz.2)
    commonPredecessor successor.radius
  verticalHalfRadius : VerticalHalfRadiusSmall endpoint
    (genericTerminalCertificate endpoint hmesh hz.1)
    (genericTerminalCertificate endpoint hmesh hz.2)
    commonPredecessor successor.radius
  horizontalSmall :
    let grid := genericRealizedGridFromUniformRadius successor endpoint hmesh hz
      commonPredecessor left_terminalIndex_le right_terminalIndex_le
        horizontalHalfRadius verticalHalfRadius
    grid.HorizontalSmall (grid.commonMeshRadius hcurv)
  verticalSmall :
    let grid := genericRealizedGridFromUniformRadius successor endpoint hmesh hz
      commonPredecessor left_terminalIndex_le right_terminalIndex_le
        horizontalHalfRadius verticalHalfRadius
    grid.VerticalSmall (grid.commonMeshRadius hcurv)

namespace GenericUniformRadiusPostRealizationGridCertificate

/-- The finite realized grid computed from the certificate's geometric
fields. -/
noncomputable def grid
    [SimplyConnectedSpace M]
    {successor : UniformGenericSuccessorRadiusCertificate g}
    {endpoint : RootedPathContinuedEndpointFamily g}
    {hcurv : HasConstantSectionalCurvature3 g 1}
    {mesh : ℝ} {hmesh : 0 < mesh}
    {x y z : M}
    {hz : z ∈ genericScheduleFreeTerminalRestrictedDomain endpoint hmesh x ∩
      genericScheduleFreeTerminalRestrictedDomain endpoint hmesh y}
    (certificate : GenericUniformRadiusPostRealizationGridCertificate
      successor endpoint hcurv hmesh x y z hz) :
    ReparameterizedRootedOverlapRealizedHomotopyGrid endpoint
      (genericTerminalCertificate endpoint hmesh hz.1)
      (genericTerminalCertificate endpoint hmesh hz.2)
      certificate.commonPredecessor :=
  genericRealizedGridFromUniformRadius successor endpoint hmesh hz
    certificate.commonPredecessor certificate.left_terminalIndex_le
      certificate.right_terminalIndex_le certificate.horizontalHalfRadius
        certificate.verticalHalfRadius

/-- The stored horizontal post-realization inequality belongs to the exact
computed grid. -/
theorem grid_horizontalSmall
    [SimplyConnectedSpace M]
    {successor : UniformGenericSuccessorRadiusCertificate g}
    {endpoint : RootedPathContinuedEndpointFamily g}
    {hcurv : HasConstantSectionalCurvature3 g 1}
    {mesh : ℝ} {hmesh : 0 < mesh}
    {x y z : M}
    {hz : z ∈ genericScheduleFreeTerminalRestrictedDomain endpoint hmesh x ∩
      genericScheduleFreeTerminalRestrictedDomain endpoint hmesh y}
    (certificate : GenericUniformRadiusPostRealizationGridCertificate
      successor endpoint hcurv hmesh x y z hz) :
    certificate.grid.HorizontalSmall
      (certificate.grid.commonMeshRadius hcurv) := by
  exact certificate.horizontalSmall

/-- The stored vertical post-realization inequality belongs to the exact
computed grid. -/
theorem grid_verticalSmall
    [SimplyConnectedSpace M]
    {successor : UniformGenericSuccessorRadiusCertificate g}
    {endpoint : RootedPathContinuedEndpointFamily g}
    {hcurv : HasConstantSectionalCurvature3 g 1}
    {mesh : ℝ} {hmesh : 0 < mesh}
    {x y z : M}
    {hz : z ∈ genericScheduleFreeTerminalRestrictedDomain endpoint hmesh x ∩
      genericScheduleFreeTerminalRestrictedDomain endpoint hmesh y}
    (certificate : GenericUniformRadiusPostRealizationGridCertificate
      successor endpoint hcurv hmesh x y z hz) :
    certificate.grid.VerticalSmall
      (certificate.grid.commonMeshRadius hcurv) := by
  exact certificate.verticalSmall

/-- Constant curvature's pointwise actual-successor radii identify the two
terminal Cartan values on this restricted overlap. -/
theorem germ_value_eq
    [SimplyConnectedSpace M]
    (successor : UniformGenericSuccessorRadiusCertificate g)
    (endpoint : RootedPathContinuedEndpointFamily g)
    (hcurv : HasConstantSectionalCurvature3 g 1)
    {mesh : ℝ} (hmesh : 0 < mesh)
    (x y z : M)
    {hz : z ∈ genericScheduleFreeTerminalRestrictedDomain endpoint hmesh x ∩
      genericScheduleFreeTerminalRestrictedDomain endpoint hmesh y}
    (certificate : GenericUniformRadiusPostRealizationGridCertificate
      successor endpoint hcurv hmesh x y z hz) :
    (endpoint.terminalState x).germ z =
      (endpoint.terminalState y).germ z :=
  certificate.grid.germ_value_eq_of_small hcurv
    certificate.grid_horizontalSmall certificate.grid_verticalSmall

end GenericUniformRadiusPostRealizationGridCertificate

/-! ## Restricted atlas and sphere recognition -/

/-- Per-overlap finite adaptive certificates for the generic restricted
endpoint domains. -/
structure GenericUniformRadiusPostRealizationGridCoherence
    [SimplyConnectedSpace M]
    (successor : UniformGenericSuccessorRadiusCertificate g)
    (endpoint : RootedPathContinuedEndpointFamily g)
    (hcurv : HasConstantSectionalCurvature3 g 1)
    {mesh : ℝ} (hmesh : 0 < mesh) where
  overlapCertificate : ∀ x y z : M,
    ∀ hz : z ∈ genericScheduleFreeTerminalRestrictedDomain endpoint hmesh x ∩
      genericScheduleFreeTerminalRestrictedDomain endpoint hmesh y,
      GenericUniformRadiusPostRealizationGridCertificate
        successor endpoint hcurv hmesh x y z hz

/-- Finite post-realization grid coherence constructs the restricted
compatible Cartan atlas without a global successor-equality radius. -/
noncomputable def
    GenericUniformRadiusPostRealizationGridCoherence.toRestrictedCompatibleCartanAtlasData3
    [SimplyConnectedSpace M]
    (successor : UniformGenericSuccessorRadiusCertificate g)
    (endpoint : RootedPathContinuedEndpointFamily g)
    (hcurv : HasConstantSectionalCurvature3 g 1)
    {mesh : ℝ} (hmesh : 0 < mesh)
    (coherence : GenericUniformRadiusPostRealizationGridCoherence
      successor endpoint hcurv hmesh) :
    UnitRecognitionNext.RestrictedCompatibleCartanAtlasData3 g where
  target := endpoint.target
  alignment := endpoint.alignment
  domain := genericScheduleFreeTerminalRestrictedDomain endpoint hmesh
  isOpen_domain :=
    isOpen_genericScheduleFreeTerminalRestrictedDomain endpoint hmesh
  anchor_mem_domain :=
    anchor_mem_genericScheduleFreeTerminalRestrictedDomain endpoint hmesh
  domain_subset_source := by
    intro x z hz
    have hterminal : z ∈ (endpoint.terminalState x).germ.source := hz.1
    have hx := endpoint.anchoredFamilyState_eq_terminalState x
    change z ∈
      (CartanLocalRigidity.anchoredFamilyState g endpoint.target
        endpoint.alignment x).germ.source
    simpa only [hx] using hterminal
  compatible := by
    intro x y z hz
    have hvalue :=
      (coherence.overlapCertificate x y z hz).germ_value_eq
        successor endpoint hcurv hmesh x y z
    have hx := endpoint.anchoredFamilyState_eq_terminalState x
    have hy := endpoint.anchoredFamilyState_eq_terminalState y
    change
      (CartanLocalRigidity.anchoredFamilyState g endpoint.target
          endpoint.alignment x).germ z =
        (CartanLocalRigidity.anchoredFamilyState g endpoint.target
          endpoint.alignment y).germ z
    simpa only [hx, hy] using hvalue

/--
Direct generic sphere recognition from successor-data stability and finite
post-realization adaptive grid coherence.

The selected rooted endpoint is constructed solely from the generic data
radius.  Constant curvature supplies every equality radius internally on each
fixed realized overlap grid.  Hence neither
`UniversalSuccessorEqualityNeighborhood` nor
`ActualSuccessorCoordinateRigidityLocalUniformity` appears in the theorem.
-/
theorem unitConstantCurvatureSphereRecognition3_of_genericDataNeighborhood_postRealizationGridCoherence
    [SecondCountableTopology M] [SimplyConnectedSpace M]
    (dataStability : ∀ (g : ClosedSmoothRiemannianMetric 3 M),
      HasConstantSectionalCurvature3 g 1 →
        CartanAtlasRootedPathCurvatureSuccessorRadius.UniversalSuccessorDataNeighborhood g)
    (completion : ∀ (g : ClosedSmoothRiemannianMetric 3 M),
      ∀ hcurv : HasConstantSectionalCurvature3 g 1,
        let successor := uniformGenericSuccessorRadiusCertificateOfNeighborhood
          g (dataStability g hcurv)
        let endpoint := rootedEndpointOfUniformGenericSuccessorRadius successor
        ∃ mesh : ℝ,
          ∃ hmesh : 0 < mesh,
            Nonempty
              (GenericUniformRadiusPostRealizationGridCoherence
                successor endpoint hcurv hmesh)) :
    UnitConstantCurvatureSphereRecognition3 M := by
  apply
    RoundSphereSimpleConnected.unitConstantCurvatureSphereRecognition3_of_restrictedCompatibleCartanAtlas
  intro g hcurv
  let successor := uniformGenericSuccessorRadiusCertificateOfNeighborhood
    g (dataStability g hcurv)
  let endpoint := rootedEndpointOfUniformGenericSuccessorRadius successor
  rcases completion g hcurv with ⟨mesh, hmesh, coherence⟩
  rcases coherence with ⟨coherence⟩
  exact
    ⟨coherence.toRestrictedCompatibleCartanAtlasData3
      successor endpoint hcurv hmesh⟩

/-- Convenience form of the preceding recognition theorem at the current
chart-local generic-data boundary.  The local cover is converted to the
legacy diagonal neighborhood only to select its uniform generic successor
radius; the equality side remains entirely finite and post-realization. -/
theorem unitConstantCurvatureSphereRecognition3_of_localGenericSuccessorDataCover_postRealizationGridCoherence
    [SecondCountableTopology M] [SimplyConnectedSpace M]
    (dataStability : ∀ (g : ClosedSmoothRiemannianMetric 3 M),
      HasConstantSectionalCurvature3 g 1 →
        LocalGenericSuccessorDataCover g)
    (completion : ∀ (g : ClosedSmoothRiemannianMetric 3 M),
      ∀ hcurv : HasConstantSectionalCurvature3 g 1,
        let successor := uniformGenericSuccessorRadiusCertificateOfNeighborhood
          g ((dataStability g hcurv).toUniversalSuccessorDataNeighborhood)
        let endpoint := rootedEndpointOfUniformGenericSuccessorRadius successor
        ∃ mesh : ℝ,
          ∃ hmesh : 0 < mesh,
            Nonempty
              (GenericUniformRadiusPostRealizationGridCoherence
                successor endpoint hcurv hmesh)) :
    UnitConstantCurvatureSphereRecognition3 M := by
  apply
    unitConstantCurvatureSphereRecognition3_of_genericDataNeighborhood_postRealizationGridCoherence
      (dataStability := fun g hcurv ↦
        (dataStability g hcurv).toUniversalSuccessorDataNeighborhood)
  exact completion

end CartanGenericRootedAdaptiveFiniteGridRecognition
end Poincare
