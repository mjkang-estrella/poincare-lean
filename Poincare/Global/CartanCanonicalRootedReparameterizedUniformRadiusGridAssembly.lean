import Poincare.Global.CartanAtlasRootedPathCurvatureSuccessorRadius
import Poincare.Global.CartanCanonicalRootedDerivedTerminalHomotopyGridAssembly
import Poincare.Global.CartanRootedOverlapReparameterizedGridRealization

/-!
# Canonical rooted assembly from one uniform generic successor radius

The proof-bearing diagonal-neighborhood contract gives one positive metric
radius on which generic differential-successor data exist for every Cartan
state.  For each schedule-free terminal overlap, half-radius geometric
smallness then constructs the complete reparameterized realized grid by
dependent recursion.

The overlap certificate in this file does not store row chains, rung data,
cross-cell data, or boundary predecessor equalities.  It stores only a common
predecessor column, the two terminal-index bounds, half-radius horizontal and
vertical geometry, and horizontal/vertical smallness at the curvature radius
of the grid constructed from those data.

The remaining feedback is deliberate: the curvature radius is selected only
after the finite realized grid has been constructed.  No theorem here claims
that a homotopy subdivision is automatically small relative to that
state-dependent radius.
-/

noncomputable section

open Metric Set
open scoped Manifold ContDiff Topology unitInterval

namespace Poincare
namespace CartanCanonicalRootedReparameterizedUniformRadiusGridAssembly

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

open CartanAtlasRootedPathCurvatureSuccessorRadius
open CartanAtlasRootedPathSkeleton
open CartanAtlasRootedReachableEndpointTransport
open CartanCanonicalRootedEndpointAssembly
open CartanCanonicalRootedEndpointAssembly.CanonicalRootedRealizationPackage
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

/-- One positive metric radius on which successor data exist for every
generic Cartan state and every next anchor. -/
structure UniformGenericSuccessorRadiusCertificate
    (g : ClosedSmoothRiemannianMetric 3 M) where
  radius : ℝ
  radius_pos : 0 < radius
  data :
    letI : MetricSpace M := g.toMetricSpace
    ∀ (s : CartanChain.ChainState g) (q : M),
      dist q s.anchor < radius → Nonempty (Data s q)

/-- The joint diagonal-neighborhood contract produces a proof-bearing
uniform generic successor radius. -/
theorem nonempty_uniformGenericSuccessorRadiusCertificate_of_universalNeighborhood
    (g : ClosedSmoothRiemannianMetric 3 M)
    (hneighborhood : UniversalSuccessorDataNeighborhood g) :
    Nonempty (UniformGenericSuccessorRadiusCertificate g) := by
  letI : MetricSpace M := g.toMetricSpace
  rcases
      exists_uniform_successor_data_radius_of_universalNeighborhood
        g hneighborhood with
    ⟨rho, hrho, hdata⟩
  refine ⟨{ radius := rho, radius_pos := hrho, data := ?_ }⟩
  intro s q hdist
  rcases s with ⟨x, p, L⟩
  exact hdata x p L q hdist

/-- The classically selected uniform-radius certificate supplied by a fixed
joint diagonal-neighborhood proof. -/
noncomputable def uniformGenericSuccessorRadiusCertificateOfNeighborhood
    (g : ClosedSmoothRiemannianMetric 3 M)
    (hneighborhood : UniversalSuccessorDataNeighborhood g) :
    UniformGenericSuccessorRadiusCertificate g :=
  Classical.choice
    (nonempty_uniformGenericSuccessorRadiusCertificate_of_universalNeighborhood
      g hneighborhood)

namespace CanonicalRootedRealizationPackage

open CartanTerminalShortPathScheduleFree

variable {skeleton : RootedCartanPathSkeleton g}

/-- Construct the complete realized grid from the uniform-radius certificate
and the four geometric boundary inputs retained by the overlap certificate. -/
noncomputable def realizedGridFromUniformRadius
    [SimplyConnectedSpace M]
    (successor : UniformGenericSuccessorRadiusCertificate g)
    (package : CanonicalRootedRealizationPackage skeleton)
    {mesh : ℝ} (hmesh : 0 < mesh)
    {x y z : M}
    (hz : z ∈
      scheduleFreeTerminalRestrictedDomain package hmesh x ∩
        scheduleFreeTerminalRestrictedDomain package hmesh y)
    (N : ℕ)
    (hleft : package.endpoint.terminalIndex x ≤ N)
    (hright : package.endpoint.terminalIndex y ≤ N)
    (hhorizontal : HorizontalHalfRadiusSmall package.endpoint
      (derivedTerminalPath package hmesh hz.1)
      (derivedTerminalPath package hmesh hz.2) N successor.radius)
    (hvertical : VerticalHalfRadiusSmall package.endpoint
      (derivedTerminalPath package hmesh hz.1)
      (derivedTerminalPath package hmesh hz.2) N successor.radius) :
    ReparameterizedRootedOverlapRealizedHomotopyGrid package.endpoint
      (derivedTerminalPath package hmesh hz.1)
      (derivedTerminalPath package hmesh hz.2) N :=
  realizedGrid_of_uniformSuccessorRadius package.endpoint
    (derivedTerminalPath package hmesh hz.1)
    (derivedTerminalPath package hmesh hz.2)
    N hleft hright successor.radius successor.radius_pos successor.data
      hhorizontal hvertical

/-- The proof-bearing residue for one canonical schedule-free overlap.

The realized differential grid is a definition computed from these fields;
it is not stored in the certificate. -/
structure UniformRadiusDerivedTerminalRootedOverlapGridCertificate
    [SimplyConnectedSpace M]
    (successor : UniformGenericSuccessorRadiusCertificate g)
    (package : CanonicalRootedRealizationPackage skeleton)
    (hcurv : HasConstantSectionalCurvature3 g 1)
    {mesh : ℝ} (hmesh : 0 < mesh)
    (x y z : M)
    (hz : z ∈
      scheduleFreeTerminalRestrictedDomain package hmesh x ∩
        scheduleFreeTerminalRestrictedDomain package hmesh y) where
  commonPredecessor : ℕ
  left_terminalIndex_le :
    package.endpoint.terminalIndex x ≤ commonPredecessor
  right_terminalIndex_le :
    package.endpoint.terminalIndex y ≤ commonPredecessor
  horizontalHalfRadius : HorizontalHalfRadiusSmall package.endpoint
    (derivedTerminalPath package hmesh hz.1)
    (derivedTerminalPath package hmesh hz.2)
    commonPredecessor successor.radius
  verticalHalfRadius : VerticalHalfRadiusSmall package.endpoint
    (derivedTerminalPath package hmesh hz.1)
    (derivedTerminalPath package hmesh hz.2)
    commonPredecessor successor.radius
  horizontalSmall :
    let grid := realizedGridFromUniformRadius successor package hmesh hz
      commonPredecessor left_terminalIndex_le right_terminalIndex_le
        horizontalHalfRadius verticalHalfRadius
    grid.HorizontalSmall (grid.commonMeshRadius hcurv)
  verticalSmall :
    let grid := realizedGridFromUniformRadius successor package hmesh hz
      commonPredecessor left_terminalIndex_le right_terminalIndex_le
        horizontalHalfRadius verticalHalfRadius
    grid.VerticalSmall (grid.commonMeshRadius hcurv)

namespace UniformRadiusDerivedTerminalRootedOverlapGridCertificate

/-- The realized grid computed from the certificate's proof-bearing geometric
fields. -/
noncomputable def grid
    [SimplyConnectedSpace M]
    {successor : UniformGenericSuccessorRadiusCertificate g}
    {package : CanonicalRootedRealizationPackage skeleton}
    {hcurv : HasConstantSectionalCurvature3 g 1}
    {mesh : ℝ} {hmesh : 0 < mesh}
    {x y z : M}
    {hz : z ∈
      scheduleFreeTerminalRestrictedDomain package hmesh x ∩
        scheduleFreeTerminalRestrictedDomain package hmesh y}
    (certificate : UniformRadiusDerivedTerminalRootedOverlapGridCertificate
      successor package hcurv hmesh x y z hz) :
    ReparameterizedRootedOverlapRealizedHomotopyGrid package.endpoint
      (derivedTerminalPath package hmesh hz.1)
      (derivedTerminalPath package hmesh hz.2)
      certificate.commonPredecessor :=
  realizedGridFromUniformRadius successor package hmesh hz
    certificate.commonPredecessor certificate.left_terminalIndex_le
      certificate.right_terminalIndex_le certificate.horizontalHalfRadius
        certificate.verticalHalfRadius

/-- The stored horizontal feedback inequality is exactly the one for the
computed realized grid. -/
theorem grid_horizontalSmall
    [SimplyConnectedSpace M]
    {successor : UniformGenericSuccessorRadiusCertificate g}
    {package : CanonicalRootedRealizationPackage skeleton}
    {hcurv : HasConstantSectionalCurvature3 g 1}
    {mesh : ℝ} {hmesh : 0 < mesh}
    {x y z : M}
    {hz : z ∈
      scheduleFreeTerminalRestrictedDomain package hmesh x ∩
        scheduleFreeTerminalRestrictedDomain package hmesh y}
    (certificate : UniformRadiusDerivedTerminalRootedOverlapGridCertificate
      successor package hcurv hmesh x y z hz) :
    certificate.grid.HorizontalSmall
      (certificate.grid.commonMeshRadius hcurv) := by
  exact certificate.horizontalSmall

/-- The stored vertical feedback inequality is exactly the one for the
computed realized grid. -/
theorem grid_verticalSmall
    [SimplyConnectedSpace M]
    {successor : UniformGenericSuccessorRadiusCertificate g}
    {package : CanonicalRootedRealizationPackage skeleton}
    {hcurv : HasConstantSectionalCurvature3 g 1}
    {mesh : ℝ} {hmesh : 0 < mesh}
    {x y z : M}
    {hz : z ∈
      scheduleFreeTerminalRestrictedDomain package hmesh x ∩
        scheduleFreeTerminalRestrictedDomain package hmesh y}
    (certificate : UniformRadiusDerivedTerminalRootedOverlapGridCertificate
      successor package hcurv hmesh x y z hz) :
    certificate.grid.VerticalSmall
      (certificate.grid.commonMeshRadius hcurv) := by
  exact certificate.verticalSmall

/-- The computed reparameterized grid identifies the two actual terminal
Cartan germ values at the overlap point. -/
theorem germ_value_eq
    [SimplyConnectedSpace M]
    (successor : UniformGenericSuccessorRadiusCertificate g)
    (package : CanonicalRootedRealizationPackage skeleton)
    (hcurv : HasConstantSectionalCurvature3 g 1)
    {mesh : ℝ} (hmesh : 0 < mesh)
    (x y z : M)
    {hz : z ∈
      scheduleFreeTerminalRestrictedDomain package hmesh x ∩
        scheduleFreeTerminalRestrictedDomain package hmesh y}
    (certificate : UniformRadiusDerivedTerminalRootedOverlapGridCertificate
      successor package hcurv hmesh x y z hz) :
    (package.endpoint.terminalState x).germ z =
      (package.endpoint.terminalState y).germ z :=
  certificate.grid.germ_value_eq_of_small hcurv
    certificate.grid_horizontalSmall certificate.grid_verticalSmall

end UniformRadiusDerivedTerminalRootedOverlapGridCertificate

/-- Schedule-free overlap coherence whose realized grids are all generated
from one metric-wide uniform successor radius. -/
structure UniformRadiusDerivedTerminalGridOverlapCoherence
    [SimplyConnectedSpace M]
    (successor : UniformGenericSuccessorRadiusCertificate g)
    (package : CanonicalRootedRealizationPackage skeleton)
    (hcurv : HasConstantSectionalCurvature3 g 1)
    {mesh : ℝ} (hmesh : 0 < mesh) where
  overlapCertificate : ∀ x y z : M,
    ∀ hz : z ∈
      scheduleFreeTerminalRestrictedDomain package hmesh x ∩
        scheduleFreeTerminalRestrictedDomain package hmesh y,
      UniformRadiusDerivedTerminalRootedOverlapGridCertificate
        successor package hcurv hmesh x y z hz

/-- Uniform-radius schedule-free coherence constructs the restricted
compatible Cartan atlas directly. -/
noncomputable def
    UniformRadiusDerivedTerminalGridOverlapCoherence.toRestrictedCompatibleCartanAtlasData3
    [SimplyConnectedSpace M]
    (successor : UniformGenericSuccessorRadiusCertificate g)
    (package : CanonicalRootedRealizationPackage skeleton)
    (hcurv : HasConstantSectionalCurvature3 g 1)
    {mesh : ℝ} (hmesh : 0 < mesh)
    (coherence : UniformRadiusDerivedTerminalGridOverlapCoherence
      successor package hcurv hmesh) :
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
    have hvalue :=
      (coherence.overlapCertificate x y z hz).germ_value_eq
        successor package hcurv hmesh x y z
    have hx := package.endpoint_anchoredFamilyState_eq_terminalState x
    have hy := package.endpoint_anchoredFamilyState_eq_terminalState y
    change
      (CartanLocalRigidity.anchoredFamilyState g package.endpoint.target
          package.endpoint.alignment x).germ z =
        (CartanLocalRigidity.anchoredFamilyState g package.endpoint.target
          package.endpoint.alignment y).germ z
    simpa only [hx, hy] using hvalue

/-- Fully quantified unit-curvature recognition from the two explicit
remaining inputs:

* joint successor-data stability at the complete parameter diagonal; and
* per-overlap geometric and curvature-radius smallness for the grids generated
  from the resulting metric-wide uniform radius.
-/
theorem unitConstantCurvatureSphereRecognition3_of_canonicalRootedReparameterizedUniformRadiusGridOverlapCoherence
    [SecondCountableTopology M] [SimplyConnectedSpace M]
    (jointStability : ∀ (g : ClosedSmoothRiemannianMetric 3 M),
      HasConstantSectionalCurvature3 g 1 →
        UniversalSuccessorDataNeighborhood g)
    (completion : ∀ (g : ClosedSmoothRiemannianMetric 3 M),
      ∀ hcurv : HasConstantSectionalCurvature3 g 1,
        ∃ skeleton : RootedCartanPathSkeleton g,
          ∃ package : CanonicalRootedRealizationPackage skeleton,
            ∃ mesh : ℝ,
              ∃ hmesh : 0 < mesh,
                Nonempty
                  (UniformRadiusDerivedTerminalGridOverlapCoherence
                    (uniformGenericSuccessorRadiusCertificateOfNeighborhood
                      g (jointStability g hcurv))
                    package hcurv hmesh)) :
    UnitConstantCurvatureSphereRecognition3 M := by
  apply
    RoundSphereSimpleConnected.unitConstantCurvatureSphereRecognition3_of_restrictedCompatibleCartanAtlas
  intro g hcurv
  rcases completion g hcurv with
    ⟨skeleton, package, mesh, hmesh, coherence⟩
  rcases coherence with ⟨coherence⟩
  exact
    ⟨coherence.toRestrictedCompatibleCartanAtlasData3
      (uniformGenericSuccessorRadiusCertificateOfNeighborhood
        g (jointStability g hcurv))
      package hcurv hmesh⟩

end CanonicalRootedRealizationPackage
end CartanCanonicalRootedReparameterizedUniformRadiusGridAssembly
end Poincare
