import Poincare.Global.CartanCanonicalRootedDerivedTerminalHomotopyGridAssembly
import Poincare.Global.CartanRootedOverlapReparameterizedHomotopyGrid

/-!
# Canonical rooted assembly through reparameterized derived-terminal grids

Schedule-free terminal-domain membership canonically supplies the two short
paths from the chosen anchors to an overlap point.  The reparameterized
boundary construction then places the two resulting root-to-overlap paths on
one common uniform column grid.

This file packages exactly the remaining per-overlap assumptions: a common
predecessor column `N`, one realized differential homotopy grid at that `N`,
and horizontal and vertical smallness for the chosen grid radius.  No
predecessor state equality is stored.  Those equalities are derived inside
`ReparameterizedRootedOverlapRealizedHomotopyGrid` from the reachable boundary
chains and their node provenance.
-/

noncomputable section

open Set
open scoped Manifold ContDiff Topology unitInterval

namespace Poincare
namespace CartanCanonicalRootedEndpointAssembly
namespace CanonicalRootedRealizationPackage

set_option linter.unusedSectionVars false

universe u

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace E M]
variable [IsManifold I ∞ M]

open CartanAtlasRootedPathSkeleton
open CartanRootedOverlapReparameterizedHomotopyGrid
open CartanTerminalShortPathScheduleFree

variable {g : ClosedSmoothRiemannianMetric 3 M}
variable {skeleton : RootedCartanPathSkeleton g}

/-- The proof-bearing payload for one schedule-free overlap after both
terminal paths have been canonically derived and their boundary samplings
have been reparameterized onto a common grid.

The certificate stores the common predecessor column, the realized row/rung
data, and the two mesh bounds.  In particular, it has no left or right
predecessor equality field. -/
structure ReparameterizedDerivedTerminalRootedOverlapHomotopyGridCertificate
    [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M]
    (package : CanonicalRootedRealizationPackage skeleton)
    (hcurv : HasConstantSectionalCurvature3 g 1)
    {mesh : ℝ} (hmesh : 0 < mesh)
    (x y z : M)
    (hz : z ∈
      scheduleFreeTerminalRestrictedDomain package hmesh x ∩
        scheduleFreeTerminalRestrictedDomain package hmesh y) where
  commonPredecessor : ℕ
  grid : ReparameterizedRootedOverlapRealizedHomotopyGrid package.endpoint
    (derivedTerminalPath package hmesh hz.1)
    (derivedTerminalPath package hmesh hz.2)
    commonPredecessor
  horizontalSmall : grid.HorizontalSmall (grid.commonMeshRadius hcurv)
  verticalSmall : grid.VerticalSmall (grid.commonMeshRadius hcurv)

namespace ReparameterizedDerivedTerminalRootedOverlapHomotopyGridCertificate

/-- A reparameterized derived-terminal certificate identifies the two actual
terminal Cartan germ values at its overlap point.  Boundary predecessor
identities are supplied internally by the grid's provenance theorems. -/
theorem germ_value_eq
    [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M]
    (package : CanonicalRootedRealizationPackage skeleton)
    (hcurv : HasConstantSectionalCurvature3 g 1)
    {mesh : ℝ} (hmesh : 0 < mesh)
    (x y z : M)
    {hz : z ∈
      scheduleFreeTerminalRestrictedDomain package hmesh x ∩
        scheduleFreeTerminalRestrictedDomain package hmesh y}
    (certificate :
      ReparameterizedDerivedTerminalRootedOverlapHomotopyGridCertificate
        package hcurv hmesh x y z hz) :
    (package.endpoint.terminalState x).germ z =
      (package.endpoint.terminalState y).germ z :=
  certificate.grid.germ_value_eq_of_small hcurv
    certificate.horizontalSmall certificate.verticalSmall

end ReparameterizedDerivedTerminalRootedOverlapHomotopyGridCertificate

/-- Minimal coherence on the canonical schedule-free terminal domains using
reparameterized realized homotopy grids.

Domain topology, anchor membership, source inclusion, and both terminal paths
are derived.  The only field is the still-nonautomatic per-overlap provider of
`N`, realized differential grid data, and chosen-radius mesh smallness. -/
structure ReparameterizedDerivedTerminalHomotopyGridOverlapCoherence
    [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M]
    (package : CanonicalRootedRealizationPackage skeleton)
    (hcurv : HasConstantSectionalCurvature3 g 1)
    {mesh : ℝ} (hmesh : 0 < mesh) where
  overlapCertificate : ∀ x y z : M,
    ∀ hz : z ∈
      scheduleFreeTerminalRestrictedDomain package hmesh x ∩
        scheduleFreeTerminalRestrictedDomain package hmesh y,
      ReparameterizedDerivedTerminalRootedOverlapHomotopyGridCertificate
        package hcurv hmesh x y z hz

/-- Reparameterized derived-terminal coherence constructs the restricted
compatible Cartan atlas directly.  It cannot pass through the legacy
homotopy-grid certificate because that type fixes a homotopy between the
unreparameterized boundary paths. -/
noncomputable def
    ReparameterizedDerivedTerminalHomotopyGridOverlapCoherence.toRestrictedCompatibleCartanAtlasData3
    [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M]
    (package : CanonicalRootedRealizationPackage skeleton)
    (hcurv : HasConstantSectionalCurvature3 g 1)
    {mesh : ℝ} (hmesh : 0 < mesh)
    (coherence :
      ReparameterizedDerivedTerminalHomotopyGridOverlapCoherence
        package hcurv hmesh) :
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
        package hcurv hmesh x y z
    have hx := package.endpoint_anchoredFamilyState_eq_terminalState x
    have hy := package.endpoint_anchoredFamilyState_eq_terminalState y
    change
      (CartanLocalRigidity.anchoredFamilyState g package.endpoint.target
        package.endpoint.alignment x).germ z =
      (CartanLocalRigidity.anchoredFamilyState g package.endpoint.target
        package.endpoint.alignment y).germ z
    simpa only [hx, hy] using hvalue

/-- A provider of reparameterized derived-terminal realized grids for every
unit-curvature metric supplies complete sphere recognition.

The provider's quantifier order is explicit.  For each metric and curvature
proof it chooses a rooted skeleton and realization package, then a positive
terminal mesh, and finally a coherence object whose per-overlap certificates
still contain the common predecessor index, realized grid, and both smallness
proofs.  This theorem does not assert any of those grid-existence data
automatically. -/
theorem unitConstantCurvatureSphereRecognition3_of_canonicalRootedReparameterizedDerivedTerminalHomotopyGridOverlapCoherence
    [SecondCountableTopology M] [CompactSpace M]
    [ConnectedSpace M] [SimplyConnectedSpace M]
    (provider : ∀ (g : ClosedSmoothRiemannianMetric 3 M),
      ∀ hcurv : HasConstantSectionalCurvature3 g 1,
        ∃ skeleton : RootedCartanPathSkeleton g,
          ∃ package : CanonicalRootedRealizationPackage skeleton,
            ∃ mesh : ℝ,
              ∃ hmesh : 0 < mesh,
                Nonempty
                  (ReparameterizedDerivedTerminalHomotopyGridOverlapCoherence
                    package hcurv hmesh)) :
    UnitConstantCurvatureSphereRecognition3 M := by
  apply
    RoundSphereSimpleConnected.unitConstantCurvatureSphereRecognition3_of_restrictedCompatibleCartanAtlas
  intro g hcurv
  rcases provider g hcurv with
    ⟨skeleton, package, mesh, hmesh, coherence⟩
  rcases coherence with ⟨coherence⟩
  exact
    ⟨coherence.toRestrictedCompatibleCartanAtlasData3
      package hcurv hmesh⟩

end CanonicalRootedRealizationPackage
end CartanCanonicalRootedEndpointAssembly
end Poincare
