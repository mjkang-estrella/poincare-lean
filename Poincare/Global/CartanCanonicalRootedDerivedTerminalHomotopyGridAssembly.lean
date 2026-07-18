import Poincare.Global.CartanCanonicalRootedHomotopyGridEndpointAssembly
import Poincare.Global.CartanTerminalShortPathScheduleFree

/-!
# Canonically derived terminal paths for rooted homotopy grids

The schedule-free terminal-radius theorem gives a short path from an anchor
to every point in its restricted terminal domain.  This module fixes one such
path by classical choice and removes both terminal-path certificates from the
per-overlap completion payload.

What remains is deliberately explicit: one realized homotopy grid for the two
derived root-to-overlap paths, including its boundary predecessor traces and
all cross-cell differential data, plus horizontal and vertical smallness at
that fixed grid's chosen radius.  In particular, no common subdivision or
grid realization is inferred from the two unrelated endpoint samplings.
-/

noncomputable section

open Set
open scoped Manifold ContDiff Topology unitInterval

namespace Poincare
namespace CartanCanonicalRootedEndpointAssembly
namespace CanonicalRootedRealizationPackage

universe u

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace E M]
variable [IsManifold I ∞ M]

open CartanAtlasRootedPathSkeleton
open CartanRootedOverlapHomotopyGrid
open CartanTerminalShortPathScheduleFree

variable {g : ClosedSmoothRiemannianMetric 3 M}
variable {skeleton : RootedCartanPathSkeleton g}

/-- The fixed terminal path selected from membership in one schedule-free
terminal restricted domain. -/
noncomputable def derivedTerminalPath
    [CompactSpace M] [ConnectedSpace M]
    (package : CanonicalRootedRealizationPackage skeleton)
    {mesh : ℝ} (hmesh : 0 < mesh) {y z : M}
    (hz : z ∈ scheduleFreeTerminalRestrictedDomain package hmesh y) :
    TerminalShortPathCertificate g y z mesh :=
  Classical.choice
    (terminalShortPathCertificate_of_mem_scheduleFreeTerminalRestrictedDomain
      package hmesh hz)

/-- The minimal proof-bearing payload for one overlap after its two terminal
paths have been canonically derived from restricted-domain membership.

The grid field still retains every realized row, rung, cross-cell datum, and
left/right predecessor trace from `RootedOverlapRealizedHomotopyGrid`.  Its
existence and both mesh bounds are honest assumptions of this record. -/
structure DerivedTerminalRootedOverlapHomotopyGridCertificate
    [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M]
    (package : CanonicalRootedRealizationPackage skeleton)
    (hcurv : HasConstantSectionalCurvature3 g 1)
    {mesh : ℝ} (hmesh : 0 < mesh)
    (x y z : M)
    (hz : z ∈
      scheduleFreeTerminalRestrictedDomain package hmesh x ∩
        scheduleFreeTerminalRestrictedDomain package hmesh y) where
  grid : RootedOverlapRealizedHomotopyGrid package.endpoint
    (derivedTerminalPath package hmesh hz.1)
    (derivedTerminalPath package hmesh hz.2)
  horizontalSmall : grid.HorizontalSmall (grid.commonMeshRadius hcurv)
  verticalSmall : grid.VerticalSmall (grid.commonMeshRadius hcurv)

namespace DerivedTerminalRootedOverlapHomotopyGridCertificate

/-- Reinsert the canonically derived terminal paths into the general
per-overlap homotopy-grid certificate. -/
noncomputable def toRootedOverlapHomotopyGridCertificate
    [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M]
    (package : CanonicalRootedRealizationPackage skeleton)
    (hcurv : HasConstantSectionalCurvature3 g 1)
    {mesh : ℝ} (hmesh : 0 < mesh)
    (x y z : M)
    {hz : z ∈
      scheduleFreeTerminalRestrictedDomain package hmesh x ∩
        scheduleFreeTerminalRestrictedDomain package hmesh y}
    (certificate :
      DerivedTerminalRootedOverlapHomotopyGridCertificate
        package hcurv hmesh x y z hz) :
    RootedOverlapHomotopyGridCertificate package hcurv x y z where
  leftMesh := mesh
  rightMesh := mesh
  leftTerminal := derivedTerminalPath package hmesh hz.1
  rightTerminal := derivedTerminalPath package hmesh hz.2
  grid := certificate.grid
  horizontalSmall := certificate.horizontalSmall
  verticalSmall := certificate.verticalSmall

/-- The derived-terminal certificate therefore proves equality of the actual
terminal Cartan germ values at the overlap point. -/
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
      DerivedTerminalRootedOverlapHomotopyGridCertificate
        package hcurv hmesh x y z hz) :
    (package.endpoint.terminalState x).germ z =
      (package.endpoint.terminalState y).germ z :=
  (certificate.toRootedOverlapHomotopyGridCertificate
    package hcurv hmesh x y z).germ_value_eq package hcurv x y z

end DerivedTerminalRootedOverlapHomotopyGridCertificate

/-- Minimal coherence on the canonical schedule-free terminal domains.

Terminal paths, domain topology, anchor membership, and source inclusion are
all derived.  The sole field supplies the still-nonautomatic realized-grid and
smallness payload separately for each actual overlap. -/
structure DerivedTerminalHomotopyGridOverlapCoherence
    [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M]
    (package : CanonicalRootedRealizationPackage skeleton)
    (hcurv : HasConstantSectionalCurvature3 g 1)
    {mesh : ℝ} (hmesh : 0 < mesh) where
  overlapCertificate : ∀ x y z : M,
    ∀ hz : z ∈
      scheduleFreeTerminalRestrictedDomain package hmesh x ∩
        scheduleFreeTerminalRestrictedDomain package hmesh y,
      DerivedTerminalRootedOverlapHomotopyGridCertificate
        package hcurv hmesh x y z hz

/-- Derived-terminal coherence supplies the existing general restricted
homotopy-grid coherence interface. -/
noncomputable def DerivedTerminalHomotopyGridOverlapCoherence.toRestrictedHomotopyGridOverlapCoherence
    [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M]
    (package : CanonicalRootedRealizationPackage skeleton)
    (hcurv : HasConstantSectionalCurvature3 g 1)
    {mesh : ℝ} (hmesh : 0 < mesh)
    (coherence :
      DerivedTerminalHomotopyGridOverlapCoherence package hcurv hmesh) :
    RestrictedHomotopyGridOverlapCoherence package hcurv where
  domain := scheduleFreeTerminalRestrictedDomain package hmesh
  isOpen_domain := isOpen_scheduleFreeTerminalRestrictedDomain package hmesh
  anchor_mem_domain :=
    anchor_mem_scheduleFreeTerminalRestrictedDomain package hmesh
  domain_subset_source :=
    scheduleFreeTerminalRestrictedDomain_subset_source package hmesh
  overlapCertificate := by
    intro x y z hz
    exact
      (coherence.overlapCertificate x y z hz).toRootedOverlapHomotopyGridCertificate
        package hcurv hmesh x y z

/-- The minimal derived-terminal homotopy-grid payload suffices for complete
unit-curvature sphere recognition.

The completion argument must still construct one realized grid with valid
boundary traces and chosen-radius horizontal/vertical smallness on every
overlap; this theorem does not assert those analytic data exist. -/
theorem unitConstantCurvatureSphereRecognition3_of_canonicalRootedDerivedTerminalHomotopyGridOverlapCoherence
    [SecondCountableTopology M] [CompactSpace M]
    [ConnectedSpace M] [SimplyConnectedSpace M]
    (completion : ∀ (g : ClosedSmoothRiemannianMetric 3 M),
      ∀ hcurv : HasConstantSectionalCurvature3 g 1,
        ∃ skeleton : RootedCartanPathSkeleton g,
          ∃ package : CanonicalRootedRealizationPackage skeleton,
            ∃ mesh : ℝ,
              ∃ hmesh : 0 < mesh,
                Nonempty
                  (DerivedTerminalHomotopyGridOverlapCoherence
                    package hcurv hmesh)) :
    UnitConstantCurvatureSphereRecognition3 M := by
  apply
    unitConstantCurvatureSphereRecognition3_of_canonicalRootedRestrictedHomotopyGridOverlapCoherence
  intro g hcurv
  rcases completion g hcurv with
    ⟨skeleton, package, mesh, hmesh, coherence⟩
  refine ⟨skeleton, package, ?_⟩
  rcases coherence with ⟨coherence⟩
  exact
    ⟨coherence.toRestrictedHomotopyGridOverlapCoherence
      package hcurv hmesh⟩

end CanonicalRootedRealizationPackage
end CartanCanonicalRootedEndpointAssembly
end Poincare
