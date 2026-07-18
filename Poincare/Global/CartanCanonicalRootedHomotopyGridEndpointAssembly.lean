import Poincare.Global.CartanRootedOverlapHomotopyGrid

/-!
# Canonical rooted endpoint assembly through realized homotopy grids

This module connects the sound rooted-overlap homotopy-grid transport to the
restricted Cartan-atlas recognition interface.  Every overlap certificate is
dependent on its two anchors and overlap point: it retains two independently
supplied terminal paths, one fixed realized homotopy grid, and the horizontal
and vertical smallness proofs for that grid's chosen curvature radius.

The certificates are inputs.  No theorem here asserts that a grid, its
realized differential data, or its mesh bounds exist.  Restricted coherence
therefore preserves the analytic quantifier order while removing the invalid
strict-factor relation between independently chosen endpoint paths.
-/

noncomputable section

open Metric Set
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
open CartanAtlasRootedReachableEndpointTransport
open CartanRootedOverlapHomotopyGrid

variable {g : ClosedSmoothRiemannianMetric 3 M}
variable {skeleton : RootedCartanPathSkeleton g}

/-- The complete proof-bearing payload for one canonical rooted overlap.

The two terminal certificates may use different mesh parameters.  Their only
common endpoint is `z`; simple connectivity constructs the homotopy between
the resulting independent root-to-`z` paths.  The fixed realized grid and its
two smallness fields are precisely the remaining hypotheses consumed by
`RootedOverlapRealizedHomotopyGrid.germ_value_eq_of_small`. -/
structure RootedOverlapHomotopyGridCertificate
    [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M]
    (package : CanonicalRootedRealizationPackage skeleton)
    (hcurv : HasConstantSectionalCurvature3 g 1)
    (x y z : M) where
  leftMesh : ℝ
  rightMesh : ℝ
  leftTerminal : TerminalShortPathCertificate g x z leftMesh
  rightTerminal : TerminalShortPathCertificate g y z rightMesh
  grid : RootedOverlapRealizedHomotopyGrid package.endpoint
    leftTerminal rightTerminal
  horizontalSmall : grid.HorizontalSmall (grid.commonMeshRadius hcurv)
  verticalSmall : grid.VerticalSmall (grid.commonMeshRadius hcurv)

namespace RootedOverlapHomotopyGridCertificate

/-- A complete overlap certificate identifies the two actual terminal Cartan
germ values at its overlap point. -/
theorem germ_value_eq
    [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M]
    (package : CanonicalRootedRealizationPackage skeleton)
    (hcurv : HasConstantSectionalCurvature3 g 1)
    (x y z : M)
    (certificate :
      RootedOverlapHomotopyGridCertificate package hcurv x y z) :
    (package.endpoint.terminalState x).germ z =
      (package.endpoint.terminalState y).germ z :=
  certificate.grid.germ_value_eq_of_small hcurv
    certificate.horizontalSmall certificate.verticalSmall

end RootedOverlapHomotopyGridCertificate

/-- Restricted canonical overlap coherence supplied by honest realized
homotopy-grid certificates.

The chosen domains are open anchor neighborhoods contained in the actual
terminal Cartan sources.  A certificate is required only for a point in a
chosen domain intersection, and its type remembers that exact pair of anchors
and overlap point. -/
structure RestrictedHomotopyGridOverlapCoherence
    [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M]
    (package : CanonicalRootedRealizationPackage skeleton)
    (hcurv : HasConstantSectionalCurvature3 g 1) where
  domain : M → Set M
  isOpen_domain : ∀ x : M, IsOpen (domain x)
  anchor_mem_domain : ∀ x : M, x ∈ domain x
  domain_subset_source : ∀ x : M,
    domain x ⊆ (package.endpoint.terminalState x).germ.source
  overlapCertificate : ∀ x y z : M,
    z ∈ domain x ∩ domain y →
      RootedOverlapHomotopyGridCertificate package hcurv x y z

/-- Restricted homotopy-grid coherence constructs exactly the restricted
compatible Cartan atlas consumed by diagonal gluing. -/
def RestrictedHomotopyGridOverlapCoherence.toRestrictedCompatibleCartanAtlasData3
    [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M]
    (package : CanonicalRootedRealizationPackage skeleton)
    (hcurv : HasConstantSectionalCurvature3 g 1)
    (coherence : RestrictedHomotopyGridOverlapCoherence package hcurv) :
    UnitRecognitionNext.RestrictedCompatibleCartanAtlasData3 g where
  target := package.endpoint.target
  alignment := package.endpoint.alignment
  domain := coherence.domain
  isOpen_domain := coherence.isOpen_domain
  anchor_mem_domain := coherence.anchor_mem_domain
  domain_subset_source := by
    intro x z hz
    have hterminal :
        z ∈ (package.endpoint.terminalState x).germ.source :=
      coherence.domain_subset_source x hz
    have hx := package.endpoint_anchoredFamilyState_eq_terminalState x
    change z ∈
      (CartanLocalRigidity.anchoredFamilyState g package.endpoint.target
        package.endpoint.alignment x).germ.source
    simpa only [hx] using hterminal
  compatible := by
    intro x y z hz
    have hvalue :=
      (coherence.overlapCertificate x y z hz).germ_value_eq
        package hcurv x y z
    have hx := package.endpoint_anchoredFamilyState_eq_terminalState x
    have hy := package.endpoint_anchoredFamilyState_eq_terminalState y
    change
      (CartanLocalRigidity.anchoredFamilyState g package.endpoint.target
        package.endpoint.alignment x).germ z =
      (CartanLocalRigidity.anchoredFamilyState g package.endpoint.target
        package.endpoint.alignment y).germ z
    simpa only [hx, hy] using hvalue

/-- Canonical rooted restricted homotopy-grid coherence supplies the complete
unit-curvature sphere-recognition interface.  The universally quantified
completion hypothesis supplies, rather than postulates the existence of, the
canonical package and all overlap certificates for each unit-curvature
metric. -/
theorem unitConstantCurvatureSphereRecognition3_of_canonicalRootedRestrictedHomotopyGridOverlapCoherence
    [SecondCountableTopology M] [CompactSpace M]
    [ConnectedSpace M] [SimplyConnectedSpace M]
    (completion : ∀ (g : ClosedSmoothRiemannianMetric 3 M),
      ∀ hcurv : HasConstantSectionalCurvature3 g 1,
        ∃ skeleton : RootedCartanPathSkeleton g,
          ∃ package : CanonicalRootedRealizationPackage skeleton,
            Nonempty
              (RestrictedHomotopyGridOverlapCoherence package hcurv)) :
    UnitConstantCurvatureSphereRecognition3 M := by
  apply
    RoundSphereSimpleConnected.unitConstantCurvatureSphereRecognition3_of_restrictedCompatibleCartanAtlas
  intro g hcurv
  rcases completion g hcurv with
    ⟨skeleton, package, coherence⟩
  rcases coherence with ⟨coherence⟩
  exact
    ⟨coherence.toRestrictedCompatibleCartanAtlasData3 package hcurv⟩

/-- The minimal payload on the canonical terminal-restricted domains.

Domain openness, anchor membership, and source inclusion are inherited from
`terminalRestrictedDomain`.  The only field is the dependent per-overlap
homotopy-grid certificate.  In particular, this structure does not claim that
membership in the terminal domain automatically produces such a certificate.
-/
structure TerminalRestrictedHomotopyGridOverlapCoherence
    [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M]
    (package : CanonicalRootedRealizationPackage skeleton)
    (hcurv : HasConstantSectionalCurvature3 g 1)
    {mesh : ℝ} (hmesh : 0 < mesh) where
  overlapCertificate : ∀ x y z : M,
    z ∈ package.terminalRestrictedDomain hmesh x ∩
        package.terminalRestrictedDomain hmesh y →
      RootedOverlapHomotopyGridCertificate package hcurv x y z

/-- The terminal-domain payload supplies the general restricted coherence
record with all domain obligations discharged canonically. -/
def TerminalRestrictedHomotopyGridOverlapCoherence.toRestrictedHomotopyGridOverlapCoherence
    [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M]
    (package : CanonicalRootedRealizationPackage skeleton)
    (hcurv : HasConstantSectionalCurvature3 g 1)
    {mesh : ℝ} (hmesh : 0 < mesh)
    (coherence :
      TerminalRestrictedHomotopyGridOverlapCoherence
        package hcurv hmesh) :
    RestrictedHomotopyGridOverlapCoherence package hcurv where
  domain := package.terminalRestrictedDomain hmesh
  isOpen_domain := package.isOpen_terminalRestrictedDomain hmesh
  anchor_mem_domain := package.anchor_mem_terminalRestrictedDomain hmesh
  domain_subset_source := package.terminalRestrictedDomain_subset_source hmesh
  overlapCertificate := coherence.overlapCertificate

/-- The minimal terminal-restricted homotopy-grid payload is already enough
for complete unit-curvature sphere recognition.  Grid and certificate
existence remain explicit in the completion argument. -/
theorem unitConstantCurvatureSphereRecognition3_of_canonicalRootedTerminalRestrictedHomotopyGridOverlapCoherence
    [SecondCountableTopology M] [CompactSpace M]
    [ConnectedSpace M] [SimplyConnectedSpace M]
    (completion : ∀ (g : ClosedSmoothRiemannianMetric 3 M),
      ∀ hcurv : HasConstantSectionalCurvature3 g 1,
        ∃ skeleton : RootedCartanPathSkeleton g,
          ∃ package : CanonicalRootedRealizationPackage skeleton,
            ∃ mesh : ℝ,
              ∃ hmesh : 0 < mesh,
                Nonempty
                  (TerminalRestrictedHomotopyGridOverlapCoherence
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
