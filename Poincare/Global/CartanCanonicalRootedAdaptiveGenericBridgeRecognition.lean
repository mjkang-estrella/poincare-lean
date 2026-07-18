import Poincare.Global.CartanGenericRootedAdaptiveFiniteGridRecognition

/-!
# Canonical-data adapter for adaptive generic Cartan recognition

The canonical target-exponential family is the convenient family for proving
joint successor-data stability.  The finite post-realization recognition
pipeline, however, is formulated for the legacy generic Cartan successor and
its rooted endpoint family.

This module records the exact adapter between those two interfaces.  It keeps
the existence-only `CanonicalDataNeighborhoodToGenericDataNeighborhood`
bridge explicit: no selected compared successor, target-chart agreement, or
automatic canonical-to-generic conversion is introduced here.  Once the
bridge has produced the legacy generic successor-data neighborhood, the
existing adaptive finite-grid recognition theorem applies unchanged.
-/

noncomputable section

open scoped Manifold ContDiff Topology

namespace Poincare
namespace CartanCanonicalRootedAdaptiveGenericBridgeRecognition

universe u

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

open CartanCanonicalRootedDirectGenericNeighborhoodRecognition
open CartanCanonicalRootedReparameterizedUniformRadiusGridAssembly
open CartanGenericRootedAdaptiveFiniteGridRecognition
open CartanTargetExponential

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace E M]
variable [IsManifold I ∞ M]
variable [CompactSpace M] [ConnectedSpace M]

/--
Canonical successor-data stability feeds the legacy adaptive recognition
endpoint through the explicit existence-only canonical-to-generic bridge.

The completion is indexed by the generic successor certificate and endpoint
obtained *after* applying that bridge.  Thus the statement does not identify
canonical and generic successor data, nor does it hide a compared-successor
continuation premise.
-/
theorem
    unitConstantCurvatureSphereRecognition3_of_canonicalDataNeighborhood_genericBridge_postRealizationGridCoherence
    [SecondCountableTopology M] [SimplyConnectedSpace M]
    (canonicalStability : ∀ (g : ClosedSmoothRiemannianMetric 3 M),
      HasConstantSectionalCurvature3 g 1 →
        UniversalSuccessorDataNeighborhood canonicalFamily g)
    (genericBridge : ∀ (g : ClosedSmoothRiemannianMetric 3 M),
      HasConstantSectionalCurvature3 g 1 →
        CanonicalDataNeighborhoodToGenericDataNeighborhood g)
    (completion : ∀ (g : ClosedSmoothRiemannianMetric 3 M),
      ∀ hcurv : HasConstantSectionalCurvature3 g 1,
        let genericStability :=
          genericBridge g hcurv (canonicalStability g hcurv)
        let successor :=
          uniformGenericSuccessorRadiusCertificateOfNeighborhood
            g genericStability
        let endpoint := rootedEndpointOfUniformGenericSuccessorRadius
          successor
        ∃ mesh : ℝ,
          ∃ hmesh : 0 < mesh,
            Nonempty
              (GenericUniformRadiusPostRealizationGridCoherence
                successor endpoint hcurv hmesh)) :
    UnitConstantCurvatureSphereRecognition3 M := by
  apply
    unitConstantCurvatureSphereRecognition3_of_genericDataNeighborhood_postRealizationGridCoherence
      (dataStability := fun g hcurv ↦
        genericBridge g hcurv (canonicalStability g hcurv))
  exact completion

end CartanCanonicalRootedAdaptiveGenericBridgeRecognition
end Poincare
