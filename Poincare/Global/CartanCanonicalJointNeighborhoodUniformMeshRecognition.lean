import Poincare.Global.DifferentialSuccessorJointEqualityNeighborhood
import Poincare.Global.CartanCanonicalFamilyComparedToGenericSuccessorRadius
import Poincare.Global.CartanCanonicalRootedUniformSuccessorMeshRecognition

/-!
# Canonical rooted recognition from two joint diagonal neighborhoods

The automatic uniform-mesh recognition theorem consumes two raw radius
interfaces.  Both now follow from proof-bearing diagonal-neighborhood
contracts:

* canonical compared-successor stability forgets to the generic successor-
  data neighborhood; and
* the four-variable actual-data equality neighborhood compactifies to a
  state-uniform successor equality ball.

After these conversions, the only completion datum is the existing finite
strict-factor boundary transport contract.  No generic data neighborhood,
numeric equality radius, realized grid, or mesh-feedback premise is supplied
by the caller.
-/

noncomputable section

open Filter
open scoped Manifold ContDiff Topology

namespace Poincare
namespace CartanCanonicalJointNeighborhoodUniformMeshRecognition

set_option linter.unusedSectionVars false

universe u

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace E M]
variable [IsManifold I ∞ M]
variable [CompactSpace M] [ConnectedSpace M]
variable [SimplyConnectedSpace M]

open CartanAtlasRootedPathSkeleton
open CartanCanonicalFamilyComparedToGenericSuccessorRadius
open CartanCanonicalFamilyProvenanceRootedAssembly
open CartanCanonicalRootedEndpointAssembly
open CartanCanonicalRootedReparameterizedUniformRadiusGridAssembly
open CartanCanonicalRootedUniformSuccessorMeshRecognition
open DifferentialSuccessorJointEqualityNeighborhood
open DifferentialUniformSuccessorMesh

/-- The sole post-neighborhood completion boundary.  Every mesh and every
finite successor datum is constructed by the uniform-mesh theorem; this
provider supplies only a rooted realization whose overlap coherence has the
existing finite strict-factor boundary transport field. -/
def UniversalFiniteStrictFactorBoundaryTransportCompletion3 : Prop :=
  ∀ (g : ClosedSmoothRiemannianMetric 3 M),
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
                  package hmesh)

/-- Unit-curvature recognition from canonical successor-provenance stability,
joint actual-data equality stability, and only the remaining finite
strict-factor boundary transport completion.

The generic successor-data neighborhood is derived by forgetting the
canonical comparison field.  The equality radius and its ball theorem are
derived by compactly thickening the joint predecessor/successor/evaluation
diagonal. -/
theorem unitConstantCurvatureSphereRecognition3_of_canonicalComparedNeighborhood_jointEqualityNeighborhood_strictFactorBoundaryTransport
    [SecondCountableTopology M] [SimplyConnectedSpace M]
    (comparedStability : ∀ (g : ClosedSmoothRiemannianMetric 3 M),
      HasConstantSectionalCurvature3 g 1 →
        UniversalComparedSuccessorLocus g ∈
          nhdsSet
            (CartanTargetExponential.successorParameterDiagonal (M := M)))
    (equalityStability : ∀ (g : ClosedSmoothRiemannianMetric 3 M),
      HasConstantSectionalCurvature3 g 1 →
        UniversalSuccessorEqualityNeighborhood g)
    (completion : UniversalFiniteStrictFactorBoundaryTransportCompletion3
      (M := M)) :
    UnitConstantCurvatureSphereRecognition3 M := by
  apply
    unitConstantCurvatureSphereRecognition3_of_canonicalRooted_uniformSuccessorData_uniformEqOnBall_strictFactorBoundaryTransport
  · intro g hcurv
    exact universalSuccessorDataNeighborhood_of_comparedNeighborhood
      (comparedStability g hcurv)
  · intro g hcurv
    exact exists_uniformSuccessorEqOnBall_of_jointNeighborhood
      g (equalityStability g hcurv)
  · exact completion

end CartanCanonicalJointNeighborhoodUniformMeshRecognition
end Poincare
