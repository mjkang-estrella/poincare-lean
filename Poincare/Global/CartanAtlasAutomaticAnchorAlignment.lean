import Poincare.Global.CartanAtlasRealizedEndpointTransport
import Poincare.Global.CartanAtlasTargetCoherence
import Poincare.Global.TangentAlignmentExists

/-!
# Constant-target specialization and automatic tangent alignments

`CartanMap.tangentAlignment_nonempty` constructs an alignment after a target
point has been chosen.  The target field itself is not automatic: overlap
compatibility forces it to equal the developing-map value, as proved in
`CartanAtlasTargetCoherence`.

This module retains the useful constant-north-pole specialization as a strong
conditional interface.  It automatically chooses the pointwise alignments,
but its transport field is correspondingly much stronger than general Cartan
globalization: if it produced compatibility, every local germ source would be
forced to contain only its anchor.  It must therefore not be treated as the
general completion boundary.
-/

noncomputable section

open Set
open scoped Manifold ContDiff Topology

namespace Poincare
namespace CartanAtlasAutomaticAnchorAlignment

universe u

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace E M]
variable [IsManifold I ∞ M]

open CartanAtlasRealizedEndpointTransport

/-- Diagnostic specialization using the concrete north pole at every source
point.  General developing-map targets cannot be chosen this way. -/
def canonicalRoundSphereTarget (_ : M) : RoundSphere3 :=
  threeSphere_northPole

/-- Choose the pointwise metric alignment whose existence is already proved
for every source point and every round-sphere target point. -/
def canonicalTangentAlignment
    (g : ClosedSmoothRiemannianMetric 3 M) (x : M) :
    CartanMap.TangentAlignment g x (canonicalRoundSphereTarget x) :=
  Classical.choice
    (CartanMap.tangentAlignment_nonempty
      g x (canonicalRoundSphereTarget x))

/-- Strict-factor endpoint transport under the strong constant-target
specialization.

For each overlap point this field supplies the realized finite refinement and
its validated gap transports.  Terminal equality, pairwise germ compatibility,
and the global Cartan atlas are all derived downstream.  Target coherence shows
that this record is not a replacement for constructing a genuine continued
target field. -/
structure CanonicalStrictFactorEndpointTransportAtlasData
    (g : ClosedSmoothRiemannianMetric 3 M) where
  transport : ∀ x y z : M,
    z ∈
        (CartanLocalRigidity.anchoredFamilyState
          g canonicalRoundSphereTarget (canonicalTangentAlignment g) x).germ.source ∩
        (CartanLocalRigidity.anchoredFamilyState
          g canonicalRoundSphereTarget (canonicalTangentAlignment g) y).germ.source →
      CommonRootStrictFactorTransport
        (CartanLocalRigidity.anchoredFamilyState
          g canonicalRoundSphereTarget (canonicalTangentAlignment g) x)
        (CartanLocalRigidity.anchoredFamilyState
          g canonicalRoundSphereTarget (canonicalTangentAlignment g) y) z

/-- Reinsert the automatically constructed local choices into the existing
strict-factor endpoint interface. -/
def CanonicalStrictFactorEndpointTransportAtlasData.toStrictFactor
    {g : ClosedSmoothRiemannianMetric 3 M}
    (data : CanonicalStrictFactorEndpointTransportAtlasData g) :
    StrictFactorEndpointTransportAtlasData g where
  target := canonicalRoundSphereTarget
  alignment := canonicalTangentAlignment g
  transport := data.transport

/-- The constant-target strict-factor hypothesis conditionally constructs the
compatible Cartan atlas. -/
theorem compatibleCartanAtlas_of_canonicalStrictFactorEndpointTransport
    (transport : ∀ (g : ClosedSmoothRiemannianMetric 3 M),
      HasConstantSectionalCurvature3 g 1 →
        CanonicalStrictFactorEndpointTransportAtlasData g) :
    UnitRecognitionNext.UnitCurvatureCompatibleCartanAtlas3 (M := M) :=
  compatibleCartanAtlas_of_strictFactorEndpointTransport
    (fun g hcurv ↦ (transport g hcurv).toStrictFactor)

/-- The reduced strict-factor transport constructs sphere recognition on the
current smooth target. -/
theorem unitConstantCurvatureSphereRecognition3_of_canonicalStrictFactorEndpointTransport
    [SecondCountableTopology M] [CompactSpace M] [ConnectedSpace M]
    [SimplyConnectedSpace M]
    (transport : ∀ (g : ClosedSmoothRiemannianMetric 3 M),
      HasConstantSectionalCurvature3 g 1 →
        CanonicalStrictFactorEndpointTransportAtlasData g) :
    UnitConstantCurvatureSphereRecognition3 M :=
  unitConstantCurvatureSphereRecognition3_of_strictFactorEndpointTransport
    (fun g hcurv ↦ (transport g hcurv).toStrictFactor)

/-- Universal constant-target strict-factor transport.  This is a diagnostic
strong hypothesis, not the general Cartan globalization boundary. -/
def UniversalCanonicalStrictFactorEndpointTransportAtlasData :
    Type (u + 1) :=
  ∀ (N : Type u) [TopologicalSpace N] [T2Space N]
    [SecondCountableTopology N]
    [ChartedSpace (ClosedSmoothModel 3) N]
    [IsManifold (closedSmoothModelWithCorners 3) ∞ N]
    [CompactSpace N] [ConnectedSpace N] [SimplyConnectedSpace N]
    (g : ClosedSmoothRiemannianMetric 3 N),
      HasConstantSectionalCurvature3 g 1 →
        CanonicalStrictFactorEndpointTransportAtlasData g

/-- The universal reduced transport provider supplies the complete unit
constant-curvature recognition interface. -/
theorem universalUnitRecognition_of_canonicalStrictFactorEndpointTransport
    (transport :
      UniversalCanonicalStrictFactorEndpointTransportAtlasData.{u}) :
    ∀ (N : Type u) [TopologicalSpace N] [T2Space N]
      [SecondCountableTopology N]
      [ChartedSpace (ClosedSmoothModel 3) N]
      [IsManifold (closedSmoothModelWithCorners 3) ∞ N]
      [CompactSpace N] [ConnectedSpace N] [SimplyConnectedSpace N],
        UnitConstantCurvatureSphereRecognition3 N := by
  intro N _top _t2 _second _charted _manifold _compact _connected _simply
  exact
    unitConstantCurvatureSphereRecognition3_of_canonicalStrictFactorEndpointTransport
      (fun g hcurv ↦ transport N g hcurv)

/-- Hamilton's reduced positive-Einstein limit together with the strong
constant-target strict-factor transport field conditionally proves the smooth
Poincare statement. -/
theorem poincareConjecture_of_hamiltonConvergenceCore_of_canonicalStrictFactorEndpointTransport
    (hHamilton :
      ∀ (N : Type u) [TopologicalSpace N] [T2Space N]
        [SecondCountableTopology N]
        [ChartedSpace (ClosedSmoothModel 3) N]
        [IsManifold (closedSmoothModelWithCorners 3) ∞ N]
        [CompactSpace N] [ConnectedSpace N] [SimplyConnectedSpace N],
          HamiltonConvergencePinchedLimit3Core N)
    (transport :
      UniversalCanonicalStrictFactorEndpointTransportAtlasData.{u}) :
    PoincareConjecture.{u} :=
  poincareConjecture_of_hamiltonConvergenceCore_of_unitRecognition
    hHamilton
    (universalUnitRecognition_of_canonicalStrictFactorEndpointTransport
      transport)

end CartanAtlasAutomaticAnchorAlignment
end Poincare
