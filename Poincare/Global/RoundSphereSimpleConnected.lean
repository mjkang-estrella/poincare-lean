import Poincare.Global.UnitRecognitionNext
import Poincare.Statement

/-!
# Simple connectivity of the literal round three-sphere

`RoundSphere3` and the statement-layer `ThreeSphere` are definitionally the
same unit metric sphere in four-dimensional Euclidean space.  This module
exports the already proved stereographic Van Kampen result under the name used
by the global Cartan-development pipeline, and removes the corresponding
explicit hypothesis from the unit-curvature recognition consumer.
-/

noncomputable section

open scoped Manifold ContDiff

universe u

namespace Poincare
namespace RoundSphereSimpleConnected

/-- The literal round three-sphere used by the Cartan development is simply connected. -/
theorem roundSphere3_simplyConnectedSpace : SimplyConnectedSpace RoundSphere3 :=
  threeSphere_instSimplyConnectedSpace

/--
A total local developing map now discharges unit-curvature recognition with no
additional target-side topology hypothesis.
-/
theorem unitConstantCurvatureSphereRecognition3_of_globalLocalDevelopment
    {M : Type u}
    [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace (ClosedSmoothModel 3) M]
    [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
    [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M]
    (hdev : UnitRecognitionNext.UnitCurvatureGlobalLocalDevelopment3 (M := M)) :
    UnitConstantCurvatureSphereRecognition3 M :=
  UnitRecognitionNext.unitConstantCurvatureSphereRecognition3_of_globalLocalDevelopment
    roundSphere3_simplyConnectedSpace hdev

/--
Pairwise-compatible anchored Cartan germs discharge unit-curvature recognition
without a separately supplied simple-connectivity witness for the target.
-/
theorem unitConstantCurvatureSphereRecognition3_of_compatibleCartanAtlas
    {M : Type u}
    [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace (ClosedSmoothModel 3) M]
    [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
    [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M]
    (hAtlas : UnitRecognitionNext.UnitCurvatureCompatibleCartanAtlas3 (M := M)) :
    UnitConstantCurvatureSphereRecognition3 M :=
  UnitRecognitionNext.unitConstantCurvatureSphereRecognition3_of_compatibleCartanAtlas
    roundSphere3_simplyConnectedSpace hAtlas

/--
Coherently continued Cartan germs discharge unit-curvature recognition with
the round-sphere topology supplied internally.
-/
theorem unitConstantCurvatureSphereRecognition3_of_coherentCartanGerms
    {M : Type u}
    [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace (ClosedSmoothModel 3) M]
    [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
    [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M]
    (hCartan : UnitRecognitionNext.UnitCurvatureCoherentCartanGerms3 (M := M)) :
    UnitConstantCurvatureSphereRecognition3 M :=
  UnitRecognitionNext.unitConstantCurvatureSphereRecognition3_of_coherentCartanGerms
    roundSphere3_simplyConnectedSpace hCartan

/--
The final coherent-Cartan-germ composition no longer carries an independent
simple-connectivity assumption for the target sphere.
-/
theorem poincareConjecture_of_hamiltonConvergence_of_coherentCartanGerms
    (hHamilton :
      ∀ (N : Type u) [TopologicalSpace N] [T2Space N]
        [SecondCountableTopology N]
        [ChartedSpace (ClosedSmoothModel 3) N]
        [IsManifold (closedSmoothModelWithCorners 3) ∞ N]
        [CompactSpace N] [ConnectedSpace N] [SimplyConnectedSpace N],
          HamiltonConvergencePinchedLimit3 N)
    (hCartan :
      ∀ (N : Type u) [TopologicalSpace N] [T2Space N]
        [SecondCountableTopology N]
        [ChartedSpace (ClosedSmoothModel 3) N]
        [IsManifold (closedSmoothModelWithCorners 3) ∞ N]
        [CompactSpace N] [ConnectedSpace N] [SimplyConnectedSpace N],
          UnitRecognitionNext.UnitCurvatureCoherentCartanGerms3 (M := N)) :
    PoincareConjecture.{u} :=
  UnitRecognitionNext.poincareConjecture_of_hamiltonConvergence_of_coherentCartanGerms
    roundSphere3_simplyConnectedSpace hHamilton hCartan

/--
Likewise, pairwise-compatible anchored Cartan atlases compose directly with
Hamilton convergence to imply the repository's Poincare statement.
-/
theorem poincareConjecture_of_hamiltonConvergence_of_compatibleCartanAtlas
    (hHamilton :
      ∀ (N : Type u) [TopologicalSpace N] [T2Space N]
        [SecondCountableTopology N]
        [ChartedSpace (ClosedSmoothModel 3) N]
        [IsManifold (closedSmoothModelWithCorners 3) ∞ N]
        [CompactSpace N] [ConnectedSpace N] [SimplyConnectedSpace N],
          HamiltonConvergencePinchedLimit3 N)
    (hAtlas :
      ∀ (N : Type u) [TopologicalSpace N] [T2Space N]
        [SecondCountableTopology N]
        [ChartedSpace (ClosedSmoothModel 3) N]
        [IsManifold (closedSmoothModelWithCorners 3) ∞ N]
        [CompactSpace N] [ConnectedSpace N] [SimplyConnectedSpace N],
          UnitRecognitionNext.UnitCurvatureCompatibleCartanAtlas3 (M := N)) :
    PoincareConjecture.{u} :=
  UnitRecognitionNext.poincareConjecture_of_hamiltonConvergence_of_compatibleCartanAtlas
    roundSphere3_simplyConnectedSpace hHamilton hAtlas

end RoundSphereSimpleConnected
end Poincare
