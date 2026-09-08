import Poincare.Global.CartanSuppliedUnitRecognition

/-!
# Universal unit-curvature sphere recognition

The mission endpoint of the Cartan developing-map route, under its registered
name.  It is the supplied patch construction's universal recognition theorem:
every closed simply connected smooth 3-manifold carrying a unit-curvature
metric is recognized as the 3-sphere.  No H1/H2 joint-neighborhood premise,
patch cover, switch control, or atlas-compatibility hypothesis remains.
-/

set_option autoImplicit false
namespace Poincare
universe u

/-- Universal unit-curvature sphere recognition (Killing-Hopf endpoint of the
Cartan route), proved by the supplied fixed-chart patch construction. -/
theorem universal_unit_constant_curvature_sphere_recognition :
    CartanTwoNeighborhoodDevelopment.UniversalUnitConstantCurvatureSphereRecognitionStatement.{u} :=
  CartanSuppliedUnitRecognition.universal_unitRecognition

end Poincare
