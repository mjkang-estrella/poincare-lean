/-
Proof-progress blocker for producing the smoothability package layer.

This module does not define the reserved final theorem.  It records the first
constructorless field needed to build the `SmoothabilityPackage` consumed by the
final assembly boundary.
-/

import Poincare.Smoothability

universe u

open scoped Manifold ContDiff

namespace Poincare

/--
The first `SmoothabilityPackage` constructor field.  It is the first
constructorless interface that must be supplied before the later Moise, PL, and
smoothing fields can be assembled.
-/
def SmoothabilityPackageFirstConstructorlessField : Prop :=
  ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace ThreeManifoldModel M]
    [SimplyConnectedSpace M] [CompactSpace M],
      HasMoiseLocalTriangulationCharts M

/--
The same blocker phrased directly for `SmoothabilityPackage`: the first missing
constructor argument is `moiseLocalCharts`.
-/
theorem smoothabilityPackage_requires_moiseLocalCharts
    (package : SmoothabilityPackage.{u}) :
    SmoothabilityPackageFirstConstructorlessField.{u} := by
  intro M _ _ _ _ _
  exact package.moiseLocalCharts M

end Poincare
