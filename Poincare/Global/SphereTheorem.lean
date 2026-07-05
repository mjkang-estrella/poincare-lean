import Poincare.Global.ScalarVariation
import Poincare.Global.Statement

/-!
# Conditional sphere theorem interface

This module isolates the positive space-form recognition theorem as a named
hypothesis and uses it to connect the proved constant-curvature limit algebra
to the statement-layer sphere conclusion.
-/

noncomputable section

open Bundle FiberBundle
open scoped Manifold ContDiff

universe u

namespace Poincare

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
variable [ChartedSpace (ClosedSmoothModel 3) M]
variable [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
variable [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M]

/--
The narrow positive constant-curvature space-form recognition interface.

This is the named hypothesis for the hard differential-geometric input: the
Killing-Hopf space-form theorem, specialized to closed connected simply
connected smooth 3-manifolds.  In mathematical terms, a complete simply
connected Riemannian manifold of constant sectional curvature `κ > 0` is
isometric to the round sphere of radius `1 / sqrt κ`; hence, in dimension three,
it is homeomorphic to the standard `S^3`.  References: Killing-Hopf space-form
classification, as in do Carmo, *Riemannian Geometry*, Chapter 8, or Petersen,
*Riemannian Geometry*, section on space forms.

The Lean statement deliberately exposes only the downstream topological
conclusion and consumes the already-proved repository predicate
`HasConstantSectionalCurvature3`.  It is a hypothesis interface, not a global
postulate and not an instantiable certificate.
-/
def PositiveConstantCurvatureSpaceForm3 (M : Type u)
    [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace (ClosedSmoothModel 3) M]
    [IsManifold (closedSmoothModelWithCorners 3) ∞ M]
    [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M] : Prop :=
  ∀ (g : ClosedSmoothRiemannianMetric 3 M) (κ : ℝ),
    HasConstantSectionalCurvature3 g κ →
      0 < κ →
        Nonempty
          (M ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) (1 : ℝ))

/-- The space-form interface expands to the intended theorem-shaped hypothesis. -/
theorem positiveConstantCurvatureSpaceForm3_eq :
    PositiveConstantCurvatureSpaceForm3 M =
      (∀ (g : ClosedSmoothRiemannianMetric 3 M) (κ : ℝ),
        HasConstantSectionalCurvature3 g κ →
          0 < κ →
            Nonempty
              (M ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) (1 : ℝ))) :=
  rfl

/--
Shape check for the target of the interface: on the literal statement-layer
round sphere, the requested homeomorphism target is inhabited by the identity.
-/
theorem positiveConstantCurvatureSpaceForm3_roundSphere_target_nonempty :
    Nonempty
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) (1 : ℝ) ≃ₜ
        Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) (1 : ℝ)) :=
  ⟨Homeomorph.refl _⟩

end Poincare
