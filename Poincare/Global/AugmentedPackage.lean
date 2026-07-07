import Poincare.Global.AugmentedC1
import Poincare.Global.GeodesicDerivative

/-!
# Augmented flow compact-tube Taylor package

This module exports the compact-uniform Taylor remainder for the augmented
chart-Christoffel field.  It is the stage-three input needed by the
second-variation fixed-time derivative argument.
-/

noncomputable section

open Metric Set
open scoped Manifold ContDiff Topology RealInnerProductSpace NNReal

namespace Poincare
namespace GeodesicTransport

universe u

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "E" => ClosedSmoothModel n

omit [T2Space M] in
/--
Uniform Taylor remainder for the chart-Christoffel augmented
geodesic/first-variation field on a compact convex augmented tube.

The derivative term is the second-variation operator, i.e. the Fréchet
linearization of the augmented vector field.
-/
theorem chartChristoffel_augmentedGeodesicFlowField_uniform_taylor_remainder_norm_le_on_compact_convex
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M)
    {Kset : Set ((E × E) × (E × E))}
    (hK_compact : IsCompact Kset) (hK_convex : Convex ℝ Kset) :
    ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ base ∈ Kset, ∀ q ∈ Kset,
      ‖q - base‖ ≤ δ →
        ‖augmentedGeodesicFlowField (chartChristoffelField g x₀) q -
            augmentedGeodesicFlowField (chartChristoffelField g x₀) base -
              secondVariationFlowOperator
                (chartChristoffelField g x₀) base (q - base)‖ ≤
          ε * ‖q - base‖ := by
  rcases
      exists_lipschitzOnWith_chartChristoffel_augmentedGeodesicFlowField_closedBall
        (g := g) (x₀ := x₀) (p := (0 : (E × E) × (E × E))) (a := 0) with
    ⟨haug, _K, _hLip⟩
  simpa [secondVariationFlowOperator] using
    (uniform_taylor_remainder_norm_le_on_compact_convex
      (f := augmentedGeodesicFlowField (chartChristoffelField g x₀))
      (K := Kset) haug hK_compact hK_convex)

end GeodesicTransport
end Poincare
