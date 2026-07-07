import Poincare.Global.GeodesicDerivative
import Poincare.Global.ThirdVariation

/-!
# C1 field package for the doubly augmented chart flow

This module exports the level-three compact-tube Taylor remainder for the
doubly augmented geodesic/first-variation field.  It is the Heine-Cantor
`C1`-with-modulus input needed before replaying the third-variation residual
comparison.
-/

noncomputable section

set_option maxHeartbeats 1000000

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
local notation "A" => (E × E) × (E × E)

omit [T2Space M] in
/--
Uniform Taylor remainder for the doubly augmented chart-Christoffel field on a
compact convex third-variation tube.

The field is
`(z, ξ) ↦ (F z, D F z ξ)`, where
`F = augmentedGeodesicFlowField (chartChristoffelField g x₀)`.
The proof obtains `ContDiff ℝ 1` for this field from the previously exported
`ContDiff ℝ 2` regularity of `F`, then applies the generic compact-uniform
Taylor theorem.
-/
theorem chartChristoffel_doublyAugmentedGeodesicFlowField_uniform_taylor_remainder_norm_le_on_compact_convex
    (g : ClosedSmoothRiemannianMetric n M) (x₀ : M)
    {Kset : Set (A × A)}
    (hK_compact : IsCompact Kset) (hK_convex : Convex ℝ Kset) :
    let doubleF : A × A → A × A := fun y =>
      let F : A → A :=
        augmentedGeodesicFlowField (chartChristoffelField g x₀)
      (F y.1, (fderiv ℝ F y.1) y.2)
    ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ base ∈ Kset, ∀ q ∈ Kset,
      ‖q - base‖ ≤ δ →
        ‖doubleF q - doubleF base -
            fderiv ℝ doubleF base (q - base)‖ ≤
          ε * ‖q - base‖ := by
  let Γ : E → E →L[ℝ] E →L[ℝ] E := chartChristoffelField g x₀
  let F : A → A := augmentedGeodesicFlowField Γ
  let doubleF : A × A → A × A := fun y =>
    (F y.1, (fderiv ℝ F y.1) y.2)
  rcases
      exists_lipschitzOnWith_chartChristoffel_augmentedGeodesicFlowField_two_closedBall
        (g := g) (x₀ := x₀) (p := (0 : A)) (a := 0) with
    ⟨hF_two, _hLip⟩
  have hbase : ContDiff ℝ 1 (fun y : A × A => F y.1) :=
    (hF_two.of_le (by norm_num)).comp contDiff_fst
  have hlin :
      ContDiff ℝ 1
        (fun y : A × A => (fderiv ℝ F y.1 : A →L[ℝ] A) y.2) := by
    simpa [F, Γ] using
      (hF_two.contDiff_fderiv_apply (m := 1) (by norm_num))
  have hdouble : ContDiff ℝ 1 doubleF := by
    simpa [doubleF] using hbase.prodMk hlin
  simpa [doubleF, F, Γ] using
    uniform_taylor_remainder_norm_le_on_compact_convex
      (f := doubleF) (K := Kset) hdouble hK_compact hK_convex

end GeodesicTransport
end Poincare
