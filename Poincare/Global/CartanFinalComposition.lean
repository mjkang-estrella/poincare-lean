import Poincare.Global.CartanCascade
import Poincare.Global.CartanEquivUpgrade

/-!
# Cartan final composition boundary

This module records the scale normalization needed by the final Cartan
composition and isolates the remaining unexported bridge.

For a fixed hosted strict-derivative time `T`, the pointwise choice
`2 * ‖v‖ / T` makes the `CartanScaleGeneric` working data coincide with the
strict-derivative data based at `T⁻¹ • v`.  This is the final-radius
composition normalization: the scale consumer is pointwise in `v`, so this
choice can be made after the common shrunk ball has supplied its fixed source
and target times.

The remaining blocker is not this scale bookkeeping.  The action-equation
theorem still requires the following endpoint identification for each
transverse component:

```
(Ψ (CartanPullback.transversePart
      (CartanMap.sourceAnchorChartMetric g x₀) v u) T).1 =
  (Φ (CartanPullback.transversePart
      (CartanMap.sourceAnchorChartMetric g x₀) v u) (speed * T)).1
```

No exported theorem currently converts the hosted linearized family produced
by `CartanCascade` into this rescaled harmonic endpoint equality.
-/

noncomputable section

open Bundle
open scoped Manifold ContDiff Topology RealInnerProductSpace

namespace Poincare
namespace CartanFinalComposition

universe u

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M]
variable [ChartedSpace E M]
variable [IsManifold I ∞ M]

/-- The pointwise `δ` that makes `workingTime δ v` equal to the fixed time `T`. -/
def hostedDeltaForTime (T : ℝ) (v : E) : ℝ :=
  2 * ‖v‖ / T

theorem workingTime_hostedDeltaForTime
    {T : ℝ} (hT : T ≠ 0) {v : E} (hv : v ≠ 0) :
    CartanHomogeneity.workingTime (hostedDeltaForTime T v) v = T := by
  have hnorm : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  unfold hostedDeltaForTime CartanHomogeneity.workingTime
  field_simp [hT, hnorm]

theorem workingVelocity_hostedDeltaForTime
    {T : ℝ} (hT : T ≠ 0) {v : E} (hv : v ≠ 0) :
    CartanHomogeneity.workingVelocity (hostedDeltaForTime T v) v = T⁻¹ • v := by
  have hnorm : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  unfold hostedDeltaForTime CartanHomogeneity.workingVelocity
  rw [show (2 * ‖v‖ / T) / 2 = ‖v‖ / T by ring]
  calc
    (‖v‖ / T) • (‖v‖⁻¹ • v) =
        ((‖v‖ / T) * ‖v‖⁻¹) • v := by
          simp [smul_smul]
    _ = T⁻¹ • v := by
          congr 1
          field_simp [hT, hnorm]

theorem hostedSourceTransverseScale_hostedDeltaForTime
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M)
    {T : ℝ} (hT : T ≠ 0) {v : E} (hv : v ≠ 0) :
    CartanScaleGeneric.hostedSourceTransverseScale g x₀
        (hostedDeltaForTime T v) v =
      CartanScaleGeneric.hostedTransverseScaleFromSpeed
        (Real.sqrt
          (CartanMap.sourceAnchorChartMetric g x₀
            (T⁻¹ • v) (T⁻¹ • v))) T := by
  rw [CartanScaleGeneric.hostedSourceTransverseScale,
    CartanScaleGeneric.hostedSourceSpeed,
    workingVelocity_hostedDeltaForTime (T := T) hT hv,
    workingTime_hostedDeltaForTime (T := T) hT hv]

theorem hostedTargetTransverseScale_hostedDeltaForTime
    {g : ClosedSmoothRiemannianMetric 3 M} {x₀ : M} {p₀ : RoundSphere3}
    (L : CartanMap.TangentAlignment g x₀ p₀)
    {T : ℝ} (hT : T ≠ 0) {v : E} (hv : v ≠ 0) :
    CartanScaleGeneric.hostedTargetTransverseScale L
        (hostedDeltaForTime T v) v =
      CartanScaleGeneric.hostedTransverseScaleFromSpeed
        (Real.sqrt
          (CartanMap.targetAnchorChartMetric p₀
            (L (T⁻¹ • v)) (L (T⁻¹ • v)))) T := by
  rw [CartanScaleGeneric.hostedTargetTransverseScale,
    CartanScaleGeneric.hostedTargetSpeed,
    workingVelocity_hostedDeltaForTime (T := T) hT hv,
    workingTime_hostedDeltaForTime (T := T) hT hv]

end CartanFinalComposition
end Poincare
