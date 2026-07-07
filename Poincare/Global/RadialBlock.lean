import Poincare.Global.DecomposedAssembly

/-!
# Radial block scalar boundary

This module records the non-vacuous algebraic boundary for the remaining
radial/radial block in the decomposed Cartan assembly.

The decomposed consumer currently asks the radial/radial block to use
`JacobiNormSystem.speedPinnedScale`, but that scalar is the sine-squared
transverse Jacobi scale.  A ray-shaped radial variation has the elementary
time-scaling recorded below.
-/

noncomputable section

open scoped Manifold ContDiff Topology RealInnerProductSpace NNReal

namespace Poincare
namespace RadialBlock

local notation "E" => ClosedSmoothModel 3

/-- The common-speed scalar in the decomposed consumer is the transverse sine scale. -/
theorem speedPinnedScale_unfold (speed T : ℝ) :
    JacobiNormSystem.speedPinnedScale speed T =
      Real.sin (speed * T) ^ 2 * (speed ^ 2)⁻¹ := by
  rfl

/-- At a half-period of the unit-speed transverse oscillator, the consumer scalar vanishes. -/
@[simp]
theorem speedPinnedScale_one_pi :
    JacobiNormSystem.speedPinnedScale 1 Real.pi = 0 := by
  simp [JacobiNormSystem.speedPinnedScale]

/-- Bilinear pairing of two ray-shaped endpoint variations. -/
theorem ray_pairing_time_smul
    (B : E →L[ℝ] E →L[ℝ] ℝ) (T : ℝ) (w w' : E) :
    B (T • w) (T • w') = T ^ 2 * B w w' := by
  simp [pow_two, mul_assoc]

/--
For the rescaled initial data used by the decomposed consumer, the explicit
ray variation has no sine factor: the endpoint pairing is the unscaled anchor
pairing.
-/
theorem ray_pairing_rescaled_initial
    (B : E →L[ℝ] E →L[ℝ] ℝ) {T : ℝ} (hT : T ≠ 0) (w w' : E) :
    B (T • (T⁻¹ • w)) (T • (T⁻¹ • w')) = B w w' := by
  simp [hT]

/--
The right-hand side requested by the decomposed radial/radial consumer rewrites
to the transverse scale multiplied by the inverse-time-squared anchor pairing.
-/
theorem consumer_speedPinned_rescaled_pairing
    (B : E →L[ℝ] E →L[ℝ] ℝ) (speed T : ℝ) (w w' : E) :
    JacobiNormSystem.speedPinnedScale speed T * B (T⁻¹ • w) (T⁻¹ • w') =
      (JacobiNormSystem.speedPinnedScale speed T * (T⁻¹ * T⁻¹)) * B w w' := by
  simp [mul_assoc, mul_left_comm, mul_comm]

end RadialBlock
end Poincare
