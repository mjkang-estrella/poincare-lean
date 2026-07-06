import Poincare.Global.AntilipschitzBallFinal

/-!
# Closing local anti-Lipschitz chart-ball estimates

This file is the intended final assembly point for the local anti-Lipschitz
chart-ball cluster.  It proves small, non-geometric helper facts that are used
by the path dichotomy and records the precise remaining formal boundary if the
full first-exit assembly cannot be discharged in this worker.
-/

noncomputable section

open Bundle Set MeasureTheory
open scoped Manifold ContDiff Topology ENNReal NNReal RealInnerProductSpace

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
attribute [local instance] normedSpaceTangentSpaceVectorSpace

namespace Poincare
namespace GeodesicTransport

universe u

variable {n : ℕ} {M : Type u}
variable [TopologicalSpace M] [T2Space M] [CompactSpace M] [ConnectedSpace M]
variable [MeasurableSpace M] [BorelSpace M]
variable [ChartedSpace (ClosedSmoothModel n) M]
variable [IsManifold (closedSmoothModelWithCorners n) ∞ M]

local notation "I" => closedSmoothModelWithCorners n
local notation "E" => ClosedSmoothModel n

omit [T2Space M] [CompactSpace M] [ConnectedSpace M]
  [MeasurableSpace M] [BorelSpace M] in
theorem dist_le_two_mul_radius_of_mem_ball
    {z u v : E} {r : ℝ} (hu : u ∈ Metric.ball z r) (hv : v ∈ Metric.ball z r) :
    dist u v ≤ 2 * r := by
  calc
    dist u v ≤ dist u z + dist v z := by
      simpa [dist_comm] using dist_triangle u z v
    _ ≤ r + r := add_le_add hu.le hv.le
    _ = 2 * r := by ring

omit [T2Space M] [CompactSpace M] [ConnectedSpace M]
  [MeasurableSpace M] [BorelSpace M] in
theorem ofReal_inv_mul_dist_le_of_dist_le_two_mul_radius
    {K : ℝ≥0} (hK : 0 < K) {r : ℝ} {u v : E}
    (hdist : dist u v ≤ 2 * r) :
    ENNReal.ofReal (((K : ℝ)⁻¹) * dist u v) ≤
      ENNReal.ofReal (((K : ℝ)⁻¹) * (2 * r)) := by
  have hKℝ : 0 ≤ ((K : ℝ)⁻¹) := inv_nonneg.mpr (by positivity)
  exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hdist hKℝ)

end GeodesicTransport
end Poincare
