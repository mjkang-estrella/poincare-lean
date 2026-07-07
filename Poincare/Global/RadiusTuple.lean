import Poincare.Global.TransverseExport

/-!
# Selector-time radius tuple boundary

This module isolates the non-vacuous arithmetic condition hidden in the
selector-time bounded norm-system tuple.  The tuple fields consumed by
`TransverseExport` are not independent: the bounded-center constructor forces
the norm-system time to be short relative to the chosen coefficient operator.

The selector currently exports `T < εlin` for the linearized geodesic-flow
package, but it does not export the corresponding bound
`‖Aop‖ * T ≤ 1` (or a strict version sufficient to choose a positive radius)
for the scalar norm-system operator.  Without that, the radius tuple cannot be
constructed from the public selector data.
-/

noncomputable section

open Bundle Metric Set
open scoped Manifold ContDiff Topology RealInnerProductSpace NNReal

namespace Poincare
namespace RadiusTuple

universe u

local notation "E3" => ClosedSmoothModel 3
local notation "I3" => closedSmoothModelWithCorners 3
local notation "Triple" => ℝ × ℝ × ℝ

variable {M : Type u}
variable [TopologicalSpace M] [T2Space M]
variable [ChartedSpace E3 M]
variable [IsManifold I3 ∞ M]

open GeodesicTransport

/--
The bounded-center tuple side conditions force a short-time condition for the
norm-system coefficient.  This is the arithmetic obstruction left by the
selector export: evaluating the center bound at `w = 0` gives
`radius ≤ B`, hence `hbound` and `hmulT` imply `‖Aop‖ * T ≤ 1` for any
positive radius.
-/
theorem norm_time_le_one_of_radius_tuple_bounds
    {T : ℝ} (hTnonneg : 0 ≤ T)
    (Aop : Triple →L[ℝ] Triple)
    {radius rNorm LNorm B : ℝ≥0}
    (hradius_pos : 0 < (radius : ℝ))
    (hcenter0 : (radius : ℝ) ≤ (B : ℝ))
    (hbound : ‖Aop‖ * (B : ℝ) ≤ (LNorm : ℝ))
    (hmulT : (LNorm : ℝ) * T ≤ (radius : ℝ) - (rNorm : ℝ)) :
    ‖Aop‖ * T ≤ 1 := by
  have hnorm_nonneg : 0 ≤ ‖Aop‖ := norm_nonneg Aop
  have hB_nonneg : 0 ≤ (B : ℝ) := NNReal.coe_nonneg B
  have hL_nonneg : 0 ≤ (LNorm : ℝ) := NNReal.coe_nonneg LNorm
  have hr_nonneg : 0 ≤ (rNorm : ℝ) := NNReal.coe_nonneg rNorm
  have hstep1 : ‖Aop‖ * (radius : ℝ) ≤ ‖Aop‖ * (B : ℝ) := by
    exact mul_le_mul_of_nonneg_left hcenter0 hnorm_nonneg
  have hstep2 : ‖Aop‖ * (radius : ℝ) * T ≤ (LNorm : ℝ) * T := by
    exact mul_le_mul_of_nonneg_right (hstep1.trans hbound) hTnonneg
  have hstep3 : ‖Aop‖ * (radius : ℝ) * T ≤ (radius : ℝ) := by
    calc
      ‖Aop‖ * (radius : ℝ) * T ≤ (LNorm : ℝ) * T := hstep2
      _ ≤ (radius : ℝ) - (rNorm : ℝ) := hmulT
      _ ≤ (radius : ℝ) := by linarith
  have hmul_comm : ‖Aop‖ * (radius : ℝ) * T = (radius : ℝ) * (‖Aop‖ * T) := by
    ring
  have hstep3' : (radius : ℝ) * (‖Aop‖ * T) ≤ (radius : ℝ) * 1 := by
    simpa [hmul_comm] using hstep3
  nlinarith

omit [T2Space M] in
/--
Source-side specialization of
`norm_time_le_one_of_radius_tuple_bounds`: the actual selector center bound,
if available, already implies `radius ≤ B` at the zero endpoint direction.
-/
theorem source_norm_time_le_one_of_selector_radius_tuple
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M)
    {T : ℝ} (hTnonneg : 0 ≤ T)
    (Aop : Triple →L[ℝ] Triple)
    {R radius rNorm LNorm _KNorm B : ℝ≥0}
    (hradius_pos : 0 < (radius : ℝ))
    (hcenter : ∀ w : E3, w ∈ closedBall (0 : E3) (R : ℝ) →
      ‖(((0 : ℝ), (0 : ℝ),
        chartGeodesicMetric g x₀ (extChartAt I3 x₀ x₀)
          (T⁻¹ • w) (T⁻¹ • w)) : Triple)‖ + (radius : ℝ) ≤ (B : ℝ))
    (hbound : ‖Aop‖ * (B : ℝ) ≤ (LNorm : ℝ))
    (hmulT : (LNorm : ℝ) * T ≤ (radius : ℝ) - (rNorm : ℝ)) :
    ‖Aop‖ * T ≤ 1 := by
  have hzero_mem : (0 : E3) ∈ closedBall (0 : E3) (R : ℝ) := by
    exact mem_closedBall_self (NNReal.coe_nonneg R)
  have hcenter0 := hcenter (0 : E3) hzero_mem
  have hcenter0' : (radius : ℝ) ≤ (B : ℝ) := by
    simpa using hcenter0
  exact
    norm_time_le_one_of_radius_tuple_bounds
      hTnonneg Aop hradius_pos hcenter0' hbound hmulT

omit [TopologicalSpace M] [T2Space M] [ChartedSpace E3 M] [IsManifold I3 ∞ M] in
/--
Target-side specialization of the same necessary condition.
-/
theorem target_norm_time_le_one_of_selector_radius_tuple
    (p₀ : RoundSphere3)
    {T : ℝ} (hTnonneg : 0 ≤ T)
    (Aop : Triple →L[ℝ] Triple)
    {R radius rNorm LNorm _KNorm B : ℝ≥0}
    (hradius_pos : 0 < (radius : ℝ))
    (hcenter : ∀ w : E3, w ∈ closedBall (0 : E3) (R : ℝ) →
      ‖(((0 : ℝ), (0 : ℝ),
        chartGeodesicMetric roundSphereMetric3 p₀ (extChartAt I3 p₀ p₀)
          (T⁻¹ • w) (T⁻¹ • w)) : Triple)‖ + (radius : ℝ) ≤ (B : ℝ))
    (hbound : ‖Aop‖ * (B : ℝ) ≤ (LNorm : ℝ))
    (hmulT : (LNorm : ℝ) * T ≤ (radius : ℝ) - (rNorm : ℝ)) :
    ‖Aop‖ * T ≤ 1 := by
  have hzero_mem : (0 : E3) ∈ closedBall (0 : E3) (R : ℝ) := by
    exact mem_closedBall_self (NNReal.coe_nonneg R)
  have hcenter0 := hcenter (0 : E3) hzero_mem
  have hcenter0' : (radius : ℝ) ≤ (B : ℝ) := by
    simpa using hcenter0
  exact
    norm_time_le_one_of_radius_tuple_bounds
      hTnonneg Aop hradius_pos hcenter0' hbound hmulT

end RadiusTuple
end Poincare
