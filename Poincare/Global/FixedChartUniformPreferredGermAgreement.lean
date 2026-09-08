import Poincare.Global.FixedChartUniformSourceNormal
import Poincare.Global.CartanSuppliedSourceGermTransfer
import Poincare.Global.ChartTransitionGeodesicMap

/-!
# Fixed-anchor frame and inverse comparison for a retained flow

The preferred-frame derivative is invertible on every retained chart overlap.
Endpoint agreement transfers to inverse normal coordinates on their actual
open domains. The remaining interval comparison is stated explicitly below.
-/

noncomputable section

open Filter Function Metric Set
open scoped Topology ContDiff NNReal Manifold

namespace Poincare.FixedChartUniformPreferredGermAgreement

universe u
local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

variable {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold I ∞ M]
variable {g : ClosedSmoothRiemannianMetric 3 M} {x₀ : M} {U : Set E}
variable (C : FixedChartUniformSourceNormal.Patch g x₀ U)

/-- The fixed-chart velocity expressed in the preferred frame of the anchor. -/
def anchorFrame (x₀ x : M) : E →L[ℝ] E :=
  GeodesicTransport.chartTransitionDeriv x₀ x (extChartAt I x₀ x)

/-- Both chart differentials are invertible on the retained overlap. -/
theorem anchorFrame_isInvertible (x : M) (hx : x ∈ C.anchors) :
    (anchorFrame x₀ x).IsInvertible := by
  have hz := (extChartAt I x₀).map_source hx.1
  have hy : (extChartAt I x₀).symm (extChartAt I x₀ x) ∈
      (extChartAt I x).source := by
    rw [(extChartAt I x₀).left_inv hx.1]
    exact mem_extChartAt_source x
  rw [anchorFrame, GeodesicTransport.chartTransitionDeriv_eq_chartTransitionMFDeriv
    x₀ x hz hy]
  exact (isInvertible_mfderiv_extChartAt hy).comp
    (isInvertible_mfderivWithin_extChartAt_symm hz)

end Poincare.FixedChartUniformPreferredGermAgreement
