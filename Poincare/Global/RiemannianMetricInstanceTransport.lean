import Poincare.Global.RiemannianContext
/-!
# Preferred-chart dependence of metric coefficients

The identity of the model fibers is not the geometric identification of
 tangent bundles belonging to different preferred-chart selections. The
 coordinate formula below records the moving preferred chart explicitly.
 See `harness/reports/metric-transport_blocked.md` for the obstruction to
 transport preserving the raw `inner` values.
-/

noncomputable section

open Bundle Filter Set
open scoped Manifold ContDiff Topology
namespace Poincare.RiemannianMetricInstanceTransport
local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3
variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold I ∞ M]
set_option backward.isDefEq.respectTransparency false in
/-- A metric's coefficients in the chart at `a` use the derivative from that
chart to the preferred chart at the moving point `x`, in both arguments. -/
theorem inner_trivialization_apply
    (g : ClosedSmoothRiemannianMetric 3 M) {a x : M}
    (hx : x ∈ (chartAt E a).source) (v w : E) :
    (trivializationAt (E →L[ℝ] E →L[ℝ] ℝ)
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
      a ⟨x, g.inner x⟩).2 v w =
    g.inner x
      ((tangentBundleCore I M).coordChange (achart E a) (achart E x) x v)
      ((tangentBundleCore I M).coordChange (achart E a) (achart E x) x w) := by
  rw [hom_trivializationAt_apply]
  simp only [ContinuousLinearMap.inCoordinates, ContinuousLinearMap.comp_apply]
  rw [Trivialization.continuousLinearMapAt_apply_of_mem]
  · rw [hom_trivializationAt_apply]
    simp only [ContinuousLinearMap.inCoordinates, ContinuousLinearMap.comp_apply]
    rw [TangentBundle.symmL_trivializationAt_eq_core hx]
    simp
    rfl
  · simpa using hx
end Poincare.RiemannianMetricInstanceTransport
