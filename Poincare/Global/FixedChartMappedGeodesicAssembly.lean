import Poincare.Global.FixedChartAugmentedSystemRegularity
import Poincare.Global.FixedChartUniformEndpointReanchoring

/-!
# Regularity and geodesic assembly for the supplied fixed-chart map

The retained endpoint time and the order of all uniform radii are preserved.
-/

noncomputable section
set_option maxHeartbeats 1200000
set_option maxRecDepth 4000
open Filter Metric Set
open scoped Manifold ContDiff Topology NNReal
namespace Poincare
universe u
local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3
variable {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold I ∞ M]
variable {g : ClosedSmoothRiemannianMetric 3 M}
namespace FixedChartMappedGeodesicAssembly
open CartanSuppliedDifferentialSuccessor FixedChartUniformEndpointReanchoring

/-- The actual coordinate endpoint is C2 at every point of its retained source. -/
theorem coordinateEndpoint_contDiffAt_two {x₀ : M} {U : Set E}
    (C : FixedChartUniformSourceNormal.Patch g x₀ U)
    (x : M) (v : E) (hv : v ∈ (C.endpoint x).source) :
    ContDiffAt ℝ 2 ((C.endpoint x).trans (chartAt E x₀)) v := by
  have hq : (extChartAt I x₀ x, C.T⁻¹ • v) ∈
      ball (extChartAt I x₀ x₀, 0) (C.r : ℝ) := C.P_source_subset hv.1.2
  have h := ((FixedChartAugmentedSystemRegularity.patch_endpoint_contDiffOn_two C).contDiffAt (isOpen_ball.mem_nhds hq)).fst
  have hi : ContDiffAt ℝ 2 (fun w : E => (extChartAt I x₀ x, C.T⁻¹ • w)) v :=
    contDiffAt_const.prodMk ((contDiffAt_const (c := C.T⁻¹)).smul contDiffAt_id)
  apply (h.comp v hi).congr_of_eventuallyEq
  filter_upwards [(C.endpoint x).open_source.mem_nhds hv] with w hw
  exact FixedChartUniformDifferentialPullback.coordinateEndpoint_eq_normalizedEndpoint C x w hw

end FixedChartMappedGeodesicAssembly
end Poincare
