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

/-- Equality of endpoint germs gives equality of inverse normal germs.
Continuity pulls the velocity neighborhood back to the anchor, where both
partial inverse laws apply. -/
theorem normal_eventuallyEq_generic_in_anchor_frame_of_endpoint_agreement
    (x : M) (hx : x ∈ C.anchors)
    (h : (C.endpoint x : E → M) =ᶠ[𝓝 (0 : E)]
      (fun v => GeodesicTransport.expAt g x (anchorFrame x₀ x v))) :
    (fun z : M => anchorFrame x₀ x (C.normal x z)) =ᶠ[𝓝 x]
      (fun z : M => (CartanSourceExponential.genericFamily g).normal x z) := by
  have hn : Tendsto (C.normal x) (𝓝 x) (𝓝 (0 : E)) := by
    simpa only [C.normal_anchor x hx] using
      ((C.normal x).continuousAt (C.anchor_mem_normal_source x hx)).tendsto
  have hJ : Tendsto (anchorFrame x₀ x) (𝓝 (0 : E)) (𝓝 (0 : E)) := by
    simpa only [map_zero] using ((anchorFrame x₀ x).continuous.continuousAt (x := (0 : E))).tendsto
  have hinv := GeodesicTransport.expAtChartOpenPartialHomeomorph_eventually_left_inverse g x
  filter_upwards [hn h, (hJ.comp hn) hinv,
    (C.normal x).open_source.mem_nhds (C.anchor_mem_normal_source x hx)] with z hz hi hs
  have he : GeodesicTransport.expAt g x (anchorFrame x₀ x (C.normal x z)) = z :=
    hz.symm.trans ((C.normal x).left_inv hs)
  change (GeodesicTransport.expAtChartOpenPartialHomeomorph g x).symm
    (extChartAt I x (GeodesicTransport.expAt g x
      (anchorFrame x₀ x (C.normal x z)))) = anchorFrame x₀ x (C.normal x z) at hi
  rw [he] at hi
  exact hi.symm

end Poincare.FixedChartUniformPreferredGermAgreement
