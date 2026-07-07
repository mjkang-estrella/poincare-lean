import Poincare.Global.DecomposedAssembly

/-!
# Discharging exported decomposed-block side facts

This module collects the block-side instantiations that are already available
from the exported alignment and Gram-decomposition inventory.  It deliberately
does not restate the final local-isometry wrapper: the endpoint radial block
identities still require exported hosted endpoint formulas before
`cartanMap_isLocalIsometry_on_normalBall_of_common_speed_decomposed_blocks`
can be applied.
-/

noncomputable section

open Bundle Set Metric
open scoped Manifold ContDiff Topology RealInnerProductSpace NNReal

namespace Poincare
namespace BlocksDischarge

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

variable {M : Type*}
variable [TopologicalSpace M]
variable [ChartedSpace E M]
variable [IsManifold I ∞ M]

/-- A Cartan tangent alignment sends nonzero model vectors to nonzero vectors. -/
theorem tangentAlignment_apply_ne_zero
    {g : ClosedSmoothRiemannianMetric 3 M} {x₀ : M} {p₀ : RoundSphere3}
    (L : CartanMap.TangentAlignment g x₀ p₀) {v : E} (hv : v ≠ 0) :
    L v ≠ 0 := by
  intro hzero
  have hlin :
      L.toContinuousLinearEquiv v = L.toContinuousLinearEquiv 0 := by
    simpa [CartanMap.TangentAlignment.toContinuousLinearEquiv_apply] using hzero
  exact hv (L.toContinuousLinearEquiv.injective hlin)

/-- Source mixed radial/transverse block vanishes at the anchor. -/
theorem source_radialPart_transversePart_pair
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M)
    {v : E} (hv : v ≠ 0) (u u' : E) :
    CartanMap.sourceAnchorChartMetric g x₀
        (CartanPullback.radialPart (CartanMap.sourceAnchorChartMetric g x₀) v u)
        (CartanPullback.transversePart (CartanMap.sourceAnchorChartMetric g x₀) v u') =
      0 := by
  exact
    CartanPullback.radialPart_transversePart_pair
      (B := CartanMap.sourceAnchorChartMetric g x₀) (v := v) (u := u) (u' := u')
      (CartanMap.sourceAnchorChartMetric_symm g x₀)
      (CartanPullback.sourceAnchorChartMetric_self_ne_zero (g := g) (x₀ := x₀) hv)

/-- Source mixed transverse/radial block vanishes at the anchor. -/
theorem source_transversePart_radialPart_pair
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M)
    {v : E} (hv : v ≠ 0) (u u' : E) :
    CartanMap.sourceAnchorChartMetric g x₀
        (CartanPullback.transversePart (CartanMap.sourceAnchorChartMetric g x₀) v u)
        (CartanPullback.radialPart (CartanMap.sourceAnchorChartMetric g x₀) v u') =
      0 := by
  exact
    CartanPullback.transversePart_radialPart_pair
      (B := CartanMap.sourceAnchorChartMetric g x₀) (v := v) (u := u) (u' := u')
      (CartanPullback.sourceAnchorChartMetric_self_ne_zero (g := g) (x₀ := x₀) hv)

/-- Target mixed radial/transverse block vanishes at the anchor. -/
theorem target_radialPart_transversePart_pair
    (p₀ : RoundSphere3) {v : E} (hv : v ≠ 0) (u u' : E) :
    CartanMap.targetAnchorChartMetric p₀
        (CartanPullback.radialPart (CartanMap.targetAnchorChartMetric p₀) v u)
        (CartanPullback.transversePart (CartanMap.targetAnchorChartMetric p₀) v u') =
      0 := by
  exact
    CartanPullback.radialPart_transversePart_pair
      (B := CartanMap.targetAnchorChartMetric p₀) (v := v) (u := u) (u' := u')
      (CartanMap.targetAnchorChartMetric_symm p₀)
      (CartanPullback.targetAnchorChartMetric_self_ne_zero (p₀ := p₀) hv)

/-- Target mixed transverse/radial block vanishes at the anchor. -/
theorem target_transversePart_radialPart_pair
    (p₀ : RoundSphere3) {v : E} (hv : v ≠ 0) (u u' : E) :
    CartanMap.targetAnchorChartMetric p₀
        (CartanPullback.transversePart (CartanMap.targetAnchorChartMetric p₀) v u)
        (CartanPullback.radialPart (CartanMap.targetAnchorChartMetric p₀) v u') =
      0 := by
  exact
    CartanPullback.transversePart_radialPart_pair
      (B := CartanMap.targetAnchorChartMetric p₀) (v := v) (u := u) (u' := u')
      (CartanPullback.targetAnchorChartMetric_self_ne_zero (p₀ := p₀) hv)

end BlocksDischarge
end Poincare
