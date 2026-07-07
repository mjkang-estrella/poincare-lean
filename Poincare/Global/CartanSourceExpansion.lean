import Poincare.Global.CartanExpansionBridge

/-!
# Source-side Cartan endpoint expansion boundary

This module records the current obstruction to the requested source-side
weighted endpoint expansion.  As written, the expansion cannot be unconditional
on the whole normal-ball parameter space: at the zero normal vector, the
existing `transverseScale` is `0 / 0`, hence `0` in Lean, so the source-scaled
normal vector collapses to zero.
-/

noncomputable section

open Bundle
open scoped Manifold ContDiff Topology RealInnerProductSpace

namespace Poincare
namespace CartanSourceExpansion

universe u

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M]
variable [ChartedSpace E M]
variable [IsManifold I ∞ M]

@[simp]
theorem sourceScaledNormalVector_zero
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M) (u : E) :
    CartanLocalIsometry.sourceScaledNormalVector g x₀
        1 (CartanLocalIsometry.transverseScale (0 : E)) (0 : E) u = 0 := by
  simp [CartanLocalIsometry.sourceScaledNormalVector,
    CartanLocalIsometry.transverseScale, CartanPullback.radialPart,
    CartanPullback.transversePart, CartanPullback.radialCoeff]

/--
The current weighted source endpoint expansion statement cannot hold at the
zero normal vector.  This blocks an unconditional theorem producing that exact
remaining hypothesis without first changing the expansion domain or the zero
case normalization.
-/
theorem not_weightedSourceEndpointExpansion_zero
    (g : ClosedSmoothRiemannianMetric 3 M) (x₀ : M) (κ : ℝ) :
    ¬ CartanLocalIsometry.WeightedSourceEndpointExpansion g x₀ (0 : E) κ := by
  intro h
  obtain ⟨u, hu⟩ := exists_ne (0 : E)
  have hmetric := h.metric u u
  have hzero :
      CovariantDerivative.chartMetric g.inner x₀
          ((GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀) (0 : E))
          u u = 0 := by
    simpa using hmetric
  have hpos :
      0 <
        CovariantDerivative.chartMetric g.inner x₀
          ((GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₀) (0 : E))
          u u := by
    simpa [CartanMap.sourceAnchorChartMetric,
      CartanMap.expAtChartOpenPartialHomeomorph_zero_eq_chart_anchor] using
      CartanMap.sourceAnchorChartMetric_pos g x₀ hu
  exact (ne_of_gt hpos) hzero

end CartanSourceExpansion
end Poincare
