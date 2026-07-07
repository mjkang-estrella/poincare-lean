import Poincare.Global.RaysToBall
import Poincare.Global.GeodesicPreservation

/-!
# Ray-cover chart-coordinate inputs on the strict common source

This module records the non-hypothetical chart-coordinate facts available at
strict common-source points for the Cartan re-centering step.  The source
identity is the inverse identity of the `x₁` exponential partial
homeomorphism, and the target identity is the anchor-based exponential
naturality of the re-centered Cartan germ.
-/

noncomputable section

open Set
open scoped Manifold ContDiff Topology

namespace Poincare
namespace RayCoverInputs

universe u

local notation "E" => ClosedSmoothModel 3

variable {M : Type u}
variable [TopologicalSpace M]
variable [ChartedSpace E M]
variable [IsManifold (closedSmoothModelWithCorners 3) ∞ M]

/--
At a strict common-source point, the `x₁` exponential coordinate obtained from
the partial-homeomorphism inverse maps back to the source chart coordinate, and
the re-centered Cartan germ has the expected target exponential chart
coordinate.
-/
theorem common_source_expAt_inverse_and_reanchored_target_chart_coordinates
    {g : ClosedSmoothRiemannianMetric 3 M} (s : CartanChain.ChainState g)
    (x₁ : M) (L₁ : CartanMap.TangentAlignment g x₁ (s.map x₁)) :
    ∀ x ∈ s.germ.source ∩
        (InducedAlignment.CompatibleStep.nextWithAlignment s x₁ L₁).germ.source,
      GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₁
          ((GeodesicTransport.expAtChartOpenPartialHomeomorph
            (g := g) x₁).symm ((chartAt E x₁) x)) =
        (chartAt E x₁) x ∧
      GeodesicTransport.expAtChartOpenPartialHomeomorph
          (g := roundSphereMetric3) (s.map x₁)
          (L₁
            ((GeodesicTransport.expAtChartOpenPartialHomeomorph
              (g := g) x₁).symm ((chartAt E x₁) x))) =
        (chartAt E (s.map x₁))
          (CartanMap.cartanMap g x₁ (s.map x₁) L₁ x) := by
  intro x hx
  let eM := GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₁
  have hxnext :
      x ∈ (CartanMap.openPartialHomeomorph g x₁ (s.map x₁) L₁).source := by
    simpa [InducedAlignment.CompatibleStep.nextWithAlignment,
      CartanChain.ChainState.germ] using hx.2
  have hsource :
      x ∈ (chartAt E x₁).source ∧
        (chartAt E x₁) x ∈ eM.target ∧
          eM.symm ((chartAt E x₁) x) ∈
              (CartanMap.tangentAlignmentOpenPartialHomeomorph L₁).source ∧
            L₁ (eM.symm ((chartAt E x₁) x)) ∈
                (GeodesicTransport.expAtChartOpenPartialHomeomorph
                  (g := roundSphereMetric3) (s.map x₁)).source ∧
              (chartAt E (s.map x₁))
                  (GeodesicTransport.expAt roundSphereMetric3 (s.map x₁)
                    (L₁ (eM.symm ((chartAt E x₁) x)))) ∈
                (chartAt E (s.map x₁)).target := by
    simpa [eM, CartanMap.openPartialHomeomorph] using hxnext
  constructor
  · simpa [eM] using eM.right_inv hsource.2.1
  · simpa [eM] using
      GeodesicPreservation.cartanMap_target_chart_exp_naturality
        (g := g) (x₀ := x₁) (p₀ := s.map x₁) L₁ (x := x) hxnext

end RayCoverInputs
end Poincare
