import Poincare.Global.RayCoverInputs

/-!
# Two bridge inputs for the ray-cover assembler

This module records the strict-partial bridge from the chart-coordinate inverse
identity to the manifold endpoint identity consumed by `RaysToBall`.  The
remaining old-map target-ray identity and target chart source membership stay
explicit: they are the non-vacuous inputs not exported by the current
re-anchoring API.
-/

noncomputable section

open Set
open scoped Manifold ContDiff Topology

namespace Poincare
namespace TwoBridges

universe u

local notation "E" => ClosedSmoothModel 3

variable {M : Type u}
variable [TopologicalSpace M]
variable [ChartedSpace E M]
variable [IsManifold (closedSmoothModelWithCorners 3) ∞ M]

/--
If the inverse `x₁` exponential coordinate has its endpoint inside the `x₁`
chart source, the chart-coordinate identity from `RayCoverInputs` promotes to
the manifold source-ray identity required by `RaysToBall`.  With the remaining
target-ray identity and target chart source membership supplied pointwise, the
strict common-source assembler proves the explicitly aligned rigid step.
-/
theorem rigidStepCompatibleWith_of_common_source_target_ray_and_chart_sources
    {g : ClosedSmoothRiemannianMetric 3 M} (s : CartanChain.ChainState g)
    (x₁ : M) (L₁ : CartanMap.TangentAlignment g x₁ (s.map x₁))
    (hsourceChart :
      ∀ x ∈ s.germ.source ∩
          (InducedAlignment.CompatibleStep.nextWithAlignment s x₁ L₁).germ.source,
        GeodesicTransport.expAt g x₁
            ((GeodesicTransport.expAtChartOpenPartialHomeomorph
              (g := g) x₁).symm ((chartAt E x₁) x)) ∈
          (chartAt E x₁).source)
    (htargetRay :
      ∀ x ∈ s.germ.source ∩
          (InducedAlignment.CompatibleStep.nextWithAlignment s x₁ L₁).germ.source,
        s.map x =
          GeodesicTransport.expAt roundSphereMetric3 (s.map x₁)
            (L₁
              ((GeodesicTransport.expAtChartOpenPartialHomeomorph
                (g := g) x₁).symm ((chartAt E x₁) x))))
    (htargetChart :
      ∀ x ∈ s.germ.source ∩
          (InducedAlignment.CompatibleStep.nextWithAlignment s x₁ L₁).germ.source,
        GeodesicTransport.expAt roundSphereMetric3 (s.map x₁)
            (L₁
              ((GeodesicTransport.expAtChartOpenPartialHomeomorph
                (g := g) x₁).symm ((chartAt E x₁) x))) ∈
          (chartAt E (s.map x₁)).source) :
    InducedAlignment.CompatibleStep.RigidStepCompatibleWith s x₁ L₁ := by
  refine
    RaysToBall.rigidStepCompatibleWith_of_common_source_expAt_ray_cover
      (s := s) (x₁ := x₁) (L₁ := L₁) ?_ ?_ htargetChart
  · intro x hx
    let eM := GeodesicTransport.expAtChartOpenPartialHomeomorph (g := g) x₁
    let v : E := eM.symm ((chartAt E x₁) x)
    have hcoords :=
      RayCoverInputs.common_source_expAt_inverse_and_reanchored_target_chart_coordinates
        (s := s) (x₁ := x₁) (L₁ := L₁) x hx
    have hxnext :
        x ∈ (CartanMap.openPartialHomeomorph g x₁ (s.map x₁) L₁).source := by
      simpa [InducedAlignment.CompatibleStep.nextWithAlignment,
        CartanChain.ChainState.germ] using hx.2
    have hxsource : x ∈ (chartAt E x₁).source := by
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
      exact hsource.1
    have hchart :
        (chartAt E x₁) (GeodesicTransport.expAt g x₁ v) =
          (chartAt E x₁) x := by
      simpa [eM, v, GeodesicTransport.expAtChartOpenPartialHomeomorph_coe] using
        hcoords.1
    exact (chartAt E x₁).injOn (by simpa [eM, v] using hsourceChart x hx)
      hxsource hchart
  · intro x hx _hsource
    exact htargetRay x hx

end TwoBridges
end Poincare
