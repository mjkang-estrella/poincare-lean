import Poincare.Global.TwoBridges

/-!
# Target-ray identity bridge

This module isolates the final chart-to-manifold step for the old carried map:
once the old map satisfies target-chart exponential naturality at `x₁`, the
corresponding manifold target-ray identity follows by injectivity of the target
chart on its source.
-/

noncomputable section

open Set
open scoped Manifold ContDiff Topology

namespace Poincare
namespace TargetRayIdentity

universe u

local notation "E" => ClosedSmoothModel 3

variable {M : Type u}
variable [TopologicalSpace M]
variable [ChartedSpace E M]
variable [IsManifold (closedSmoothModelWithCorners 3) ∞ M]

/--
Target-chart exponential naturality for the old carried map gives the pointwise
manifold target-ray identity consumed by `TwoBridges`.
-/
theorem target_ray_identity_of_target_chart_exp_naturality
    {g : ClosedSmoothRiemannianMetric 3 M} (s : CartanChain.ChainState g)
    (x₁ : M) (L₁ : CartanMap.TangentAlignment g x₁ (s.map x₁))
    (hmapChart :
      ∀ x ∈ s.germ.source ∩
          (InducedAlignment.CompatibleStep.nextWithAlignment s x₁ L₁).germ.source,
        s.map x ∈ (chartAt E (s.map x₁)).source)
    (htargetChart :
      ∀ x ∈ s.germ.source ∩
          (InducedAlignment.CompatibleStep.nextWithAlignment s x₁ L₁).germ.source,
        GeodesicTransport.expAt roundSphereMetric3 (s.map x₁)
            (L₁
              ((GeodesicTransport.expAtChartOpenPartialHomeomorph
                (g := g) x₁).symm ((chartAt E x₁) x))) ∈
          (chartAt E (s.map x₁)).source)
    (hnaturality :
      ∀ x ∈ s.germ.source ∩
          (InducedAlignment.CompatibleStep.nextWithAlignment s x₁ L₁).germ.source,
        GeodesicTransport.expAtChartOpenPartialHomeomorph
            (g := roundSphereMetric3) (s.map x₁)
            (L₁
              ((GeodesicTransport.expAtChartOpenPartialHomeomorph
                (g := g) x₁).symm ((chartAt E x₁) x))) =
          (chartAt E (s.map x₁)) (s.map x)) :
    ∀ x ∈ s.germ.source ∩
        (InducedAlignment.CompatibleStep.nextWithAlignment s x₁ L₁).germ.source,
      s.map x =
        GeodesicTransport.expAt roundSphereMetric3 (s.map x₁)
          (L₁
            ((GeodesicTransport.expAtChartOpenPartialHomeomorph
              (g := g) x₁).symm ((chartAt E x₁) x))) := by
  intro x hx
  let v : E :=
    (GeodesicTransport.expAtChartOpenPartialHomeomorph
      (g := g) x₁).symm ((chartAt E x₁) x)
  have hchart_eq :
      (chartAt E (s.map x₁))
          (GeodesicTransport.expAt roundSphereMetric3 (s.map x₁) (L₁ v)) =
        (chartAt E (s.map x₁)) (s.map x) := by
    simpa [v, GeodesicTransport.expAtChartOpenPartialHomeomorph_coe] using
      hnaturality x hx
  have htarget_eq :
      GeodesicTransport.expAt roundSphereMetric3 (s.map x₁) (L₁ v) =
        s.map x :=
    (chartAt E (s.map x₁)).injOn (by simpa [v] using htargetChart x hx)
      (hmapChart x hx) hchart_eq
  simpa [v] using htarget_eq.symm

end TargetRayIdentity
end Poincare
