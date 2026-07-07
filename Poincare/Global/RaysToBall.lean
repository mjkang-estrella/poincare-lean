import Poincare.Global.NaturalityCascade
import Poincare.Global.ExpNaturality

/-!
# Rays-to-ball assembly for Cartan re-centering

This module isolates the strict pointwise assembly step demanded after
`NaturalityCascade`: once every common-source point is represented by its
`x₁`-anchored exponential ray and the corresponding target ray endpoint is the
old Cartan value, the full common-source `EqOn` follows.
-/

noncomputable section

open Set
open scoped Manifold ContDiff Topology

namespace Poincare
namespace RaysToBall

universe u

local notation "E" => ClosedSmoothModel 3
local notation "I" => closedSmoothModelWithCorners 3

variable {M : Type u}
variable [TopologicalSpace M]
variable [ChartedSpace E M]
variable [IsManifold I ∞ M]

/--
Assemble `RigidStepCompatibleWith` from pointwise ray data on the strict common
source.

The hypotheses are the non-vacuous geometric boundary left after the
one-dimensional re-anchor law: `hsourceRay` says the inverse normal coordinate
at `x₁` really parametrizes the common-source point, `htargetRay` is the target
ray identity at that same parameter, and `htargetChart` lets the target chart
inverse read the endpoint as the re-centered Cartan map.
-/
theorem rigidStepCompatibleWith_of_common_source_expAt_ray_cover
    {g : ClosedSmoothRiemannianMetric 3 M} (s : CartanChain.ChainState g)
    (x₁ : M) (L₁ : CartanMap.TangentAlignment g x₁ (s.map x₁))
    (hsourceRay :
      ∀ x ∈ s.germ.source ∩
          (InducedAlignment.CompatibleStep.nextWithAlignment s x₁ L₁).germ.source,
        GeodesicTransport.expAt g x₁
            ((GeodesicTransport.expAtChartOpenPartialHomeomorph
              (g := g) x₁).symm ((chartAt E x₁) x)) =
          x)
    (htargetRay :
      ∀ x ∈ s.germ.source ∩
          (InducedAlignment.CompatibleStep.nextWithAlignment s x₁ L₁).germ.source,
        GeodesicTransport.expAt g x₁
            ((GeodesicTransport.expAtChartOpenPartialHomeomorph
              (g := g) x₁).symm ((chartAt E x₁) x)) =
          x →
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
  intro x hx
  change s.map x = CartanMap.cartanMap g x₁ (s.map x₁) L₁ x
  let v : E :=
    (GeodesicTransport.expAtChartOpenPartialHomeomorph
      (g := g) x₁).symm ((chartAt E x₁) x)
  have hsource : GeodesicTransport.expAt g x₁ v = x := by
    simpa [v] using hsourceRay x hx
  have htarget :
      s.map x =
        GeodesicTransport.expAt roundSphereMetric3 (s.map x₁) (L₁ v) := by
    simpa [v] using htargetRay x hx hsource
  have htarget_source :
      GeodesicTransport.expAt roundSphereMetric3 (s.map x₁) (L₁ v) ∈
        (chartAt E (s.map x₁)).source := by
    simpa [v] using htargetChart x hx
  have hnew :
      CartanMap.cartanMap g x₁ (s.map x₁) L₁ x =
        GeodesicTransport.expAt roundSphereMetric3 (s.map x₁) (L₁ v) := by
    calc
      CartanMap.cartanMap g x₁ (s.map x₁) L₁ x =
          (chartAt E (s.map x₁)).symm
            (GeodesicTransport.expAtChartOpenPartialHomeomorph
              (g := roundSphereMetric3) (s.map x₁) (L₁ v)) := rfl
      _ =
          (chartAt E (s.map x₁)).symm
            ((chartAt E (s.map x₁))
              (GeodesicTransport.expAt roundSphereMetric3 (s.map x₁) (L₁ v))) := by
        simp [GeodesicTransport.expAtChartOpenPartialHomeomorph_coe,
          closedSmoothModelWithCorners]
      _ = GeodesicTransport.expAt roundSphereMetric3 (s.map x₁) (L₁ v) :=
        (chartAt E (s.map x₁)).left_inv htarget_source
  exact htarget.trans hnew.symm

end RaysToBall
end Poincare
