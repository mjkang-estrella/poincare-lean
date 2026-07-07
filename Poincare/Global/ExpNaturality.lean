import Poincare.Global.InducedAlignment

/-!
# Exponential naturality consumer for Cartan re-centering

This module isolates the strict-partial consumer for the final classical
identity in the re-centering step.  Once the old Cartan germ is identified in
the `x₁` and `s.map x₁` exponential charts with the `x₁`-anchored Cartan germ,
the required compatible step follows by applying the target chart inverse.
-/

noncomputable section

open Set
open scoped Manifold ContDiff Topology

namespace Poincare
namespace ExpNaturality

universe u

local notation "E" => ClosedSmoothModel 3

variable {M : Type u}
variable [TopologicalSpace M]
variable [ChartedSpace E M]
variable [IsManifold (closedSmoothModelWithCorners 3) ∞ M]

/--
Normal-coordinate exponential naturality is enough to re-center a Cartan chain
state with an explicitly supplied tangent alignment.

The hypothesis `hnaturality` is the local identity
`Φ ∘ exp_{x₁} = exp_{Φ x₁} ∘ dΦ_{x₁}` written in the charted exponential
coordinates used by `CartanMap.openPartialHomeomorph`.  The source restriction
is the strict common source of the old and re-anchored germs; `hchart` records
that the old target values stay in the new target chart there.
-/
theorem rigidStepCompatibleWith_of_target_chart_exp_naturality
    {g : ClosedSmoothRiemannianMetric 3 M} (s : CartanChain.ChainState g)
    (x₁ : M) (L₁ : CartanMap.TangentAlignment g x₁ (s.map x₁))
    (hchart :
      ∀ x ∈ s.germ.source ∩
          (InducedAlignment.CompatibleStep.nextWithAlignment s x₁ L₁).germ.source,
        s.map x ∈ (chartAt E (s.map x₁)).source)
    (hnaturality :
      ∀ x ∈ s.germ.source ∩
          (InducedAlignment.CompatibleStep.nextWithAlignment s x₁ L₁).germ.source,
        GeodesicTransport.expAtChartOpenPartialHomeomorph
            (g := roundSphereMetric3) (s.map x₁)
            (L₁
              ((GeodesicTransport.expAtChartOpenPartialHomeomorph
                (g := g) x₁).symm ((chartAt E x₁) x))) =
          (chartAt E (s.map x₁)) (s.map x)) :
    InducedAlignment.CompatibleStep.RigidStepCompatibleWith s x₁ L₁ := by
  intro x hx
  change s.map x =
    CartanMap.cartanMap g x₁ (s.map x₁) L₁ x
  calc
    s.map x =
        (chartAt E (s.map x₁)).symm ((chartAt E (s.map x₁)) (s.map x)) := by
          exact ((chartAt E (s.map x₁)).left_inv (hchart x hx)).symm
    _ =
        (chartAt E (s.map x₁)).symm
          (GeodesicTransport.expAtChartOpenPartialHomeomorph
            (g := roundSphereMetric3) (s.map x₁)
            (L₁
              ((GeodesicTransport.expAtChartOpenPartialHomeomorph
                (g := g) x₁).symm ((chartAt E x₁) x)))) := by
          rw [← hnaturality x hx]
    _ = CartanMap.cartanMap g x₁ (s.map x₁) L₁ x := rfl

end ExpNaturality
end Poincare
